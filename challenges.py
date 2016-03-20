#!/usr/bin/env python3

import argparse
import base64
import cProfile
import os
import pprint
import re
import struct
import sys
import warnings

from collections import Counter, defaultdict, deque
from contextlib import ExitStack, redirect_stderr, redirect_stdout
from functools import lru_cache
from heapq import nlargest
from http.server import BaseHTTPRequestHandler, HTTPServer
from itertools import count, cycle
from multiprocessing.dummy import Pool as ThreadPool
from random import SystemRandom
from socketserver import ForkingMixIn, ThreadingMixIn
from statistics import median
from threading import Thread
from time import perf_counter, sleep, time
from urllib.error import HTTPError
from urllib.parse import parse_qs, quote as url_quote, urlencode, urlparse
from urllib.request import urlopen

from Crypto.Cipher import AES
from md4.md4 import MD4
from sha1.sha1 import Sha1Hash

try:
    # Python 3.5
    from math import gcd
except ImportError:
    # older Python versions
    from fractions import gcd

warnings.simplefilter("default", BytesWarning)
warnings.simplefilter("default", ResourceWarning)
warnings.simplefilter("default", DeprecationWarning)

random = SystemRandom()

EXAMPLE_PLAIN_BYTES = (b"Give a man a beer, he'll waste an hour. "
    b"Teach a man to brew, he'll waste a lifetime.")


NIST_DIFFIE_HELLMAN_PRIME = int("ffffffffffffffffc90fdaa22168c234c4c6628b80dc1c"
    "d129024e088a67cc74020bbea63b139b22514a08798e3404ddef9519b3cd3a431b302b0a6d"
    "f25f14374fe1356d6d51c245e485b576625e7ec6f44c42e9a637ed6b0bff5cb6f406b7edee"
    "386bfb5a899fa5ae9f24117c4b1fe649286651ece45b3dc2007cb8a163bf0598da48361c55"
    "d39a69163fa8fd24cf5f83655d23dca3ad961c62f356208552bb9ed529077096966d670c35"
    "4e4abc9804f1746c08ca237327ffffffffffffffff", 16)


def pp(*args, width=120, **kwargs):
    pprint.pprint(*args, width=width, **kwargs)


def bytes_to_string(b):
    return b.decode("utf-8", errors="replace")


def xor_bytes(*bytes_objects):
    lengths = [len(b) for b in bytes_objects]
    if len(set(lengths)) > 1:
        raise ValueError("inputs must be of equal length")
    result = bytearray([0]) * lengths[0]
    for b in bytes_objects:
        for i, byte in enumerate(b):
            result[i] ^= byte
    return bytes(result)


def xor_encrypt(input_bytes, key):
    return bytes(a ^ b for a, b in zip(input_bytes, cycle(key)))


def byte_chunks(input_bytes, chunk_size=16):
    return [input_bytes[i : i + chunk_size]
        for i in range(0, len(input_bytes), chunk_size)]


# Character frequencies were taken from raw letter averages at
# http://www.macfreek.nl/memory/Letter_Distribution, then rounded to 6
# decimal places for readability. Numbers for control characters (\x00
# through \x1f excluding tab (\x09), newline (\x0a), and carriage return
# (\x0d)) were added by me after observing better results. Text should
# be converted to lowercase before one attempts to analyze it using this
# dictionary.
english_byte_frequencies = defaultdict(
    # The following number will be returned for any byte not explicitly
    # represented. 4e-6 was observed to produce the best ratio of score for
    # English text to score for incorrectly decrypted text.
    lambda: 4e-6,
    {ord(char): freq for char, freq in {
        "\x00": 1e-6, "\x01": 1e-6, "\x02": 1e-6, "\x03": 1e-6, "\x04": 1e-6,
        "\x05": 1e-6, "\x06": 1e-6, "\x07": 1e-6, "\x08": 1e-6, "\x0b": 1e-6,
        "\x0c": 1e-6, "\x0e": 1e-6, "\x0f": 1e-6, "\x10": 1e-6, "\x11": 1e-6,
        "\x12": 1e-6, "\x13": 1e-6, "\x14": 1e-6, "\x15": 1e-6, "\x16": 1e-6,
        "\x17": 1e-6, "\x18": 1e-6, "\x19": 1e-6, "\x1a": 1e-6, "\x1b": 1e-6,
        "\x1c": 1e-6, "\x1d": 1e-6, "\x1e": 1e-6, "\x1f": 1e-6,
        " ": 0.183169, "a": 0.065531, "b": 0.012708, "c": 0.022651, "d": 0.033523,
        "e": 0.102179, "f": 0.019718, "g": 0.016359, "h": 0.048622, "i": 0.057343,
        "j": 0.001144, "k": 0.005692, "l": 0.033562, "m": 0.020173, "n": 0.057031,
        "o": 0.062006, "p": 0.015031, "q": 0.000881, "r": 0.049720, "s": 0.053263,
        "t": 0.075100, "u": 0.022952, "v": 0.007880, "w": 0.016896, "x": 0.001498,
        "y": 0.014700, "z": 0.000598
    }.items()})


def english_like_score(text_bytes):
    # english_byte_frequencies is defined outside of this function as a
    # performance optimization. In my tests, the time spent in this function
    # is less than half of what it would be if english_byte_frequencies were
    # defined inside this function. I am also using a defaultdict instead of
    # a Counter for the byte counts as a performance optimization.
    byte_counts = defaultdict(int)
    for byte in text_bytes.lower():
        byte_counts[byte] += 1
    text_length = len(text_bytes)
    chi_squared = 0
    for byte, byte_count in byte_counts.items():
        expected = text_length * english_byte_frequencies[byte]
        difference = byte_count - expected
        chi_squared += difference * difference / expected
    return 1e6 / chi_squared / text_length


def english_like_score_data(ciphertext):
    result = []
    for i in range(256):
        message = xor_encrypt(ciphertext, bytes([i]))
        score = english_like_score(message)
        result.append({"key": i, "message": message, "score": score})
    return result


def best_english_like_score_data(ciphertext):
    return max(english_like_score_data(ciphertext), key=lambda x: x["score"])


def looks_like_ecb(ciphertext, block_size=16):
    # TODO: use birthday paradox to calculate an estimate for the expected
    # number of duplicate blocks so this function works on big ciphertexts.
    block_counter = Counter(byte_chunks(ciphertext, block_size))
    return block_counter.most_common(1)[0][1] > 1


def crack_common_xor_key(ciphertexts):
    key = bytearray()
    for i in count(start=0):
        transposed_block = bytes(c[i] for c in ciphertexts if i < len(c))
        if transposed_block:
            score_data = best_english_like_score_data(transposed_block)
            key.append(score_data["key"])
        else:
            plaintexts = [xor_encrypt(c, key) for c in ciphertexts]
            return (plaintexts, key)


def pkcs7_pad(input_bytes, block_size=16):
    padding_length = -len(input_bytes) % block_size
    if padding_length == 0:
        padding_length = block_size
    return input_bytes + bytes([padding_length] * padding_length)


def pkcs7_unpad(ciphertext, block_size=16):
    padding_length = ciphertext[-1]
    expected_padding = bytes([padding_length]) * padding_length
    padding = ciphertext[-padding_length:]
    if padding_length > block_size or padding != expected_padding:
        raise ValueError("Invalid padding")
    return ciphertext[:-padding_length]


def cbc_encrypt(key, iv, plain_bytes):
    cipher = AES.new(key, AES.MODE_ECB, iv)
    last_cipher_block = iv
    result = bytearray()
    for plain_block in byte_chunks(plain_bytes):
        combined_block = xor_bytes(last_cipher_block, plain_block)
        cipher_block = cipher.encrypt(combined_block)
        result.extend(cipher_block)
        last_cipher_block = cipher_block
    return bytes(result)


def cbc_decrypt(key, iv, ciphertext):
    cipher = AES.new(key, AES.MODE_ECB, iv)
    last_cipher_block = iv
    result = bytearray()
    for cipher_block in byte_chunks(ciphertext):
        decrypted_block = cipher.decrypt(cipher_block)
        plain_block = xor_bytes(last_cipher_block, decrypted_block)
        result.extend(plain_block)
        last_cipher_block = cipher_block
    return bytes(result)


def create_random_aes_key():
    return os.urandom(16)


def appears_to_produce_ecb(oracle_fn, block_size=16):
    return any(looks_like_ecb(oracle_fn(b"A" * i), block_size) for i in range(1000))


def guess_block_size(oracle_fn):
    seen_sizes = set()
    for plaintext_size in range(33):
        ciphertext = oracle_fn(os.urandom(plaintext_size))
        seen_sizes.add(len(ciphertext))
    if len(seen_sizes) >= 2:
        result = 0
        for size in seen_sizes:
            result = gcd(result, size)
        return result
    else:
        raise ValueError("Could not guess block size")


def crack_ecb_oracle(oracle_fn, prefix_length=0, block_size=16):
    assert appears_to_produce_ecb(oracle_fn)

    result = bytearray()
    while True:
        short_block_length = (block_size - len(result) - 1 - prefix_length) % block_size
        short_input_block = b"A" * short_block_length
        short_block_output = oracle_fn(short_input_block)
        block_index = (len(result) + prefix_length) // block_size
        block_to_look_for = byte_chunks(short_block_output)[block_index]
        for i in range(256):
            test_input = short_input_block + result + bytes([i])
            output = oracle_fn(test_input)
            telltale_block = byte_chunks(output)[block_index]
            if telltale_block == block_to_look_for:
                result.append(i)
                break
        else:  # if no byte matches
            return pkcs7_unpad(result)


def create_encrypted_query_string(cipher, user_data):
    query_string = ("comment1=cooking%20MCs;userdata=" + url_quote(user_data) +
        ";comment2=%20like%20a%20pound%20of%20bacon")
    bytes_to_encrypt = pkcs7_pad(query_string.encode("utf-8"))
    return cipher.encrypt(bytes_to_encrypt)


def encrypted_string_has_admin(ciphertext, cipher):
    plain_bytes = pkcs7_unpad(cipher.decrypt(ciphertext))
    return b";admin=true;" in plain_bytes


def create_ctr_counter(nonce, block_index=0):
    # This is roughly equivalent to the following code:
    # return Crypto.Util.Counter.new(
    #     nbits=64, prefix=struct.pack("<Q", nonce), initial_value=block_index,
    #     little_endian=True)
    # I prefer to use my own implementation because it is simpler, more
    # readable, and good enough for my purposes. The nonce and the counter
    # are encoded as 64-bit little-endian integers. I am returning the
    # iterator's __next__ method instead of the iterator itself because
    # PyCrypto's CTR implementation requires a function that returns a new
    # value each time it is called.
    return (struct.pack("<QQ", nonce, i) for i in count(start=block_index)).__next__


class MT19937_RNG:
    """Mersenne Twister random number generator"""

    def __init__(self, seed):
        self.index = 624
        buffer = self.buffer = [seed] + [0]*623
        prev = seed
        for i in range(1, 624):
            prev = buffer[i] = 0xffffffff & (1812433253 * (prev ^ (prev >> 30)) + i)

    def get_number(self):
        if self.index >= 624:
            self.twist()
        result = self.temper(self.buffer[self.index])
        self.index += 1
        return result

    def twist(self):
        buffer = self.buffer
        for i in range(624):
            y = ((buffer[i] & 0x80000000) +
                       (buffer[(i + 1) % 624] & 0x7fffffff))
            buffer[i] = buffer[(i + 397) % 624] ^ (y >> 1)

            if y & 1:
                buffer[i] ^= 0x9908b0df
        self.index = 0

    @staticmethod
    def temper(x):
        x ^= (x >> 11)
        x ^= (x << 7) & 0x9d2c5680
        x ^= (x << 15) & 0xefc60000
        x ^= (x >> 18)
        return x

    @staticmethod
    def untemper(x):
        x ^= (x >> 18)

        x ^= (x << 15) & 0xefc60000

        x ^= (x << 7) & 0x9d2c5680
        x ^= (x << 14) & 0x94284000
        x ^= (x << 28) & 0x10000000

        x ^= (x >> 11)
        x ^= (x >> 22)
        return x


def sha1(message):
    return Sha1Hash().update(message).digest()


def calculate_hmac(key, message):
    key_hash = sha1(key)
    o_key_pad = xor_encrypt(key_hash, b"\x5c")
    i_key_pad = xor_encrypt(key_hash, b"\x36")
    return sha1(o_key_pad + sha1(i_key_pad + message))


get_hmac = lru_cache()(calculate_hmac)


def insecure_compare(data1, data2, delay):
    if len(data1) != len(data2):
        return False
    for byte1, byte2 in zip(data1, data2):
        if byte1 != byte2:
            return False
        sleep(delay)
    return True


class ValidatingRequestHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        url_components = urlparse(self.path)
        if url_components.path == "/signature_is_valid":
            query_vars = parse_qs(url_components.query)
            try:
                filename = query_vars["file"][0]
                with open(filename, "rb") as file:
                    data = file.read()
                signature = bytes.fromhex(query_vars["signature"][0])
            except (KeyError, ValueError, FileNotFoundError):
                self.send_error(400)
            else:
                hmac = get_hmac(self.server.hmac_key, data)
                if self.server.validate_signature(hmac, signature):
                    self.send_response(200)
                    self.end_headers()
                    self.wfile.write(b"Signature matches.")
                else:
                    self.send_error(500)
        else:
            self.send_error(404)


def recover_signature(validate_signature, quiet=True, thread_count=300):
    # TODO: make this more efficient, reliable, and flexible

    def try_signature(signature):
        start_time = perf_counter()
        is_valid = validate_signature(signature)
        duration = perf_counter() - start_time
        return {"signature": signature, "is_valid": is_valid, "duration": duration}

    difference_expectations = deque(maxlen=20)
    result = bytearray()
    with ThreadPool(thread_count) as pool:
        for pos in range(20):
            assert pos == len(result)
            sig_durations = {}
            for b in range(256):
                sig = bytes(result + bytes([b] + [0]*(19 - pos)))
                sig_durations[sig] = []
            for i in range(20):
                for sig_data in pool.imap_unordered(try_signature, sig_durations.keys()):
                    if sig_data["is_valid"]:
                        if not quiet:
                            print("signature recovered: {}, {} attempts".format(
                                list(result), i + 1))
                        return sig_data["signature"]
                    sig_durations[sig_data["signature"]].append(sig_data["duration"])
                slowest_sig, second_slowest_sig = nlargest(
                    2, sig_durations, key=lambda x: median(sig_durations[x]))
                slowest_duration = median(sig_durations[slowest_sig])
                second_slowest_duration = median(sig_durations[second_slowest_sig])
                duration_difference = slowest_duration - second_slowest_duration
                difference_expectations.append(duration_difference)
                if duration_difference > median(difference_expectations):
                    result.append(slowest_sig[pos])
                    if not quiet:
                        print("recovered so far: {}, {} attempts".format(
                            list(result), i + 1))
                    break
            else:
                raise ValueError("can't recover signature")
    raise ValueError("can't recover signature")


def challenge1():
    """Convert hex to base64"""
    encoded_text = ("49276d206b696c6c696e6720796f757220627261696e206c" +
        "696b65206120706f69736f6e6f7573206d757368726f6f6d")
    message = bytes.fromhex(encoded_text)
    print(bytes_to_string(message))
    result = base64.b64encode(message)
    assert result == b"SSdtIGtpbGxpbmcgeW91ciBicmFpbiBsaWtlIGEgcG9pc29ub3VzIG11c2hyb29t"


def challenge2():
    """Fixed XOR"""
    output = xor_bytes(
        bytes.fromhex("1c0111001f010100061a024b53535009181c"),
        bytes.fromhex("686974207468652062756c6c277320657965"))
    assert output == b"the kid don't play"
    print(bytes_to_string(output))
    print(output.hex())


def challenge3():
    """Single-byte XOR cipher"""
    cipher_hex = "1b37373331363f78151b7f2b783431333d78397828372d363c78373e783a393b3736"
    ciphertext = bytes.fromhex(cipher_hex)
    score_data = english_like_score_data(ciphertext)
    best_data = nlargest(5, score_data, key=lambda x: x["score"])
    pp(best_data)
    print(bytes_to_string(best_data[0]["message"]))
    assert best_data[0]["message"] == b"Cooking MC's like a pound of bacon"


def challenge4():
    """Detect single-character XOR"""
    with open("4.txt") as f:
        ciphertexts = [bytes.fromhex(line.strip()) for line in f.readlines()]
    decoded_string_data = []
    for i, ciphertext in enumerate(ciphertexts):
        decoded_string_data.append(best_english_like_score_data(ciphertext))
        decoded_string_data[-1]["index"] = i
    best_decodings = nlargest(3, decoded_string_data, key=lambda d: d["score"])
    pp(best_decodings)
    assert best_decodings[0]["message"] == b"Now that the party is jumping\n"


def challenge5():
    """Implement repeating-key XOR"""
    stanza = ("Burning 'em, if you ain't quick and nimble\n"
        "I go crazy when I hear a cymbal")
    result = xor_encrypt(stanza.encode("utf-8"), b"ICE").hex()
    assert result == ("0b3637272a2b2e63622c2e69692a23693a2a3c6324202d623d63343"
        "c2a26226324272765272a282b2f20430a652e2c652a3124333a653e2b2027630c692b"
        "20283165286326302e27282f")
    print(result)


def challenge6():
    """Break repeating-key XOR"""
    def edit_distance(bytes1, bytes2):
        result = 0
        for byte1, byte2 in zip(bytes1, bytes2):
            result += sum(1 for i in range(8) if byte1 & (1 << i) != byte2 & (1 << i))
        return result

    assert edit_distance(b"this is a test", b"wokka wokka!!!") == 37
    with open("6.txt") as f:
        ciphertext = base64.b64decode(f.read())
    edit_distances = defaultdict(int)
    for key_size in range(2, 41):
        chunks = byte_chunks(ciphertext, key_size)
        for i in range(10):
            edit_distances[key_size] += edit_distance(chunks[i], chunks[i + 1])
        edit_distances[key_size] /= key_size
    best_key_size = min(edit_distances, key=edit_distances.get)

    cipher_chunks = byte_chunks(ciphertext, best_key_size)
    plain_chunks, key = crack_common_xor_key(cipher_chunks)
    plaintext = bytes_to_string(b"".join(plain_chunks))
    print(key)
    print()
    print(plaintext)
    assert "white boy" in plaintext


def challenge7():
    """AES in ECB mode"""
    with open("7.txt") as f:
        ciphertext = base64.b64decode(f.read())
    message = AES.new(b"YELLOW SUBMARINE", AES.MODE_ECB).decrypt(ciphertext)
    print(bytes_to_string(message))
    assert b"white boy" in message


def challenge8():
    """Detect AES in ECB mode"""
    with open("8.txt") as f:
        lines = f.readlines()
    ecb_texts = []
    for i, line in enumerate(lines):
        ciphertext = bytes.fromhex(line.strip())
        if looks_like_ecb(ciphertext):
            ecb_texts.append({"index": i, "ciphertext": ciphertext})
    pp(ecb_texts)
    assert len(ecb_texts) == 1


def challenge9():
    """Implement PKCS#7 padding"""
    assert pkcs7_pad(b"YELLOW SUBMARINE", 20) == b"YELLOW SUBMARINE\x04\x04\x04\x04"


def challenge10():
    """Implement CBC mode"""
    with open("10.txt") as f:
        ciphertext = base64.b64decode(f.read())
    key = b"YELLOW SUBMARINE"
    iv = bytes([0] * 16)

    plain_bytes = cbc_decrypt(key, iv, ciphertext)
    assert b"white boy" in plain_bytes
    assert plain_bytes == AES.new(key, AES.MODE_CBC, iv).decrypt(ciphertext)

    # Create new cipher object because using cipher object messes up
    # internal IV state.
    new_ciphertext = cbc_encrypt(key, iv, plain_bytes)
    assert new_ciphertext == AES.new(key, AES.MODE_CBC, iv).encrypt(plain_bytes)
    assert new_ciphertext == ciphertext


def challenge11():
    """An ECB/CBC detection oracle"""
    def encrypt_with_random_mode(plain_bytes):
        key = create_random_aes_key()
        mode = random.choice([AES.MODE_CBC, AES.MODE_ECB])
        # iv is ignored for MODE_ECB
        iv = os.urandom(16)
        prefix = os.urandom(random.randint(5, 10))
        suffix = os.urandom(random.randint(5, 10))
        bytes_to_encrypt = pkcs7_pad(prefix + plain_bytes + suffix)
        return (AES.new(key, mode, iv).encrypt(bytes_to_encrypt), mode)

    # hamlet.txt from http://erdani.com/tdpl/hamlet.txt
    # This seems to work perfectly when encrypting 2923 or more bytes of
    # hamlet.txt, but frequently guesses incorrectly with 2922 bytes or
    # fewer. Different files produce different results but for any given
    # file, there seems to be a precise amount of data at which this
    # function works reliably, and below which it frequently thinks ECB is
    # CBC.
    with open("hamlet.txt", "rb") as f:
        plain_bytes = f.read(3000)
    results = Counter()
    for i in range(1000):
        ciphertext, mode_number = encrypt_with_random_mode(plain_bytes)
        mode = {1: "ECB", 2: "CBC"}[mode_number]
        apparent_mode = "ECB" if looks_like_ecb(ciphertext) else "CBC"
        results[apparent_mode] += 1
        assert mode == apparent_mode, (mode, apparent_mode, results)


def challenge12():
    """Byte-at-a-time ECB decryption (Simple)"""
    unknown_bytes = base64.b64decode(
        "Um9sbGluJyBpbiBteSA1LjAKV2l0aCBteSByYWctdG9wIGRvd24gc28gbXkgaGFpciBjYW"
        "4gYmxvdwpUaGUgZ2lybGllcyBvbiBzdGFuZGJ5IHdhdmluZyBqdXN0IHRvIHNheSBoaQpE"
        "aWQgeW91IHN0b3A/IE5vLCBJIGp1c3QgZHJvdmUgYnkK")
    cipher = AES.new(create_random_aes_key(), AES.MODE_ECB)

    def oracle_fn(attacker_bytes):
        return cipher.encrypt(pkcs7_pad(attacker_bytes + unknown_bytes))

    block_size = guess_block_size(oracle_fn)
    assert block_size == 16

    plaintext = crack_ecb_oracle(oracle_fn)
    print(bytes_to_string(plaintext))
    assert plaintext == unknown_bytes


def challenge13():
    """ECB cut-and-paste"""
    cipher = AES.new(create_random_aes_key(), mode=AES.MODE_ECB)

    def create_encrypted_user_profile(email_address):
        profile_data = [("email", email_address), ("uid", "10"), ("role", "user")]
        return cipher.encrypt(pkcs7_pad(urlencode(profile_data).encode("utf-8")))

    def decrypt_profile(encrypted_profile):
        return bytes_to_string(pkcs7_unpad(cipher.decrypt(encrypted_profile)))


    profile1 = create_encrypted_user_profile("peter.gregory@piedpiper.com")
    profile1_blocks = byte_chunks(profile1)

    profile2 = create_encrypted_user_profile("zach.woods@piedpiper.comadmin")
    profile2_blocks = byte_chunks(profile2)

    profile3 = create_encrypted_user_profile("a@a.com")
    padding_only_block = byte_chunks(profile3)[-1]

    new_profile = b"".join(profile1_blocks[:3]) + profile2_blocks[2] + padding_only_block
    decrypted_new_profile = decrypt_profile(new_profile)
    assert parse_qs(decrypted_new_profile)["role"] == ["admin"]
    print(decrypted_new_profile)
    # TODO: try to make a profile without duplicate uid params and "rol"
    # string at end


def challenge14():
    """Byte-at-a-time ECB decryption (Harder)"""
    cipher = AES.new(create_random_aes_key(), AES.MODE_ECB)
    random_bytes = os.urandom(random.randint(0, 64))
    target_bytes = EXAMPLE_PLAIN_BYTES

    def oracle_fn(attacker_bytes):
        return cipher.encrypt(pkcs7_pad(random_bytes + attacker_bytes + target_bytes))

    assert appears_to_produce_ecb(oracle_fn)
    block_size = guess_block_size(oracle_fn)
    assert block_size == 16

    blocks = byte_chunks(oracle_fn(b"A" * 3*block_size))
    attacker_block, attacker_block_count = Counter(blocks).most_common(1)[0]
    assert attacker_block_count >= 2
    attacker_block_pos = block_size * blocks.index(attacker_block)
    for i in range(block_size):
        blocks = byte_chunks(oracle_fn(b"A" * (3*block_size - i - 1)))
        if blocks.count(attacker_block) < attacker_block_count:
            prefix_length = attacker_block_pos - (-i % block_size)
            break
    # TODO: make prefix_length calculation work reliably even if attacker
    # bytes look like random bytes or target bytes.

    plaintext = crack_ecb_oracle(oracle_fn, prefix_length=prefix_length)
    assert plaintext == target_bytes


def challenge15():
    """PKCS#7 padding validation"""
    assert pkcs7_unpad(b"ICE ICE BABY\x04\x04\x04\x04") == b"ICE ICE BABY"

    try:
        pkcs7_unpad(b"ICE ICE BABY\x05\x05\x05\x05")
    except ValueError:
        pass
    else:
        assert False, "Padding should not be considered valid"

    try:
        pkcs7_unpad(b"ICE ICE BABY\x01\x02\x03\x04")
    except ValueError:
        pass
    else:
        assert False, "Padding should not be considered valid"


def challenge16():
    """CBC bitflipping attacks"""
    key = create_random_aes_key()
    iv = os.urandom(16)

    cipher = AES.new(key, AES.MODE_CBC, iv)
    ciphertext = create_encrypted_query_string(cipher, "foo")

    bits_to_flip = (bytes([0] * 32) +
        xor_bytes(b"like%20a%20pound", b";admin=true;foo=") + bytes([0] * 32))
    modified_ciphertext = xor_bytes(ciphertext, bits_to_flip)

    cipher = AES.new(key, AES.MODE_CBC, iv)
    assert encrypted_string_has_admin(modified_ciphertext, cipher)


def challenge17():
    """The CBC padding oracle"""
    unknown_strings = [base64.b64decode(x) for x in [
        "MDAwMDAwTm93IHRoYXQgdGhlIHBhcnR5IGlzIGp1bXBpbmc=",
        "MDAwMDAxV2l0aCB0aGUgYmFzcyBraWNrZWQgaW4gYW5kIHRoZSBWZWdhJ3MgYXJlIHB1bXBpbic=",
        "MDAwMDAyUXVpY2sgdG8gdGhlIHBvaW50LCB0byB0aGUgcG9pbnQsIG5vIGZha2luZw==",
        "MDAwMDAzQ29va2luZyBNQydzIGxpa2UgYSBwb3VuZCBvZiBiYWNvbg==",
        "MDAwMDA0QnVybmluZyAnZW0sIGlmIHlvdSBhaW4ndCBxdWljayBhbmQgbmltYmxl",
        "MDAwMDA1SSBnbyBjcmF6eSB3aGVuIEkgaGVhciBhIGN5bWJhbA==",
        "MDAwMDA2QW5kIGEgaGlnaCBoYXQgd2l0aCBhIHNvdXBlZCB1cCB0ZW1wbw==",
        "MDAwMDA3SSdtIG9uIGEgcm9sbCwgaXQncyB0aW1lIHRvIGdvIHNvbG8=",
        "MDAwMDA4b2xsaW4nIGluIG15IGZpdmUgcG9pbnQgb2g=",
        "MDAwMDA5aXRoIG15IHJhZy10b3AgZG93biBzbyBteSBoYWlyIGNhbiBibG93",
    ]]

    random.shuffle(unknown_strings)

    def create_encrypted_string(random_string):
        cipher = AES.new(key, AES.MODE_CBC, iv)
        return cipher.encrypt(pkcs7_pad(random_string))

    def has_valid_padding(iv, ciphertext):
        cipher = AES.new(key, AES.MODE_CBC, iv)
        plain_bytes = cipher.decrypt(ciphertext)
        try:
            pkcs7_unpad(plain_bytes)
        except ValueError:
            return False
        else:
            return True

    key = create_random_aes_key()
    iv = os.urandom(16)

    for unknown_string in unknown_strings:
        ciphertext = create_encrypted_string(unknown_string)
        recovered_plaintext = bytearray()
        prev_cipher_block = iv
        for cipher_block in byte_chunks(ciphertext):
            recovered_block = bytes()
            for pos in reversed(range(16)):
                assert len(recovered_block) == 15 - pos
                cipher_slice = prev_cipher_block[pos + 1:]
                padding = bytes([len(recovered_block) + 1] * len(recovered_block))
                iv_end = xor_bytes(cipher_slice, padding, recovered_block)
                new_iv = bytearray(prev_cipher_block[:pos] + b"\x00" + iv_end)
                for i in range(256):
                    new_iv[pos] = prev_cipher_block[pos] ^ i ^ (16 - pos)
                    if has_valid_padding(bytes(new_iv), cipher_block):
                        if not recovered_block:
                            new_iv[14] ^= 2
                            if not has_valid_padding(bytes(new_iv), cipher_block):
                                # Last byte of cipher_block appears to have \x01 for
                                # padding, but this is wrong.
                                # See https://blog.skullsecurity.org/2013/padding-oracle-attacks-in-depth
                                continue
                        recovered_block = bytes([i]) + recovered_block
                        break
            recovered_plaintext += recovered_block
            prev_cipher_block = cipher_block
        recovered_plaintext = pkcs7_unpad(recovered_plaintext)
        assert recovered_plaintext == unknown_string
        print(bytes_to_string(recovered_plaintext))


def challenge18():
    """Implement CTR, the stream cipher mode"""
    ciphertext = base64.b64decode("L77na/nrFsKvynd6HzOoG7GHTLXsTVu9qvY/"
        "2syLXzhPweyyMTJULu/6/kXX0KSvoOLSFQ==")
    key = b"YELLOW SUBMARINE"
    ecb_cipher = AES.new(key, AES.MODE_ECB)
    nonce = 0

    plaintext = bytearray()
    ctr_iterator = create_ctr_counter(nonce).__self__
    for counter_value, block in zip(ctr_iterator, byte_chunks(ciphertext)):
        keystream = ecb_cipher.encrypt(counter_value)
        plaintext += xor_bytes(keystream[:len(block)], block)
    print(bytes_to_string(plaintext))

    ctr_cipher = AES.new(key, AES.MODE_CTR, counter=create_ctr_counter(nonce))
    assert plaintext == ctr_cipher.decrypt(ciphertext)


def challenge19():
    """Break fixed-nonce CTR mode using substitions"""
    # [sic]. "substitions" looks like a typo but I don't know what it is
    # supposed to say.
    key = create_random_aes_key()

    def encrypt(ciphertext):
        cipher = AES.new(key, AES.MODE_CTR, counter=create_ctr_counter(0))
        return cipher.encrypt(ciphertext)

    plaintexts = [base64.b64decode(x) for x in [
        "SSBoYXZlIG1ldCB0aGVtIGF0IGNsb3NlIG9mIGRheQ==",
        "Q29taW5nIHdpdGggdml2aWQgZmFjZXM=",
        "RnJvbSBjb3VudGVyIG9yIGRlc2sgYW1vbmcgZ3JleQ==",
        "RWlnaHRlZW50aC1jZW50dXJ5IGhvdXNlcy4=",
        "SSBoYXZlIHBhc3NlZCB3aXRoIGEgbm9kIG9mIHRoZSBoZWFk",
        "T3IgcG9saXRlIG1lYW5pbmdsZXNzIHdvcmRzLA==",
        "T3IgaGF2ZSBsaW5nZXJlZCBhd2hpbGUgYW5kIHNhaWQ=",
        "UG9saXRlIG1lYW5pbmdsZXNzIHdvcmRzLA==",
        "QW5kIHRob3VnaHQgYmVmb3JlIEkgaGFkIGRvbmU=",
        "T2YgYSBtb2NraW5nIHRhbGUgb3IgYSBnaWJl",
        "VG8gcGxlYXNlIGEgY29tcGFuaW9u",
        "QXJvdW5kIHRoZSBmaXJlIGF0IHRoZSBjbHViLA==",
        "QmVpbmcgY2VydGFpbiB0aGF0IHRoZXkgYW5kIEk=",
        "QnV0IGxpdmVkIHdoZXJlIG1vdGxleSBpcyB3b3JuOg==",
        "QWxsIGNoYW5nZWQsIGNoYW5nZWQgdXR0ZXJseTo=",
        "QSB0ZXJyaWJsZSBiZWF1dHkgaXMgYm9ybi4=",
        "VGhhdCB3b21hbidzIGRheXMgd2VyZSBzcGVudA==",
        "SW4gaWdub3JhbnQgZ29vZCB3aWxsLA==",
        "SGVyIG5pZ2h0cyBpbiBhcmd1bWVudA==",
        "VW50aWwgaGVyIHZvaWNlIGdyZXcgc2hyaWxsLg==",
        "V2hhdCB2b2ljZSBtb3JlIHN3ZWV0IHRoYW4gaGVycw==",
        "V2hlbiB5b3VuZyBhbmQgYmVhdXRpZnVsLA==",
        "U2hlIHJvZGUgdG8gaGFycmllcnM/",
        "VGhpcyBtYW4gaGFkIGtlcHQgYSBzY2hvb2w=",
        "QW5kIHJvZGUgb3VyIHdpbmdlZCBob3JzZS4=",
        "VGhpcyBvdGhlciBoaXMgaGVscGVyIGFuZCBmcmllbmQ=",
        "V2FzIGNvbWluZyBpbnRvIGhpcyBmb3JjZTs=",
        "SGUgbWlnaHQgaGF2ZSB3b24gZmFtZSBpbiB0aGUgZW5kLA==",
        "U28gc2Vuc2l0aXZlIGhpcyBuYXR1cmUgc2VlbWVkLA==",
        "U28gZGFyaW5nIGFuZCBzd2VldCBoaXMgdGhvdWdodC4=",
        "VGhpcyBvdGhlciBtYW4gSSBoYWQgZHJlYW1lZA==",
        "QSBkcnVua2VuLCB2YWluLWdsb3Jpb3VzIGxvdXQu",
        "SGUgaGFkIGRvbmUgbW9zdCBiaXR0ZXIgd3Jvbmc=",
        "VG8gc29tZSB3aG8gYXJlIG5lYXIgbXkgaGVhcnQs",
        "WWV0IEkgbnVtYmVyIGhpbSBpbiB0aGUgc29uZzs=",
        "SGUsIHRvbywgaGFzIHJlc2lnbmVkIGhpcyBwYXJ0",
        "SW4gdGhlIGNhc3VhbCBjb21lZHk7",
        "SGUsIHRvbywgaGFzIGJlZW4gY2hhbmdlZCBpbiBoaXMgdHVybiw=",
        "VHJhbnNmb3JtZWQgdXR0ZXJseTo=",
        "QSB0ZXJyaWJsZSBiZWF1dHkgaXMgYm9ybi4="]]

    ciphertexts = [encrypt(x) for x in plaintexts]

    recovered_plaintexts, recovered_key = crack_common_xor_key(ciphertexts)
    print("\n".join(bytes_to_string(p) for p in recovered_plaintexts))


def challenge20():
    """Break fixed-nonce CTR statistically"""
    key = create_random_aes_key()

    def encrypt(ciphertext):
        cipher = AES.new(key, AES.MODE_CTR, counter=create_ctr_counter(0))
        return cipher.encrypt(ciphertext)

    with open("20.txt") as f:
        plaintexts = [base64.b64decode(x) for x in f.readlines()]
    ciphertexts = [encrypt(x) for x in plaintexts]
    recovered_plaintexts, recovered_key = crack_common_xor_key(ciphertexts)
    print("\n".join(bytes_to_string(p) for p in recovered_plaintexts))


def challenge21():
    """Implement the MT19937 Mersenne Twister RNG"""
    rng = MT19937_RNG(seed=0)
    numbers = [rng.get_number() for _ in range(10)]
    assert numbers == [2357136044, 2546248239, 3071714933, 3626093760, 2588848963,
        3684848379, 2340255427, 3638918503, 1819583497, 2678185683]


def challenge22():
    """Crack an MT19937 seed"""
    seed = int(time()) + random.randint(40, 1000)
    output = MT19937_RNG(seed).get_number()
    future = seed + random.randint(40, 1000)
    for seed_guess in reversed(range(future - 1000, future)):
        if MT19937_RNG(seed_guess).get_number() == output:
            assert seed_guess == seed
            return
    assert False, "seed not found"


def challenge23():
    """Clone an MT19937 RNG from its output"""
    rng = MT19937_RNG(seed=random.getrandbits(32))
    numbers = [rng.get_number() for _ in range(624)]

    # The seed passed in the next line has no effect since the buffer is
    # being overwritten.
    rng2 = MT19937_RNG(seed=0)
    rng2.buffer = [MT19937_RNG.untemper(x) for x in numbers]
    rng2.index = 0
    numbers2 = [rng2.get_number() for _ in range(624)]
    assert numbers == numbers2


def challenge24():
    """Create the MT19937 stream cipher and break it"""
    def encrypt_with_rng(rng, ciphertext):
        result = bytearray()
        for chunk in byte_chunks(ciphertext, 4):
            # Create 4-byte chunk from rng
            keystream_bytes = struct.pack(">L", rng.get_number())
            result += xor_bytes(chunk, keystream_bytes[:len(chunk)])
        return bytes(result)

    def encrypt_with_random_prefix(rng, plain_bytes):
        prefix = os.urandom(random.randint(0, 64))
        return encrypt_with_rng(rng, prefix + plain_bytes)

    def create_token(timestamp):
        rng = MT19937_RNG(seed=timestamp)
        return struct.pack(">4L", *[rng.get_number() for _ in range(4)])

    def token_came_from_timestamp(token, timestamp):
        rng = MT19937_RNG(seed=timestamp)
        return token == struct.pack(">4L", *[rng.get_number() for _ in range(4)])

    def partially_twist(buffer, n):
        # Populate buffer with the first n results of twisting. This function
        # destroys the internal state of whatever RNG it belongs to, so the RNG
        # should no longer be used after being passed to this function.
        for i in range(n):
            y = ((buffer[i] & 0x80000000) +
                       (buffer[(i + 1) % 624] & 0x7fffffff))
            buffer[i] = buffer[(i + 397) % 624] ^ (y >> 1)
            if y & 1:
                buffer[i] ^= 0x9908b0df

    seed = random.getrandbits(16)
    test_ciphertext = encrypt_with_rng(MT19937_RNG(seed), EXAMPLE_PLAIN_BYTES)
    assert encrypt_with_rng(MT19937_RNG(seed), test_ciphertext) == EXAMPLE_PLAIN_BYTES

    seed = random.getrandbits(16)
    my_bytes = b"A" * 14
    ciphertext = encrypt_with_random_prefix(MT19937_RNG(seed), my_bytes)
    cipher_chunks = byte_chunks(ciphertext, 4)
    # Get bytes from last 2 chunks, excluding last chunk, which may not have
    # 4 bytes, and therefore may not allow me to determine the keystream
    # numbers.
    ciphertext_with_my_string = b"".join(cipher_chunks[-3:-1])
    keystream = xor_encrypt(ciphertext_with_my_string, b"A")
    keystream_numbers = list(struct.unpack(">LL", keystream))
    untempered_numbers = [MT19937_RNG.untemper(x) for x in keystream_numbers]

    for seed_guess in range(2**16):
        if seed_guess % 5000 == 0:
            print("tried {} seeds".format(seed_guess))
        test_rng = MT19937_RNG(seed_guess)
        # The obvious way to test whether seed_guess is right is to generate
        # (len(cipher_chunks) - 1) numbers from test_rng and see whether the
        # last 2 match keystream_numbers. However, that is agonizingly slow, so
        # I am using partially_twist instead.
        partially_twist(test_rng.buffer, len(cipher_chunks) - 1)
        buffer_slice = test_rng.buffer[len(cipher_chunks) - 3 : len(cipher_chunks) - 1]
        if buffer_slice == untempered_numbers:
            print("found seed: {}".format(seed_guess))
            assert seed_guess == seed
            break
    else:
        assert False, "seed not found"

    now = int(time())
    token = create_token(now)
    assert token_came_from_timestamp(token, now)


def challenge25():
    """Break "random access read/write" AES CTR"""
    key = create_random_aes_key()
    nonce = random.getrandbits(64)

    def edit(ciphertext, block_index, new_bytes):
        if len(new_bytes) % 16 != 0:
            raise ValueError("new_bytes must be a multiple of 16 bytes long")
        counter = create_ctr_counter(nonce, block_index)
        cipher = AES.new(key, AES.MODE_CTR, counter=counter)
        new_ciphertext = cipher.encrypt(new_bytes)
        result = bytearray(ciphertext)
        result[16*block_index : 16*block_index + len(new_bytes)] = new_ciphertext
        return bytes(result)

    # 25.txt is identical to 7.txt
    with open("25.txt") as f:
        temp_bytes = base64.b64decode(f.read())
    plain_bytes = AES.new(b"YELLOW SUBMARINE", AES.MODE_ECB).decrypt(temp_bytes)
    cipher = AES.new(key, AES.MODE_CTR, counter=create_ctr_counter(nonce))
    ciphertext = cipher.encrypt(plain_bytes)

    keystream = edit(ciphertext, 0, bytes([0]) * len(plain_bytes))
    recovered_plaintext = xor_bytes(ciphertext, keystream)
    assert recovered_plaintext == plain_bytes


def challenge26():
    """CTR bitflipping"""
    key = create_random_aes_key()
    nonce = random.getrandbits(64)

    cipher = AES.new(key, AES.MODE_CTR, counter=create_ctr_counter(nonce))
    ciphertext = create_encrypted_query_string(cipher, "A" * 16)
    new_ciphertext = bytearray(ciphertext)
    new_ciphertext[32:48] = xor_bytes(
        b"A" * 16, b"ha_ha;admin=true", new_ciphertext[32:48])
    new_ciphertext = bytes(new_ciphertext)

    cipher = AES.new(key, AES.MODE_CTR, counter=create_ctr_counter(nonce))
    assert encrypted_string_has_admin(new_ciphertext, cipher)


def challenge27():
    """Recover the key from CBC with IV=Key"""
    key = create_random_aes_key()
    iv = key

    def create_encrypted_string(user_bytes):
        return AES.new(key, AES.MODE_CBC, iv).encrypt(pkcs7_pad(user_bytes))

    def decrypt(ciphertext):
        plain_bytes = AES.new(key, AES.MODE_CBC, iv).decrypt(ciphertext)
        return pkcs7_unpad(plain_bytes.decode("ascii"))

    ciphertext = create_encrypted_string(EXAMPLE_PLAIN_BYTES)
    modified_ciphertext = ciphertext[:16] + bytes([0] * 16) + ciphertext

    try:
        decrypted_plaintext = decrypt(modified_ciphertext)
    except UnicodeDecodeError as e:
        plain_bytes = e.object
        recovered_key = xor_bytes(plain_bytes[0:16], plain_bytes[32:48])
        assert recovered_key == key
    else:
        assert False


def challenge28():
    """Implement a SHA-1 keyed MAC"""
    key1 = os.urandom(16)
    key2 = os.urandom(16)
    assert sha1(key1 + b"message1") != sha1(key1 + b"message2")
    assert sha1(key1 + b"message1") != sha1(key2 + b"message2")


def challenge29():
    """Break a SHA-1 keyed MAC using length extension"""
    def sha1_padding(message_length):
        return (b"\x80" +
            b"\x00" * ((55 - message_length) % 64) +
            struct.pack(">Q", message_length * 8))

    my_padding = sha1_padding(len(EXAMPLE_PLAIN_BYTES))
    their_padding = Sha1Hash().update(EXAMPLE_PLAIN_BYTES)._produce_padding()
    assert their_padding == my_padding

    key = os.urandom(16)
    query_string = (b"comment1=cooking%20MCs;userdata=foo;"
        b"comment2=%20like%20a%20pound%20of%20bacon")
    mac = sha1(key + query_string)

    glue_padding = sha1_padding(len(key + query_string))
    new_param = b";admin=true"
    modified_hash_fn = Sha1Hash(
        prefix_hash=mac,
        prefix_length=len(key + query_string + glue_padding))
    new_hash = modified_hash_fn.update(new_param).digest()

    expected_hash = sha1(key + query_string + glue_padding + new_param)
    assert new_hash == expected_hash


def challenge30():
    """Break an MD4 keyed MAC using length extension"""
    def md4_padding(message_length):
        # Very similar to sha1_padding, but little endian instead of big endian
        return (b"\x80" +
            b"\x00" * ((55 - message_length) % 64) +
            struct.pack("<Q", message_length * 8))

    key = os.urandom(16)
    query_string = (b"comment1=cooking%20MCs;userdata=foo;"
        b"comment2=%20like%20a%20pound%20of%20bacon")
    mac = MD4(key + query_string)

    glue_padding = md4_padding(len(key + query_string))
    new_param = b";admin=true"
    new_hash = MD4(new_param,
        fake_byte_len=len(key + query_string + glue_padding + new_param),
        state=struct.unpack("<4I", mac))

    expected_hash = MD4(key + query_string + glue_padding + new_param)
    assert new_hash == expected_hash


def challenge31():
    """Implement and break HMAC-SHA1 with an artificial timing leak"""
    def signature_is_valid(signature):
        return insecure_compare(hmac, signature, 0.05)

    key = os.urandom(16)
    data = EXAMPLE_PLAIN_BYTES
    hmac = get_hmac(key, data)

    print("looking for {}".format(list(get_hmac(key, data))))
    print()
    signature = recover_signature(signature_is_valid, quiet=False)
    print("recovered signature: {}".format(list(signature)))
    assert get_hmac(key, data) == signature


def challenge31_with_server():
    """Challenge 31 with actual server instead of comparison function"""
    # TODO: use this in place of what I have for challenge 31 when I can
    # make it work reliably.
    def signature_is_valid(signature):
        query = urlencode({"file": "hamlet.txt", "signature": signature.hex()})
        try:
            urlopen("http://localhost:31415/signature_is_valid?" + query)
        except HTTPError:
            return False
        else:
            return True

    key = os.urandom(16)
    with open("hamlet.txt", "rb") as f:
        data = f.read()
    hmac = get_hmac(key, data)

    print("looking for {}".format(list(get_hmac(key, data))))
    print()
    FancyHTTPServer = type("FancyHTTPServer", (ThreadingMixIn, HTTPServer), {})
    server = FancyHTTPServer(("localhost", 31415), ValidatingRequestHandler)
    server.hmac_key = key
    server.validate_signature = lambda hmac, sig: insecure_compare(hmac, sig, 0.05)
    try:
        with open(os.devnull, "w") as null_stream:
            with redirect_stderr(null_stream):
                Thread(target=server.serve_forever).start()
                print("Server is running on {}".format(server.server_address))
                print()
                signature = recover_signature(
                    signature_is_valid,
                    quiet=False,
                    thread_count=6)
                print("recovered signature: {}".format(list(signature)))
    finally:
        server.shutdown()
        server.server_close()
        pp(get_hmac.cache_info())

    assert get_hmac(key, data) == signature


def challenge32():
    """Break HMAC-SHA1 with a slightly less artificial timing leak"""
    # This works reliably with timing differences down to about 20ms. I am
    # planning to improve it, probably some time after I get the web server
    # working.

    def signature_is_valid(signature):
        return insecure_compare(hmac, signature, 0.025)

    key = os.urandom(16)
    data = EXAMPLE_PLAIN_BYTES
    hmac = get_hmac(key, data)

    print("looking for {}".format(list(get_hmac(key, data))))
    print()
    signature = recover_signature(signature_is_valid, quiet=False)
    print("recovered signature: {}".format(list(signature)))
    assert get_hmac(key, data) == signature


def challenge33():
    """Implement Diffie-Hellman"""
    p = 37
    g = 5
    a = random.randrange(p)
    A = pow(g, a, p)
    b = random.randrange(p)
    B = pow(g, b, p)
    assert pow(A, b, p) == pow(B, a, p)

    p = NIST_DIFFIE_HELLMAN_PRIME
    g = 2
    a = random.randrange(p)
    A = pow(g, a, p)
    b = random.randrange(p)
    B = pow(g, b, p)
    assert pow(A, b, p) == pow(B, a, p)


def test_all_challenges(output_stream=sys.stdout):
    challenges = {}
    for name, var in globals().copy().items():
        try:
            num = int(re.findall("challenge(\d+)$", name)[0])
        except (IndexError, ValueError):
            pass
        else:
            if callable(var):
                challenges[num] = var
    for num in sorted(challenges):
        print("Running challenge {}: {}".format(num, challenges[num].__doc__),
            file=output_stream)
        challenges[num]()
    # If this point is reached, no exceptions occurred in the challenges, so
    # they all passed. TODO: come up with a less hacky and more flexible way
    # to test for this.
    print("All challenges passed.", file=output_stream)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Solve the Matasano crypto challenges.")
    parser.add_argument(
        "challenge", nargs="?",
        help="The challenge to run. If this is not specified, all challenges will be "
             "run.")
    parser.add_argument(
        "-p", "--profile", help="Profile challenges.", action="store_true")
    parser.add_argument(
        "-q", "--quiet", help="Don't show challenge output.", action="store_true")
    args = parser.parse_args()

    if args.challenge:
        func = globals().get("challenge" + args.challenge)
        if not func:
            parser.error("Challenge {} not found".format(args.challenge))
    else:
        real_stdout = sys.stdout
        func = lambda: test_all_challenges(real_stdout)
    with ExitStack() as stack:
        if args.profile:
            profile = cProfile.Profile()
            stack.callback(profile.print_stats, sort="cumtime")
        if args.quiet:
            null_stream = open(os.devnull, "w")
            stack.enter_context(null_stream)
            stack.enter_context(redirect_stdout(null_stream))
        if args.profile:
            profile.runcall(func)
        else:
            func()
