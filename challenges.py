#!/usr/bin/env python3

import argparse
import base64
import cProfile
import os
import pprint
import re
import struct
import sys
import traceback
import warnings

from collections import Counter, defaultdict
from contextlib import ExitStack, redirect_stdout
from functools import lru_cache
from hashlib import sha256
from heapq import nlargest
from http.server import BaseHTTPRequestHandler, HTTPServer
from itertools import count, cycle
from multiprocessing.dummy import Pool as ThreadPool
from random import SystemRandom
from socketserver import ThreadingMixIn
from statistics import median
from threading import Thread
from time import perf_counter, sleep, time
from urllib.error import HTTPError
from urllib.parse import parse_qs, quote as url_quote, urlencode, urlparse
from urllib.request import urlopen

from Crypto.Cipher import AES
from Crypto.Util.number import getStrongPrime
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


IETF_DIFFIE_HELLMAN_PRIME = int("ffffffffffffffffc90fdaa22168c234c4c6628b80dc1c"
    "d129024e088a67cc74020bbea63b139b22514a08798e3404ddef9519b3cd3a431b302b0a6d"
    "f25f14374fe1356d6d51c245e485b576625e7ec6f44c42e9a637ed6b0bff5cb6f406b7edee"
    "386bfb5a899fa5ae9f24117c4b1fe649286651ece45b3dc2007cb8a163bf0598da48361c55"
    "d39a69163fa8fd24cf5f83655d23dca3ad961c62f356208552bb9ed529077096966d670c35"
    "4e4abc9804f1746c08ca237327ffffffffffffffff", 16)


def pp(*args, width=120, **kwargs):
    pprint.pprint(*args, width=width, **kwargs)


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


def int_to_bytes(x):
    return x.to_bytes(length=(x.bit_length() // 8) + 1, byteorder="big")


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
    for i in range(max(len(c) for c in ciphertexts)):
        transposed_block = bytes(c[i] for c in ciphertexts if i < len(c))
        key.append(best_english_like_score_data(transposed_block)["key"])
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


def random_aes_key():
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


def encrypted_query_string(cipher, user_data):
    query_string = ("comment1=cooking%20MCs;userdata=" + url_quote(user_data) +
        ";comment2=%20like%20a%20pound%20of%20bacon")
    bytes_to_encrypt = pkcs7_pad(query_string.encode("utf-8"))
    return cipher.encrypt(bytes_to_encrypt)


def ctr_iterator(nonce, block_index=0):
    return (struct.pack("<QQ", nonce, i) for i in count(start=block_index))


def ctr_counter(nonce, block_index=0):
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
    return ctr_iterator(nonce, block_index).__next__


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
    return Sha1Hash().update(message)


def calculate_hmac(key, message, hash_fn=sha1):
    key_hash = hash_fn(key).digest()
    o_key_pad = xor_encrypt(key_hash, b"\x5c")
    i_key_pad = xor_encrypt(key_hash, b"\x36")
    return hash_fn(o_key_pad + hash_fn(i_key_pad + message).digest()).digest()


get_hmac = lru_cache()(calculate_hmac)


def insecure_compare(data1, data2, delay):
    if len(data1) != len(data2):
        return False
    for byte1, byte2 in zip(data1, data2):
        if byte1 != byte2:
            return False
        sleep(delay)
    return True


class FancyHTTPServer(ThreadingMixIn, HTTPServer):
    request_queue_size = 128


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

    def log_message(self, format, *args):
        pass


def server_approves_of_signature(signature):
    query = urlencode({"file": "hamlet.txt", "signature": signature.hex()})
    try:
        urlopen("http://localhost:31415/signature_is_valid?" + query)
    except HTTPError:
        return False
    else:
        return True


class CantRecoverSignatureError(Exception):
    pass


def recover_signature(validate_signature, thread_count, threshold, attempt_limit):
    # TODO: make this function figure out threshold on its own

    def try_signature(signature):
        start_time = perf_counter()
        is_valid = validate_signature(signature)
        duration = perf_counter() - start_time
        return {"signature": signature, "is_valid": is_valid, "duration": duration}

    result = bytearray()
    sig_durations = defaultdict(list)
    with ThreadPool(thread_count) as pool:
        for pos in range(20):
            assert pos == len(result)
            test_sigs = [bytes(result + bytes([b] + [0]*(19 - pos))) for b in range(256)]
            for i in range(attempt_limit):
                for sig_data in pool.imap_unordered(try_signature, test_sigs):
                    signature = sig_data["signature"]
                    if sig_data["is_valid"]:
                        print("signature recovered: {}, "
                            "{} attempt(s) for last byte".format(list(result), i + 1))
                        return signature
                    sig_durations[signature].append(sig_data["duration"])
                slowest_sig, second_slowest_sig = nlargest(
                    2, test_sigs, key=lambda x: median(sig_durations[x]))
                slowest_duration = median(sig_durations[slowest_sig])
                second_slowest_duration = median(sig_durations[second_slowest_sig])
                duration_difference = slowest_duration - second_slowest_duration
                if duration_difference > threshold:
                    result.append(slowest_sig[pos])
                    print("recovered so far: {}, {} attempt(s) for last byte, "
                        "duration difference: {:.3f} ms".format(list(result), i + 1,
                        1000 * duration_difference))
                    break
            else:
                print("recovered so far: {}, {} attempt(s) for last byte, "
                    "duration difference: {:.3f} ms".format(list(result), i + 1,
                    1000 * duration_difference))
                raise CantRecoverSignatureError("can't recover signature")
    raise CantRecoverSignatureError("can't recover signature")


class DiffieHellmanUser:
    def __init__(self, p=IETF_DIFFIE_HELLMAN_PRIME, g=2, private_key=None):
        self.p = p
        if private_key is None:
            self._private_key = random.randint(1, p - 1)
        else:
            self._private_key = private_key
        self.public_key = pow(g, self._private_key, p)
        self._shared_keys = {}
        self._decrypted_messages = defaultdict(list)

    def get_shared_key_for(self, other):
        if other not in self._shared_keys:
            self._shared_keys[other] = pow(other.public_key, self._private_key, other.p)
        return self._shared_keys[other]

    def send_echo_request(self, other, message):
        iv, encrypted_request = self._encrypt_message(message, other)
        new_iv, response = other._respond_to_echo_request(iv, encrypted_request, self)
        assert self._decrypt_message(new_iv, response, other) == message

    def _respond_to_echo_request(self, iv, encrypted_request, other):
        message = self._decrypt_message(iv, encrypted_request, other)
        self._decrypted_messages[other].append(message)
        return self._encrypt_message(message, other)

    def _generate_symmetric_key(self, other):
        return sha1(int_to_bytes(self.get_shared_key_for(other))).digest()[:16]

    def _encrypt_message(self, message, other):
        iv = os.urandom(16)
        key = self._generate_symmetric_key(other)
        return (iv, AES.new(key, AES.MODE_CBC, iv).encrypt(pkcs7_pad(message)))

    def _decrypt_message(self, iv, ciphertext, other):
        key = self._generate_symmetric_key(other)
        return pkcs7_unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(ciphertext))


def scramble_srp_keys(A, B):
    return int(sha256(int_to_bytes(A) + int_to_bytes(B)).hexdigest(), 16)


class SRPServer:
    N = IETF_DIFFIE_HELLMAN_PRIME
    g = 2

    def __init__(self):
        self.users = {}

    def _respond_to_sign_up_request(self, username, salt, verifier):
        self.users[username] = {"salt": salt, "verifier": verifier}

    def _respond_to_login_request(self, username, A, k=3):
        # A == public ephemeral number from client
        user = self.users[username]
        b = random.randint(1, self.N - 1)  # private ephemeral number
        # B == public ephemeral number. Usually, B depends on the password, but
        # if k == 0, it is a completely random Diffie-Hellman public key, which
        # causes u to be essentially random.
        B = ((k * user["verifier"]) + pow(self.g, b, self.N)) % self.N
        u = scramble_srp_keys(A, B)
        S = pow(A * pow(user["verifier"], u, self.N), b, self.N)
        user["shared_session_key"] = sha256(int_to_bytes(S)).digest()
        return (user["salt"], B, u)

    def _verify_hmac(self, hmac, username):
        user = self.users[username]
        return hmac == get_hmac(user["shared_session_key"], user["salt"], sha256)


class MitmSRPServer(SRPServer):
    def __init__(self, real_server):
        super().__init__()
        self.real_server = real_server

    def _respond_to_login_request(self, username, A, k=3):
        if k != 0:
            raise ValueError("k must be 0")
        salt, _, _ = self.real_server._respond_to_login_request(username, A, k=k)
        b = random.randint(1, self.N - 1)
        self.users[username] = {"salt": salt, "A": A, "b": b}
        u = 1
        B = pow(self.g, b, self.N)
        return (salt, B, u)

    def _verify_hmac(self, hmac, username):
        user = self.users[username]
        # 20 most common passwords according to xato.net
        common_passwords = ["password", "123456", "12345678", "1234", "qwerty", "12345",
            "dragon", "pussy", "baseball", "football", "letmein", "monkey", "696969",
            "abc123", "mustang", "michael", "shadow", "master", "jennifer", "111111"]
        u = 1
        for test_password in common_passwords:
            test_x = SRPClient._generate_private_key(
                username, test_password, user["salt"])
            test_verifier = pow(self.g, test_x, self.N)
            test_S = pow(user["A"] * pow(test_verifier, u, self.N), user["b"], self.N)
            test_session_key = sha256(int_to_bytes(test_S)).digest()
            if get_hmac(test_session_key, user["salt"], sha256) == hmac:
                user["password"] = test_password
                return True
        return False


class SRPClient:
    N = IETF_DIFFIE_HELLMAN_PRIME
    g = 2

    def sign_up(self, server, username, password):
        salt = os.urandom(16)
        x = self._generate_private_key(username, password, salt)
        verifier = pow(self.g, x, self.N)
        server._respond_to_sign_up_request(username, salt, verifier)

    def log_in(self, server, username, password, k=3):
        a = random.randint(1, self.N - 1)  # private ephemeral number
        A = pow(self.g, a, self.N)  # public ephemeral number
        # B == public ephemeral number from server
        salt, B, u = server._respond_to_login_request(username, A, k=k)

        # TODO: figure out if it is possible to make the offline attack work if
        # the following line is uncommented
        # assert u == scramble_srp_keys(A, B)
        x = self._generate_private_key(username, password, salt)
        S = pow(B - k * pow(self.g, x, self.N), a + u*x, self.N)
        shared_session_key = sha256(int_to_bytes(S)).digest()  # called "K" in challenge
        hmac = get_hmac(shared_session_key, salt, sha256)
        return server._verify_hmac(hmac, username)

    @staticmethod
    def _generate_private_key(username, password, salt):
        inner_hash = sha256((username + ":" + password).encode()).digest()
        return int(sha256(salt + inner_hash).hexdigest(), 16)


def extended_gcd(a, b):
    if a == 0:
        return (b, 0, 1)
    else:
        g, y, x = extended_gcd(b % a, a)
        return (g, x - (b // a) * y, y)


def invmod(a, m):
    g, x, y = extended_gcd(a, m)
    if g != 1:
        raise ValueError("modular inverse does not exist")
    else:
        return x % m


def challenge1():
    """Convert hex to base64"""
    encoded_text = ("49276d206b696c6c696e6720796f757220627261696e206c" +
        "696b65206120706f69736f6e6f7573206d757368726f6f6d")
    message = bytes.fromhex(encoded_text)
    print(message.decode())
    result = base64.b64encode(message)

    assert result == b"SSdtIGtpbGxpbmcgeW91ciBicmFpbiBsaWtlIGEgcG9pc29ub3VzIG11c2hyb29t"


def challenge2():
    """Fixed XOR"""
    output = xor_bytes(
        bytes.fromhex("1c0111001f010100061a024b53535009181c"),
        bytes.fromhex("686974207468652062756c6c277320657965"))
    assert output == b"the kid don't play"
    print(output.decode())
    print(output.hex())


def challenge3():
    """Single-byte XOR cipher"""
    cipher_hex = "1b37373331363f78151b7f2b783431333d78397828372d363c78373e783a393b3736"
    ciphertext = bytes.fromhex(cipher_hex)
    score_data = english_like_score_data(ciphertext)
    best_data = nlargest(5, score_data, key=lambda x: x["score"])
    pp(best_data)
    print(best_data[0]["message"].decode())
    assert best_data[0]["message"] == b"Cooking MC's like a pound of bacon"


def challenge4():
    """Detect single-character XOR"""
    with open("4.txt") as f:
        ciphertexts = [bytes.fromhex(line.strip()) for line in f.readlines()]
    decoded_string_data = enumerate(best_english_like_score_data(c) for c in ciphertexts)
    best_decodings = nlargest(3, decoded_string_data, key=lambda d: d[1]["score"])
    pp(best_decodings)
    assert best_decodings[0][1]["message"] == b"Now that the party is jumping\n"


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
    def hamming_distance(bytes1, bytes2):
        return sum(bin(b1 ^ b2).count("1") for b1, b2 in zip(bytes1, bytes2))

    def index_of_coincidence(data, key_size):
        chunks = byte_chunks(data, key_size)
        result = 0
        for i in range(len(chunks) - 1):
            result += hamming_distance(chunks[i], chunks[i + 1])
        return result / key_size / len(chunks)

    assert hamming_distance(b"this is a test", b"wokka wokka!!!") == 37

    with open("6.txt") as f:
        ciphertext = base64.b64decode(f.read())

    best_key_size = min(range(2, 41), key=lambda x: index_of_coincidence(ciphertext, x))
    cipher_chunks = byte_chunks(ciphertext, best_key_size)
    plain_chunks, key = crack_common_xor_key(cipher_chunks)
    plaintext = b"".join(plain_chunks).decode()
    print("key: {}".format(key.decode()))
    print()
    print(plaintext)
    assert "white boy" in plaintext


def challenge7():
    """AES in ECB mode"""
    with open("7.txt") as f:
        ciphertext = base64.b64decode(f.read())
    message = AES.new(b"YELLOW SUBMARINE", AES.MODE_ECB).decrypt(ciphertext)
    print(message.decode())
    assert b"white boy" in message


def challenge8():
    """Detect AES in ECB mode"""
    with open("8.txt") as f:
        ciphertexts = [bytes.fromhex(line.strip()) for line in f.readlines()]
    ecb_texts = [(i, c) for i, c in enumerate(ciphertexts) if looks_like_ecb(c)]
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

    new_ciphertext = cbc_encrypt(key, iv, plain_bytes)
    assert new_ciphertext == AES.new(key, AES.MODE_CBC, iv).encrypt(plain_bytes)
    assert new_ciphertext == ciphertext


def challenge11():
    """An ECB/CBC detection oracle"""
    def encrypt_with_random_mode(plain_bytes):
        key = random_aes_key()
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
    cipher = AES.new(random_aes_key(), AES.MODE_ECB)

    def oracle_fn(attacker_bytes):
        return cipher.encrypt(pkcs7_pad(attacker_bytes + unknown_bytes))

    block_size = guess_block_size(oracle_fn)
    assert block_size == 16

    plaintext = crack_ecb_oracle(oracle_fn)
    print(plaintext.decode())
    assert plaintext == unknown_bytes


def challenge13():
    """ECB cut-and-paste"""
    cipher = AES.new(random_aes_key(), mode=AES.MODE_ECB)

    def encrypted_user_profile(email_address):
        profile_data = [("email", email_address), ("uid", "10"), ("role", "user")]
        return cipher.encrypt(pkcs7_pad(urlencode(profile_data).encode("utf-8")))

    def decrypt_profile(encrypted_profile):
        return pkcs7_unpad(cipher.decrypt(encrypted_profile)).decode()


    profile1 = encrypted_user_profile("peter.gregory@piedpiper.com")
    profile1_blocks = byte_chunks(profile1)

    profile2 = encrypted_user_profile("zach.woods@piedpiper.comadmin")
    profile2_blocks = byte_chunks(profile2)

    profile3 = encrypted_user_profile("a@a.com")
    padding_only_block = byte_chunks(profile3)[-1]

    new_profile = b"".join(profile1_blocks[:3]) + profile2_blocks[2] + padding_only_block
    decrypted_new_profile = decrypt_profile(new_profile)
    assert parse_qs(decrypted_new_profile)["role"] == ["admin"]
    print(decrypted_new_profile)
    # TODO: try to make a profile without duplicate uid params and "rol"
    # string at end


def challenge14():
    """Byte-at-a-time ECB decryption (Harder)"""
    cipher = AES.new(random_aes_key(), AES.MODE_ECB)
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
    key = random_aes_key()
    iv = os.urandom(16)

    cipher = AES.new(key, AES.MODE_CBC, iv)
    ciphertext = encrypted_query_string(cipher, "foo")

    new_ciphertext = bytearray(ciphertext)
    new_ciphertext[32:48] = xor_bytes(
        b"like%20a%20pound", b";admin=true;foo=", new_ciphertext[32:48])
    new_ciphertext = bytes(new_ciphertext)

    cipher = AES.new(key, AES.MODE_CBC, iv)
    assert b";admin=true;" in pkcs7_unpad(cipher.decrypt(new_ciphertext))


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

    key = random_aes_key()
    iv = os.urandom(16)

    def encrypt(unknown_string):
        return AES.new(key, AES.MODE_CBC, iv).encrypt(pkcs7_pad(unknown_string))

    def has_valid_padding(iv, ciphertext):
        plain_bytes = AES.new(key, AES.MODE_CBC, bytes(iv)).decrypt(ciphertext)
        try:
            pkcs7_unpad(plain_bytes)
        except ValueError:
            return False
        else:
            return True

    # The following code does a padding oracle attack. Details of how it
    # works can be found at
    # https://blog.skullsecurity.org/2013/padding-oracle-attacks-in-depth
    for unknown_string in unknown_strings:
        recovered_plaintext = bytearray()
        prev_cipher_block = iv
        for cipher_block in byte_chunks(encrypt(unknown_string)):
            recovered_block = bytes()
            for pos in reversed(range(16)):
                assert len(recovered_block) == 15 - pos
                cipher_slice = prev_cipher_block[pos + 1:]
                padding = bytes([len(recovered_block) + 1] * len(recovered_block))
                iv_end = xor_bytes(cipher_slice, padding, recovered_block)
                new_iv = bytearray(prev_cipher_block[:pos] + b"\x00" + iv_end)
                for i in range(256):
                    new_iv[pos] = prev_cipher_block[pos] ^ i ^ (16 - pos)
                    if has_valid_padding(new_iv, cipher_block):
                        if pos == 15:
                            new_iv[14] ^= 2
                            if not has_valid_padding(new_iv, cipher_block):
                                continue
                        recovered_block = bytes([i]) + recovered_block
                        break
            recovered_plaintext += recovered_block
            prev_cipher_block = cipher_block
        recovered_plaintext = pkcs7_unpad(recovered_plaintext)
        assert recovered_plaintext == unknown_string
        print(recovered_plaintext.decode())


def challenge18():
    """Implement CTR, the stream cipher mode"""
    ciphertext = base64.b64decode("L77na/nrFsKvynd6HzOoG7GHTLXsTVu9qvY/"
        "2syLXzhPweyyMTJULu/6/kXX0KSvoOLSFQ==")
    key = b"YELLOW SUBMARINE"
    ecb_cipher = AES.new(key, AES.MODE_ECB)
    nonce = 0

    plaintext = bytearray()
    for counter_value, block in zip(ctr_iterator(nonce), byte_chunks(ciphertext)):
        keystream = ecb_cipher.encrypt(counter_value)
        plaintext += xor_bytes(keystream[:len(block)], block)
    print(plaintext.decode())

    ctr_cipher = AES.new(key, AES.MODE_CTR, counter=ctr_counter(nonce))
    assert plaintext == ctr_cipher.decrypt(ciphertext)


def challenge19():
    """Break fixed-nonce CTR mode using substitions"""
    # [sic]. "substitions" looks like a typo but I don't know what it is
    # supposed to say.
    key = random_aes_key()

    def encrypt(ciphertext):
        cipher = AES.new(key, AES.MODE_CTR, counter=ctr_counter(0))
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
    print("\n".join(p.decode() for p in recovered_plaintexts))


def challenge20():
    """Break fixed-nonce CTR statistically"""
    key = random_aes_key()

    def encrypt(ciphertext):
        cipher = AES.new(key, AES.MODE_CTR, counter=ctr_counter(0))
        return cipher.encrypt(ciphertext)

    with open("20.txt") as f:
        plaintexts = [base64.b64decode(x) for x in f.readlines()]
    ciphertexts = [encrypt(x) for x in plaintexts]
    recovered_plaintexts, recovered_key = crack_common_xor_key(ciphertexts)
    print("\n".join(p.decode() for p in recovered_plaintexts))


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
    ciphertext_with_my_bytes = b"".join(cipher_chunks[-3:-1])
    keystream = xor_encrypt(ciphertext_with_my_bytes, b"A")
    keystream_numbers = struct.unpack(">LL", keystream)
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
    key = random_aes_key()
    nonce = random.getrandbits(64)

    def edit(ciphertext, block_index, new_bytes):
        if len(new_bytes) % 16 != 0:
            raise ValueError("new_bytes must be a multiple of 16 bytes long")
        cipher = AES.new(key, AES.MODE_CTR, counter=ctr_counter(nonce, block_index))
        new_ciphertext = cipher.encrypt(new_bytes)
        result = bytearray(ciphertext)
        result[16*block_index : 16*block_index + len(new_bytes)] = new_ciphertext
        return bytes(result)

    # 25.txt is identical to 7.txt
    with open("25.txt") as f:
        temp_bytes = base64.b64decode(f.read())
    plain_bytes = AES.new(b"YELLOW SUBMARINE", AES.MODE_ECB).decrypt(temp_bytes)
    cipher = AES.new(key, AES.MODE_CTR, counter=ctr_counter(nonce))
    ciphertext = cipher.encrypt(plain_bytes)

    keystream = edit(ciphertext, 0, bytes([0]) * len(plain_bytes))
    recovered_plaintext = xor_bytes(ciphertext, keystream)
    assert recovered_plaintext == plain_bytes


def challenge26():
    """CTR bitflipping"""
    key = random_aes_key()
    nonce = random.getrandbits(64)

    cipher = AES.new(key, AES.MODE_CTR, counter=ctr_counter(nonce))
    ciphertext = encrypted_query_string(cipher, "A" * 16)
    new_ciphertext = bytearray(ciphertext)
    new_ciphertext[32:48] = xor_bytes(
        b"A" * 16, b"ha_ha;admin=true", new_ciphertext[32:48])
    new_ciphertext = bytes(new_ciphertext)

    cipher = AES.new(key, AES.MODE_CTR, counter=ctr_counter(nonce))
    assert b";admin=true;" in pkcs7_unpad(cipher.decrypt(new_ciphertext))


def challenge27():
    """Recover the key from CBC with IV=Key"""
    key = random_aes_key()
    iv = key

    def encrypt(user_bytes):
        return AES.new(key, AES.MODE_CBC, iv).encrypt(pkcs7_pad(user_bytes))

    def decrypt(ciphertext):
        plain_bytes = AES.new(key, AES.MODE_CBC, iv).decrypt(ciphertext)
        return pkcs7_unpad(plain_bytes.decode("ascii"))

    ciphertext = encrypt(EXAMPLE_PLAIN_BYTES)
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
    key = os.urandom(16)
    assert sha1(key + b"message1").digest() != sha1(key + b"message2").digest()


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
    mac = sha1(key + query_string).digest()

    glue_padding = sha1_padding(len(key + query_string))
    new_param = b";admin=true"
    modified_hash_fn = Sha1Hash(
        prefix_hash=mac,
        prefix_length=len(key + query_string + glue_padding))
    new_hash = modified_hash_fn.update(new_param).digest()

    expected_hash = sha1(key + query_string + glue_padding + new_param).digest()
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
    key = os.urandom(16)
    with open("hamlet.txt", "rb") as f:
        data = f.read()
    hmac = get_hmac(key, data)

    print("looking for {}".format(list(hmac)))
    print()
    server = FancyHTTPServer(("localhost", 31415), ValidatingRequestHandler)
    server.hmac_key = key
    server.validate_signature = lambda hmac, sig: insecure_compare(hmac, sig, 0.05)
    try:
        Thread(target=server.serve_forever).start()
        print("Server is running on {}".format(server.server_address))
        print()
        signature = recover_signature(
            server_approves_of_signature,
            thread_count=20,
            threshold=0.02,
            attempt_limit=20)
        print("recovered signature: {}".format(list(signature)))
    finally:
        server.shutdown()
        server.server_close()

    assert signature == hmac


def challenge32():
    """Break HMAC-SHA1 with a slightly less artificial timing leak"""
    key = os.urandom(16)
    with open("hamlet.txt", "rb") as f:
        data = f.read()
    hmac = get_hmac(key, data)

    print("looking for {}".format(list(hmac)))
    print()
    server = FancyHTTPServer(("localhost", 31415), ValidatingRequestHandler)
    server.hmac_key = key
    server.validate_signature = lambda hmac, sig: insecure_compare(hmac, sig, 0.025)
    try:
        Thread(target=server.serve_forever).start()
        print("Server is running on {}".format(server.server_address))
        print()
        signature = recover_signature(
            server_approves_of_signature,
            thread_count=15,
            threshold=0.006,
            attempt_limit=20)
        print("recovered signature: {}".format(list(signature)))
    finally:
        server.shutdown()
        server.server_close()

    assert signature == hmac


def challenge33():
    """Implement Diffie-Hellman"""
    alice = DiffieHellmanUser(p=37, g=5)
    bob = DiffieHellmanUser(p=37, g=5)
    assert alice.get_shared_key_for(bob) == bob.get_shared_key_for(alice)

    alice = DiffieHellmanUser()
    bob = DiffieHellmanUser()
    assert alice.get_shared_key_for(bob) == bob.get_shared_key_for(alice)


def challenge34():
    """Implement a MITM key-fixing attack on Diffie-Hellman with parameter injection"""
    alice = DiffieHellmanUser()
    bob = DiffieHellmanUser()
    alice.send_echo_request(bob, EXAMPLE_PLAIN_BYTES)
    assert EXAMPLE_PLAIN_BYTES in bob._decrypted_messages[alice]

    alice = DiffieHellmanUser()
    bob = DiffieHellmanUser()
    mallory = DiffieHellmanUser()
    mallory.public_key = mallory.p
    assert alice.get_shared_key_for(mallory) == 0
    mallory._shared_keys[alice] = 0
    assert bob.get_shared_key_for(mallory) == 0
    mallory._shared_keys[bob] = 0
    alice.send_echo_request(mallory, EXAMPLE_PLAIN_BYTES)
    # Mallory decrypts request without real key.
    assert EXAMPLE_PLAIN_BYTES in mallory._decrypted_messages[alice]
    mallory.send_echo_request(bob, EXAMPLE_PLAIN_BYTES)
    assert EXAMPLE_PLAIN_BYTES in bob._decrypted_messages[mallory]


def challenge35():
    """Implement DH with negotiated groups, and break with malicious "g" parameters"""
    # Mallory tricks Alice and Bob into using g=1
    alice = DiffieHellmanUser(g=1)
    bob = DiffieHellmanUser(g=1)
    mallory = DiffieHellmanUser(g=1)
    assert mallory.public_key == 1
    assert alice.get_shared_key_for(mallory) == 1
    assert bob.get_shared_key_for(mallory) == 1
    alice.send_echo_request(mallory, EXAMPLE_PLAIN_BYTES)
    # Mallory decrypts request without real key.
    assert EXAMPLE_PLAIN_BYTES in mallory._decrypted_messages[alice]
    mallory.send_echo_request(bob, EXAMPLE_PLAIN_BYTES)
    assert EXAMPLE_PLAIN_BYTES in bob._decrypted_messages[mallory]

    # Mallory tricks Alice and Bob into using g=IETF_DIFFIE_HELLMAN_PRIME
    alice = DiffieHellmanUser(g=IETF_DIFFIE_HELLMAN_PRIME)
    bob = DiffieHellmanUser(g=IETF_DIFFIE_HELLMAN_PRIME)
    mallory = DiffieHellmanUser(g=IETF_DIFFIE_HELLMAN_PRIME)
    assert mallory.public_key == 0
    assert alice.get_shared_key_for(mallory) == 0
    assert bob.get_shared_key_for(mallory) == 0
    alice.send_echo_request(mallory, EXAMPLE_PLAIN_BYTES)
    # Mallory decrypts request without real key.
    assert EXAMPLE_PLAIN_BYTES in mallory._decrypted_messages[alice]
    mallory.send_echo_request(bob, EXAMPLE_PLAIN_BYTES)
    assert EXAMPLE_PLAIN_BYTES in bob._decrypted_messages[mallory]

    # Mallory tricks Alice and Bob into using g=IETF_DIFFIE_HELLMAN_PRIME - 1
    alice = DiffieHellmanUser(g=IETF_DIFFIE_HELLMAN_PRIME - 1)
    bob = DiffieHellmanUser(g=IETF_DIFFIE_HELLMAN_PRIME - 1)
    # Private key must be even.
    mallory = DiffieHellmanUser(g=IETF_DIFFIE_HELLMAN_PRIME - 1,
        private_key=random.randrange(0, IETF_DIFFIE_HELLMAN_PRIME, 2))
    assert mallory.public_key == 1
    assert alice.get_shared_key_for(mallory) == 1
    assert bob.get_shared_key_for(mallory) == 1
    alice.send_echo_request(mallory, EXAMPLE_PLAIN_BYTES)
    # Mallory decrypts request without real key.
    assert EXAMPLE_PLAIN_BYTES in mallory._decrypted_messages[alice]
    mallory.send_echo_request(bob, EXAMPLE_PLAIN_BYTES)
    assert EXAMPLE_PLAIN_BYTES in bob._decrypted_messages[mallory]


def challenge36():
    """Implement Secure Remote Password (SRP)"""
    username = "peter.gregory@piedpiper.com"
    password = "letmein"
    wrong_password = "qwerty"

    server = SRPServer()
    client = SRPClient()
    client.sign_up(server, username, password)

    assert client.log_in(server, username, password)
    assert not client.log_in(server, username, wrong_password)


def challenge37():
    """Break SRP with a zero key"""
    username = "peter.gregory@piedpiper.com"
    password = "letmein"

    server = SRPServer()
    client = SRPClient()
    client.sign_up(server, username, password)

    for i in range(10):
        # Attacker tricks server into computing easily derivable session key
        salt, _, _ = server._respond_to_login_request(username, i * client.N)
        # Attacker derives shared session key without password
        shared_session_key = sha256(int_to_bytes(0)).digest()
        hmac = get_hmac(shared_session_key, salt, sha256)
        # Attacker logs in without password
        assert server._verify_hmac(hmac, username)


def challenge38():
    """Offline dictionary attack on simplified SRP"""
    username = "peter.gregory@piedpiper.com"
    password = "letmein"
    wrong_password = "qwerty"

    server = SRPServer()
    client = SRPClient()
    client.sign_up(server, username, password)
    assert client.log_in(server, username, password, k=0)
    assert not client.log_in(server, username, wrong_password, k=0)

    server = SRPServer()
    mallory_server = MitmSRPServer(server)
    client.sign_up(server, username, password)
    login_is_valid = client.log_in(mallory_server, username, password, k=0)
    assert login_is_valid
    assert mallory_server.users[username]["password"] == password


def challenge39():
    """Implement RSA"""
    assert invmod(17, 3120) == 2753

    public_exponent = 3  # called "e" in challenge
    while True:
        p = getStrongPrime(512)
        q = getStrongPrime(512)
        n = p * q
        totient = (p - 1) * (q - 1)  # called "et" in challenge
        assert totient > public_exponent
        if gcd(public_exponent, totient) == 1:
            break

    private_exponent = invmod(public_exponent, totient)  # called "d" in challenge
    assert (public_exponent * private_exponent) % totient == 1
    message = int.from_bytes(EXAMPLE_PLAIN_BYTES, byteorder="big")
    assert message < n
    ciphertext = pow(message, public_exponent, n)
    plaintext = pow(ciphertext, private_exponent, n)
    assert plaintext == message


def test_all_challenges(output_stream=sys.stdout):
    challenges = {}
    for name, var in globals().items():
        try:
            num = int(re.findall("^challenge(\d+)$", name)[0])
        except IndexError:
            pass
        else:
            if callable(var):
                challenges[num] = var
    for num in sorted(challenges):
        print("Running challenge {}: {}".format(num, challenges[num].__doc__),
            file=output_stream)
        try:
            challenges[num]()
        except Exception as e:
            traceback.print_exc(file=output_stream)
        else:
            print("Challenge {} passed.".format(num), file=output_stream)


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
