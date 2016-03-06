#!/usr/bin/env python3

import Crypto.Util.Counter
import argparse
import base64
import cProfile
import os
import pprint
import re
import struct
import sys

from Crypto.Cipher import AES
from collections import Counter, defaultdict
from contextlib import redirect_stdout
from fractions import gcd
from itertools import cycle, zip_longest
from random import SystemRandom
from urllib.parse import parse_qs, quote as url_quote, urlencode

random = SystemRandom()

ALL_BYTES = [bytes([i]) for i in range(256)]


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


def english_like_score(text):
    # Character frequencies taken from raw letter averages at
    # http://www.macfreek.nl/memory/Letter_Distribution, then rounded to 6
    # decimal places for readability.
    frequencies = {
        " ": 0.183169, "a": 0.065531, "b": 0.012708, "c": 0.022651, "d": 0.033523,
        "e": 0.102179, "f": 0.019718, "g": 0.016359, "h": 0.048622, "i": 0.057343,
        "j": 0.001144, "k": 0.005692, "l": 0.033562, "m": 0.020173, "n": 0.057031,
        "o": 0.062006, "p": 0.015031, "q": 0.000881, "r": 0.049720, "s": 0.053263,
        "t": 0.075100, "u": 0.022952, "v": 0.007880, "w": 0.016896, "x": 0.001498,
        "y": 0.014700, "z": 0.000598,
        "\ufffd": 1e-6 # Unicode replacement character
    }
    # Use defaultdict instead of Counter because Counter is slow
    char_counts = defaultdict(int)
    for char in text.lower():
        char_counts[char] += 1
    text_length = len(text)
    chi_squared = 0
    for char, char_count in char_counts.items():
        # Number 5.4e-4 was empirically observed to produce the best ratio of
        # score for English text to score for incorrectly decrypted text.
        expected = text_length * frequencies.get(char, 5.4e-4)
        difference = char_count - expected
        chi_squared += difference * difference / expected
    return 1e6 / chi_squared / text_length


def all_english_like_scores_data(cipher_bytes):
    result = []
    for key in ALL_BYTES:
        message = bytes_to_string(xor_encrypt(cipher_bytes, key))
        score = english_like_score(message)
        result.append({
            "key": list(key),
            "key_binary": ["{:08b}".format(b) for b in key],
            "message": message,
            "original": cipher_bytes,
            "score": score})
    return result


def best_english_like_score_data(text):
    return sorted(all_english_like_scores_data(text),
                  key=lambda m: m["score"],
                  reverse=True)


def looks_like_ecb(cipher_bytes):
    # TODO: use birthday paradox to calculate an estimate for the expected
    # number of duplicate blocks so this function works on big ciphertexts.
    chunk_counter = Counter(byte_chunks(cipher_bytes))
    return chunk_counter.most_common(1)[0][1] > 1


def pkcs7_pad(input_bytes, block_size=16):
    padding_length = -len(input_bytes) % block_size
    if padding_length == 0:
        padding_length = block_size
    return input_bytes + bytes([padding_length] * padding_length)


def pkcs7_unpad(cipher_bytes, block_size=16):
    padding_length = cipher_bytes[-1]
    expected_padding = bytes([padding_length]) * padding_length
    padding = cipher_bytes[-padding_length:]
    if padding_length > block_size or padding != expected_padding:
        raise ValueError("Invalid padding")
    return cipher_bytes[:-padding_length]


def cbc_encrypt(key, iv, plain_bytes):
    cipher = AES.new(key, AES.MODE_ECB, iv)
    last_cipher_chunk = iv
    result = bytearray()
    for plain_chunk in byte_chunks(plain_bytes):
        combined_chunk = xor_bytes(last_cipher_chunk, plain_chunk)
        cipher_chunk = cipher.encrypt(combined_chunk)
        result.extend(cipher_chunk)
        last_cipher_chunk = cipher_chunk
    return bytes(result)


def cbc_decrypt(key, iv, cipher_bytes):
    cipher = AES.new(key, AES.MODE_ECB, iv)
    last_cipher_chunk = iv
    result = bytearray()
    for cipher_chunk in byte_chunks(cipher_bytes):
        decrypted_chunk = cipher.decrypt(cipher_chunk)
        plain_chunk = xor_bytes(last_cipher_chunk, decrypted_chunk)
        result.extend(plain_chunk)
        last_cipher_chunk = cipher_chunk
    return bytes(result)


def create_random_aes_key():
    return os.urandom(16)


def appears_to_produce_ecb(oracle_fn):
    return any(looks_like_ecb(oracle_fn(b"A" * i)) for i in range(1000))


def guess_block_size(oracle_fn):
    seen_sizes = set()
    for plaintext_size in range(33):
        cipher_bytes = oracle_fn(os.urandom(plaintext_size))
        seen_sizes.add(len(cipher_bytes))
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
        for test_byte in ALL_BYTES:
            test_input = short_input_block + result + test_byte
            output = oracle_fn(test_input)
            telltale_chunk = byte_chunks(output)[block_index]
            if telltale_chunk == block_to_look_for:
                result += test_byte
                break
        else:  # if no byte matches
            return pkcs7_unpad(result)


def create_ctr_counter(nonce):
    return Crypto.Util.Counter.new(
        nbits=64, prefix=struct.pack("<Q", nonce), initial_value=0, little_endian=True)


def challenge1():
    """Convert hex to base64"""
    def hex_to_base64(hex_string):
        return base64.b64encode(bytes.fromhex(hex_string))

    cipher_hex = ("49276d206b696c6c696e6720796f757220627261696e206c" +
        "696b65206120706f69736f6e6f7573206d757368726f6f6d")
    result = hex_to_base64(cipher_hex)
    assert result == b"SSdtIGtpbGxpbmcgeW91ciBicmFpbiBsaWtlIGEgcG9pc29ub3VzIG11c2hyb29t"
    print(bytes_to_string(result))


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
    best_data = best_english_like_score_data(ciphertext)[:5]
    pp(best_data)
    print(best_data[0]["message"])
    assert best_data[0]["message"] == "Cooking MC's like a pound of bacon"


def challenge4():
    """Detect single-character XOR"""
    cipher_hexes = [line.rstrip() for line in open("4.txt").readlines()]
    decoded_string_data = []
    for i, string in enumerate(cipher_hexes):
        cipher_bytes = bytes.fromhex(string)
        decoded_string_data.append(best_english_like_score_data(cipher_bytes)[0])
        decoded_string_data[-1]["index"] = i
    best_decodings = sorted(decoded_string_data, key=lambda d: d["score"], reverse=True)
    result = best_decodings[:3]
    pp(result)
    assert best_decodings[0]["message"] == "Now that the party is jumping\n"


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
    cipher_bytes = base64.b64decode(open("6.txt").read())
    edit_distances = defaultdict(int)
    for key_size in range(2, 41):
        chunks = byte_chunks(cipher_bytes, key_size)
        for i in range(10):
            edit_distances[key_size] += edit_distance(chunks[i], chunks[i + 1])
        edit_distances[key_size] /= key_size
    best_key_size = min(edit_distances, key=lambda key_size: edit_distances[key_size])

    chunks = byte_chunks(cipher_bytes, best_key_size)
    transposed_messages = []
    key = bytearray()
    for i in range(best_key_size):
        transposed_block = bytes(chunk[i] for chunk in chunks if i < len(chunk))
        score_data = best_english_like_score_data(transposed_block)[0]
        transposed_messages.append(score_data["message"])
        key.extend(score_data["key"])
    print(key)
    print()
    plaintext = []
    for message in zip_longest(*transposed_messages):
        plaintext.append("".join(char for char in message if char is not None))
    plaintext = "".join(plaintext)
    print(plaintext)
    assert "white boy" in plaintext


def challenge7():
    """AES in ECB mode"""
    cipher_bytes = base64.b64decode(open("7.txt").read())
    message = AES.new("YELLOW SUBMARINE", AES.MODE_ECB).decrypt(cipher_bytes)
    print(bytes_to_string(message))
    assert b"white boy" in message


def challenge8():
    """Detect AES in ECB mode"""
    ecb_texts = []
    for i, line in enumerate(open("8.txt").readlines()):
        cipher_bytes = bytes.fromhex(line.strip())
        if looks_like_ecb(cipher_bytes):
            ecb_texts.append({"index": i, "ciphertext": cipher_bytes})
    pp(ecb_texts)
    assert len(ecb_texts) == 1


def challenge9():
    """Implement PKCS#7 padding"""
    assert pkcs7_pad(b"YELLOW SUBMARINE", 20) == b"YELLOW SUBMARINE\x04\x04\x04\x04"


def challenge10():
    """Implement CBC mode"""
    cipher_bytes = base64.b64decode(open("10.txt").read())
    key = b"YELLOW SUBMARINE"
    iv = bytes([0] * 16)

    plain_bytes = cbc_decrypt(key, iv, cipher_bytes)
    assert b"white boy" in plain_bytes
    assert plain_bytes == AES.new(key, AES.MODE_CBC, iv).decrypt(cipher_bytes)

    # Create new cipher object because using cipher object messes up
    # internal IV state.
    new_cipher_bytes = cbc_encrypt(key, iv, plain_bytes)
    assert new_cipher_bytes == AES.new(key, AES.MODE_CBC, iv).encrypt(plain_bytes)
    assert new_cipher_bytes == cipher_bytes


def challenge11():
    """An ECB/CBC detection oracle"""
    def encrypt_with_random_key_and_random_mode(plain_bytes):
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
    plain_bytes = open("hamlet.txt", "rb").read(3000)
    results = Counter()
    for i in range(1000):
        cipher_bytes, mode_number = encrypt_with_random_key_and_random_mode(plain_bytes)
        mode = {1: "ECB", 2: "CBC"}[mode_number]
        apparent_mode = "ECB" if looks_like_ecb(cipher_bytes) else "CBC"
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
    profile1_chunks = byte_chunks(profile1)

    profile2 = create_encrypted_user_profile("zach.woods@piedpiper.comadmin")
    profile2_chunks = byte_chunks(profile2)

    profile3 = create_encrypted_user_profile("a@a.com")
    padding_only_chunk = byte_chunks(profile3)[-1]

    new_profile = b"".join(profile1_chunks[:3]) + profile2_chunks[2] + padding_only_chunk
    decrypted_new_profile = decrypt_profile(new_profile)
    assert parse_qs(decrypted_new_profile)["role"] == ["admin"]
    print(decrypted_new_profile)
    # TODO: try to make a profile without duplicate uid params and "rol"
    # string at end


def challenge14():
    """Byte-at-a-time ECB decryption (Harder)"""
    cipher = AES.new(create_random_aes_key(), AES.MODE_ECB)
    random_bytes = os.urandom(random.randint(0, 64))
    target_bytes = (b"Give a man a beer, he'll waste an hour. "
        b"Teach a man to brew, he'll waste a lifetime.")

    def oracle_fn(attacker_bytes):
        return cipher.encrypt(pkcs7_pad(random_bytes + attacker_bytes + target_bytes))

    assert appears_to_produce_ecb(oracle_fn)
    block_size = guess_block_size(oracle_fn)
    assert block_size == 16

    chunks = byte_chunks(oracle_fn(b"A" * 3*block_size))
    attacker_block, attacker_block_count = Counter(chunks).most_common(1)[0]
    assert attacker_block_count >= 2
    attacker_block_pos = block_size * chunks.index(attacker_block)
    for i in range(block_size):
        chunks = byte_chunks(oracle_fn(b"A" * (3*block_size - i - 1)))
        if Counter(chunks)[attacker_block] < attacker_block_count:
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

    def create_encrypted_string(user_data):
        cipher = AES.new(key, AES.MODE_CBC, iv)
        query_string = ("comment1=cooking%20MCs;userdata=" + url_quote(user_data) +
            ";comment2=%20like%20a%20pound%20of%20bacon")
        bytes_to_encrypt = pkcs7_pad(query_string.encode("utf-8"))
        return cipher.encrypt(bytes_to_encrypt)

    def encrypted_string_has_admin(cipher_bytes):
        # Create new cipher object because internal IV state in old one gets
        # messed up after being used.
        cipher = AES.new(key, AES.MODE_CBC, iv)
        plain_bytes = pkcs7_unpad(cipher.decrypt(cipher_bytes))
        return b";admin=true;" in plain_bytes

    cipher_bytes = create_encrypted_string("foo")
    bits_to_flip = (bytes([0] * 32) +
        xor_bytes(b"like%20a%20pound", b";admin=true;foo=") + bytes([0] * 32))
    modified_cipher_bytes = xor_bytes(cipher_bytes, bits_to_flip)
    assert encrypted_string_has_admin(modified_cipher_bytes)


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

    def has_valid_padding(iv, cipher_bytes):
        cipher = AES.new(key, AES.MODE_CBC, iv)
        plain_bytes = cipher.decrypt(cipher_bytes)
        try:
            pkcs7_unpad(plain_bytes)
        except ValueError:
            return False
        else:
            return True

    key = create_random_aes_key()
    iv = os.urandom(16)

    for unknown_string in unknown_strings:
        cipher_bytes = create_encrypted_string(unknown_string)
        recovered_plaintext = bytearray()
        prev_cipher_block = iv
        for cipher_block in byte_chunks(cipher_bytes):
            recovered_block = bytes()
            for pos in reversed(range(16)):
                assert len(recovered_block) == 15 - pos
                cipher_slice = prev_cipher_block[pos + 1:]
                padding = bytes([len(recovered_block) + 1] * len(recovered_block))
                iv_end = xor_bytes(cipher_slice, padding, recovered_block)
                new_iv = bytearray(prev_cipher_block[:pos] + b"\x00" + iv_end)
                for guess in ALL_BYTES:
                    new_iv[pos] = prev_cipher_block[pos] ^ guess[0] ^ (16 - pos)
                    if has_valid_padding(bytes(new_iv), cipher_block):
                        if not recovered_block:
                            new_iv[14] ^= 2
                            if not has_valid_padding(bytes(new_iv), cipher_block):
                                # Last byte of cipher_block appears to have \x01 for
                                # padding, but this is wrong.
                                # See https://blog.skullsecurity.org/2013/padding-oracle-attacks-in-depth
                                continue
                        recovered_block = guess + recovered_block
                        break
            recovered_plaintext += recovered_block
            prev_cipher_block = cipher_block
        recovered_plaintext = pkcs7_unpad(recovered_plaintext)
        assert recovered_plaintext == unknown_string
        print(bytes_to_string(recovered_plaintext))


def challenge18():
    """Implement CTR, the stream cipher mode"""
    cipher_bytes = base64.b64decode("L77na/nrFsKvynd6HzOoG7GHTLXsTVu9qvY/"
        "2syLXzhPweyyMTJULu/6/kXX0KSvoOLSFQ==")
    key = b"YELLOW SUBMARINE"
    ecb_cipher = AES.new(key, AES.MODE_ECB)
    nonce = 0

    plaintext = bytearray()
    for block_index, chunk in enumerate(byte_chunks(cipher_bytes), start=nonce):
        # Encode nonce and block_index as 64-bit little-endian integers
        counter_value = struct.pack("<QQ", nonce, block_index)
        keystream = ecb_cipher.encrypt(counter_value)
        plaintext += xor_bytes(keystream[:len(chunk)], chunk)
    print(bytes_to_string(plaintext))

    ctr_cipher = AES.new(key, AES.MODE_CTR, counter=create_ctr_counter(nonce))
    assert plaintext == ctr_cipher.decrypt(cipher_bytes)


def test_all_challenges(stdout=sys.stdout):
    # Pass sys.stdout when this function is created so "running challenge"
    # output shows even if stdout is redirected.
    challenges = {}
    for name, var in globals().copy().items():
        try:
            num = int(re.findall("challenge(\d+)", name)[0])
        except (IndexError, ValueError):
            pass
        else:
            if callable(var):
                challenges[num] = var
    for num in sorted(challenges):
        print("running challenge {}".format(num), file=stdout)
        challenges[num]()


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
        func = test_all_challenges
    with redirect_stdout(open(os.devnull, "w") if args.quiet else sys.stdout):
        if args.profile:
            profile = cProfile.Profile()
            profile.runcall(func)
        else:
            func()
    if args.profile:
        profile.print_stats(sort="cumtime")
