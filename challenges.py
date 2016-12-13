#!/usr/bin/env python3

# standard library modules
import base64
import cProfile
import functools
import gzip
import hashlib
import inspect
import itertools
import os
import pprint as pprint_module
import re
import string
import struct
import sys
import traceback
import warnings

from argparse import ArgumentParser
from collections import Counter, defaultdict
from contextlib import redirect_stdout
from hashlib import sha1, sha256
from heapq import nlargest
from math import ceil, gcd
from threading import Thread
from time import time
from urllib.parse import parse_qs, quote as url_quote, urlencode


# third-party modules
from Cryptodome.Cipher import ARC4
from md4 import MD4


# modules in this project
import block_tools
import diffie_hellman
import dsa
import english
import merkle_damgard
import mersenne_twister
import rsa
import sha1.sha1 as pure_python_sha1
import srp
import timing_attack
import util

random = util.random


warnings.simplefilter("default", BytesWarning)
warnings.simplefilter("default", ResourceWarning)
warnings.simplefilter("default", DeprecationWarning)

EXAMPLE_PLAIN_BYTES = (b"Give a man a beer, he'll waste an hour. "
                       b"Teach a man to brew, he'll waste a lifetime.")


def pprint(*args, width=120, **kwargs):
    pprint_module.pprint(*args, width=width, **kwargs)


def make_user_query_string(user_data):
    return ("comment1=cooking%20MCs;userdata=" + url_quote(user_data) +
            ";comment2=%20like%20a%20pound%20of%20bacon").encode()


def challenge1():
    """Convert hex to base64"""
    encoded_text = ("49276d206b696c6c696e6720796f757220627261696e206c696b65206120706f6973"
                    "6f6e6f7573206d757368726f6f6d")
    message = bytes.fromhex(encoded_text)
    print(message.decode())
    result = base64.b64encode(message)

    assert result == b"SSdtIGtpbGxpbmcgeW91ciBicmFpbiBsaWtlIGEgcG9pc29ub3VzIG11c2hyb29t"


def challenge2():
    """Fixed XOR"""
    output = util.xor_bytes(
        bytes.fromhex("1c0111001f010100061a024b53535009181c"),
        bytes.fromhex("686974207468652062756c6c277320657965"))
    assert output == b"the kid don't play"
    print(output.decode())
    print(output.hex())


def challenge3():
    """Single-byte XOR cipher"""
    cipher_hex = "1b37373331363f78151b7f2b783431333d78397828372d363c78373e783a393b3736"
    ciphertext = bytes.fromhex(cipher_hex)
    score_data = (english.xor_score_data(ciphertext, bytes([i])) for i in range(256))
    best_data = nlargest(5, score_data, key=lambda x: x["score"])
    pprint(best_data)
    print(best_data[0]["message"].decode())
    assert best_data[0]["message"] == b"Cooking MC's like a pound of bacon"


def challenge4():
    """Detect single-character XOR"""
    with open("text_files/4.txt") as f:
        ciphertexts = [bytes.fromhex(line.strip()) for line in f.readlines()]
    decoded_string_data = enumerate(english.best_byte_xor_score_data(c)
                                    for c in ciphertexts)
    best_decodings = nlargest(3, decoded_string_data, key=lambda d: d[1]["score"])
    pprint(best_decodings)
    assert best_decodings[0][1]["message"] == b"Now that the party is jumping\n"


def challenge5():
    """Implement repeating-key XOR"""
    stanza = ("Burning 'em, if you ain't quick and nimble\n"
              "I go crazy when I hear a cymbal")
    result = util.apply_repeating_xor_key(stanza.encode(), b"ICE").hex()
    assert result == ("0b3637272a2b2e63622c2e69692a23693a2a3c6324202d623d63343c2a26226324"
                      "272765272a282b2f20430a652e2c652a3124333a653e2b2027630c692b20283165"
                      "286326302e27282f")
    print(result)


def challenge6():
    """Break repeating-key XOR"""
    def bit_hamming_distance(bytes1, bytes2):
        return sum(bin(b1 ^ b2).count("1") for b1, b2 in zip(bytes1, bytes2))

    def index_of_coincidence(data, key_size):
        # This function is equivalent to the normalized edit distance approach
        # mentioned in the challenge, but simpler.
        return bit_hamming_distance(data[:-key_size], data[key_size:])

    assert bit_hamming_distance(b"this is a test", b"wokka wokka!!!") == 37

    with open("text_files/6.txt") as f:
        ciphertext = base64.b64decode(f.read())

    best_key_size = min(range(2, 41), key=lambda x: index_of_coincidence(ciphertext, x))
    key = english.crack_common_xor_key(util.chunks(ciphertext, best_key_size))
    plaintext = util.apply_repeating_xor_key(ciphertext, key).decode()
    print("key: {}".format(key.decode()))
    print()
    print(plaintext)
    assert "white boy" in plaintext


def challenge7():
    """AES in ECB mode"""
    with open("text_files/7.txt") as f:
        ciphertext = base64.b64decode(f.read())
    message = block_tools.aes_decrypt(ciphertext, key=b"YELLOW SUBMARINE", mode="ECB")
    print(message.decode())
    assert b"white boy" in message


def challenge8():
    """Detect AES in ECB mode"""
    with open("text_files/8.txt") as f:
        ciphertexts = [bytes.fromhex(line.strip()) for line in f.readlines()]
    ecb_texts = []
    for i, ciphertext in enumerate(ciphertexts, start=1):
        if block_tools.looks_like_ecb(ciphertext):
            ecb_texts.append(ciphertext)
            print("ECB-like ciphertext found on line {}".format(i))
            pprint([util.pretty_hex_bytes(x) for x in util.chunks(ciphertext)])
    assert len(ecb_texts) == 1


def challenge9():
    """Implement PKCS#7 padding"""
    assert (block_tools.pkcs7_pad(b"YELLOW SUBMARINE", 20) ==
            b"YELLOW SUBMARINE\x04\x04\x04\x04")


def challenge10():
    """Implement CBC mode"""
    def cbc_encrypt(key, iv, plain_bytes):
        result = bytearray()
        prev_cipher_block = iv
        for plain_block in util.chunks(plain_bytes):
            combined_block = util.xor_bytes(prev_cipher_block, plain_block)
            cipher_block = block_tools.aes_encrypt(combined_block, key, "ECB")
            result.extend(cipher_block)
            prev_cipher_block = cipher_block
        return bytes(result)

    def cbc_decrypt(key, iv, ciphertext):
        result = bytearray()
        prev_cipher_block = iv
        for cipher_block in util.chunks(ciphertext):
            decrypted_block = block_tools.aes_decrypt(cipher_block, key, "ECB")
            plain_block = util.xor_bytes(prev_cipher_block, decrypted_block)
            result.extend(plain_block)
            prev_cipher_block = cipher_block
        return bytes(result)

    with open("text_files/10.txt") as f:
        ciphertext = base64.b64decode(f.read())
    key = b"YELLOW SUBMARINE"
    iv = b"\x00" * 16

    plain_bytes = cbc_decrypt(key, iv, ciphertext)
    assert b"white boy" in plain_bytes
    assert plain_bytes == block_tools.aes_decrypt(ciphertext, key, "CBC", iv)

    new_ciphertext = cbc_encrypt(key, iv, plain_bytes)
    assert new_ciphertext == block_tools.aes_encrypt(plain_bytes, key, "CBC", iv)
    assert new_ciphertext == ciphertext


def challenge11():
    """An ECB/CBC detection oracle"""
    def encrypt_with_random_mode(plain_bytes):
        settings = {
            "key": block_tools.random_aes_key(),
            "mode": random.choice(["CBC", "ECB"]),
            "pad": True,
        }
        prefix = os.urandom(random.randint(5, 10))
        suffix = os.urandom(random.randint(5, 10))
        cipher_input = prefix + plain_bytes + suffix
        if settings["mode"] == "CBC":
            settings["iv"] = os.urandom(16)
        return (block_tools.aes_encrypt(cipher_input, **settings), settings["mode"])

    # hamlet.txt from http://erdani.com/tdpl/hamlet.txt
    # This seems to work perfectly when encrypting 2923 or more bytes of
    # hamlet.txt, but frequently guesses incorrectly with 2922 bytes or
    # fewer. Different files produce different results but for any given
    # file, there seems to be a precise amount of data at which this
    # function works reliably, and below which it frequently thinks ECB is
    # CBC.
    with open("text_files/hamlet.txt", "rb") as f:
        plain_bytes = f.read(3000)
    for _ in range(1000):
        ciphertext, mode = encrypt_with_random_mode(plain_bytes)
        assert mode == "ECB" if block_tools.looks_like_ecb(ciphertext) else "CBC"


def challenge12():
    """Byte-at-a-time ECB decryption (Simple)"""
    unknown_bytes = base64.b64decode(
        "Um9sbGluJyBpbiBteSA1LjAKV2l0aCBteSByYWctdG9wIGRvd24gc28gbXkgaGFpciBjYW"
        "4gYmxvdwpUaGUgZ2lybGllcyBvbiBzdGFuZGJ5IHdhdmluZyBqdXN0IHRvIHNheSBoaQpE"
        "aWQgeW91IHN0b3A/IE5vLCBJIGp1c3QgZHJvdmUgYnkK")
    key = block_tools.random_aes_key()

    def oracle_fn(attacker_bytes):
        plaintext = attacker_bytes + unknown_bytes
        return block_tools.aes_encrypt(plaintext, key, "ECB", pad=True)

    plaintext = block_tools.crack_ecb_oracle(oracle_fn)
    print(plaintext.decode())
    assert plaintext == unknown_bytes


def challenge13():
    """ECB cut-and-paste"""
    key = block_tools.random_aes_key()

    def encrypted_user_profile(email_address):
        profile_data = [("email", email_address), ("uid", "10"), ("role", "user")]
        profile = urlencode(profile_data).encode()
        return block_tools.aes_encrypt(profile, key, "ECB", pad=True)

    def decrypt_profile(encrypted_profile):
        profile = block_tools.aes_decrypt(encrypted_profile, key, "ECB", unpad=True)
        return profile.decode()

    profile1 = encrypted_user_profile("peter.gregory@piedpiper.com")
    profile1_blocks = util.chunks(profile1)

    profile2 = encrypted_user_profile("zach.woods@piedpiper.comadmin")
    profile2_blocks = util.chunks(profile2)

    profile3 = encrypted_user_profile("a@a.com")
    padding_only_block = util.chunks(profile3)[-1]

    new_profile = b"".join(profile1_blocks[:3]) + profile2_blocks[2] + padding_only_block
    decrypted_new_profile = decrypt_profile(new_profile)
    assert parse_qs(decrypted_new_profile)["role"] == ["admin"]
    print(decrypted_new_profile)


def challenge14():
    """Byte-at-a-time ECB decryption (Harder)"""
    key = block_tools.random_aes_key()
    random_bytes = os.urandom(random.randint(0, 64))
    target_bytes = EXAMPLE_PLAIN_BYTES

    def oracle_fn(attacker_bytes):
        plaintext = random_bytes + attacker_bytes + target_bytes
        return block_tools.aes_encrypt(plaintext, key, "ECB", pad=True)

    def guess_prefix_length(oracle_fn):
        block_size = block_tools.guess_block_size(oracle_fn)
        test_output = oracle_fn(b"A" * (3*block_size))
        assert block_tools.looks_like_ecb(test_output, block_size)
        blocks = util.chunks(test_output)
        attacker_block, attacker_block_count = Counter(blocks).most_common(1)[0]
        assert attacker_block_count >= 2
        for i in range(block_size):
            blocks = util.chunks(oracle_fn(b"A" * (3*block_size - i - 1)))
            if blocks.count(attacker_block) < attacker_block_count:
                last_attacker_block_index = (len(blocks) - 1 -
                                             list(reversed(blocks)).index(attacker_block))
                return block_size * (last_attacker_block_index - 1) + i

    prefix_length = guess_prefix_length(oracle_fn)
    plaintext = block_tools.crack_ecb_oracle(oracle_fn, prefix_length)
    assert plaintext == target_bytes


def challenge15():
    """PKCS#7 padding validation"""
    assert block_tools.pkcs7_unpad(b"ICE ICE BABY\x04\x04\x04\x04") == b"ICE ICE BABY"

    try:
        block_tools.pkcs7_unpad(b"ICE ICE BABY\x05\x05\x05\x05")
    except ValueError:
        pass
    else:
        assert False, "Padding should not be considered valid"

    try:
        block_tools.pkcs7_unpad(b"ICE ICE BABY\x01\x02\x03\x04")
    except ValueError:
        pass
    else:
        assert False, "Padding should not be considered valid"


def challenge16():
    """CBC bitflipping attacks"""
    key = block_tools.random_aes_key()
    iv = os.urandom(16)

    query_string = make_user_query_string("foo")
    ciphertext = block_tools.aes_encrypt(query_string, key, "CBC", iv, pad=True)

    new_ciphertext = bytearray(ciphertext)
    new_ciphertext[32:48] = util.xor_bytes(
        b"like%20a%20pound", b";admin=true;foo=", new_ciphertext[32:48])
    new_ciphertext = bytes(new_ciphertext)

    query_string = block_tools.aes_decrypt(new_ciphertext, key, "CBC", iv, unpad=True)
    assert b";admin=true;" in query_string


def challenge17():
    """The CBC padding oracle"""
    # The code in this challenge does a padding oracle attack. Details of
    # how it works can be found at
    # https://blog.skullsecurity.org/2013/padding-oracle-attacks-in-depth

    plaintexts = [base64.b64decode(x) for x in [
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

    random.shuffle(plaintexts)

    key = block_tools.random_aes_key()

    def encrypt(plaintext):
        iv = os.urandom(16)
        return (iv, block_tools.aes_encrypt(plaintext, key, "CBC", iv, pad=True))

    def has_valid_padding(iv, ciphertext):
        plain_bytes = block_tools.aes_decrypt(ciphertext, key, "CBC", bytes(iv))
        return block_tools.pkcs7_padding_is_valid(plain_bytes)

    def recover_plain_byte(prev_cipher_block, cipher_block, recovered_so_far):
        block_size = len(cipher_block)
        pos = block_size - len(recovered_so_far) - 1
        padding = bytes([len(recovered_so_far) + 1]) * (len(recovered_so_far) + 1)
        test_iv = bytearray(util.xor_bytes(
            prev_cipher_block,
            padding.rjust(block_size, b"\x00"),
            recovered_so_far.rjust(block_size, b"\x00")))
        for guess in english.all_bytes_by_frequency:
            test_iv[pos] = prev_cipher_block[pos] ^ guess ^ (len(recovered_so_far) + 1)
            if has_valid_padding(test_iv, cipher_block):
                if pos == block_size - 1:
                    test_iv[block_size - 2] = prev_cipher_block[block_size - 2] ^ 2
                    if not has_valid_padding(test_iv, cipher_block):
                        test_iv[block_size - 2] = prev_cipher_block[block_size - 2]
                        continue
                return bytes([guess])
        raise ValueError("can't recover byte")

    def recover_plain_block(prev_cipher_block, cipher_block):
        result = bytes()
        for _ in range(len(cipher_block)):
            result = recover_plain_byte(prev_cipher_block, cipher_block, result) + result
        return result

    def crack_padding_oracle(iv, ciphertext):
        result = bytearray()
        prev_cipher_block = iv
        for cipher_block in util.chunks(ciphertext):
            result += recover_plain_block(prev_cipher_block, cipher_block)
            prev_cipher_block = cipher_block
        return block_tools.pkcs7_unpad(result)

    for plaintext in plaintexts:
        iv, ciphertext = encrypt(plaintext)
        recovered_plaintext = crack_padding_oracle(iv, ciphertext)
        assert recovered_plaintext == plaintext
        print(recovered_plaintext.decode())


def challenge18():
    """Implement CTR, the stream cipher mode"""
    ciphertext = base64.b64decode(
        "L77na/nrFsKvynd6HzOoG7GHTLXsTVu9qvY/2syLXzhPweyyMTJULu/6/kXX0KSvoOLSFQ==")
    key = b"YELLOW SUBMARINE"
    nonce = b"\x00" * 8

    plaintext = bytearray()
    for i, block in enumerate(util.chunks(ciphertext)):
        keystream = block_tools.aes_encrypt(nonce + struct.pack("<Q", i), key, "ECB")
        plaintext += util.xor_bytes(keystream[:len(block)], block)
    print(plaintext.decode())

    assert (plaintext ==
            block_tools.aes_decrypt(ciphertext, key, "CTR", nonce, little_endian=True))


def challenge19():
    """Break fixed-nonce CTR mode using substitutions"""
    key = block_tools.random_aes_key()

    def encrypt(plaintext):
        return block_tools.aes_encrypt(plaintext, key, "CTR", nonce=b"\x00" * 8)

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

    recovered_key = english.crack_common_xor_key(ciphertexts)
    for c in ciphertexts:
        print(util.apply_repeating_xor_key(c, recovered_key).decode())


def challenge20():
    """Break fixed-nonce CTR statistically"""
    key = block_tools.random_aes_key()

    def encrypt(plaintext):
        return block_tools.aes_encrypt(plaintext, key, "CTR", nonce=b"\x00" * 8)

    with open("text_files/20.txt") as f:
        plaintexts = [base64.b64decode(x) for x in f.readlines()]
    ciphertexts = [encrypt(x) for x in plaintexts]
    recovered_key = english.crack_common_xor_key(ciphertexts)
    for c in ciphertexts:
        print(util.apply_repeating_xor_key(c, recovered_key).decode())


def challenge21():
    """Implement the MT19937 Mersenne Twister RNG"""
    rng = mersenne_twister.MT19937_RNG(seed=0)
    numbers = [rng.get_number() for _ in range(10)]
    assert numbers == [2357136044, 2546248239, 3071714933, 3626093760, 2588848963,
                       3684848379, 2340255427, 3638918503, 1819583497, 2678185683]


def challenge22():
    """Crack an MT19937 seed"""
    seed = int(time()) + random.randint(40, 1000)
    output = mersenne_twister.MT19937_RNG(seed).get_number()
    future = seed + random.randint(40, 1000)
    for seed_guess in reversed(range(future - 1000, future)):
        if mersenne_twister.MT19937_RNG(seed_guess).get_number() == output:
            assert seed_guess == seed
            return
    assert False, "seed not found"


def challenge23():
    """Clone an MT19937 RNG from its output"""
    rng = mersenne_twister.MT19937_RNG(seed=random.getrandbits(32))
    numbers = [rng.get_number() for _ in range(624)]

    # The seed passed in the next line has no effect since the buffer is
    # being overwritten.
    rng2 = mersenne_twister.MT19937_RNG(seed=0)
    rng2.buffer = [mersenne_twister.untemper(x) for x in numbers]
    rng2.index = 0
    numbers2 = [rng2.get_number() for _ in range(624)]
    assert numbers == numbers2


def challenge24():
    """Create the MT19937 stream cipher and break it"""
    def encrypt_with_rng(rng, ciphertext):
        result = bytearray()
        for chunk in util.chunks(ciphertext, 4):
            # Create 4-byte chunk from rng
            keystream_bytes = struct.pack(">L", rng.get_number())
            result += util.xor_bytes(chunk, keystream_bytes[:len(chunk)])
        return bytes(result)

    def encrypt_with_random_prefix(rng, plain_bytes):
        prefix = os.urandom(random.randint(0, 64))
        return encrypt_with_rng(rng, prefix + plain_bytes)

    seed = random.getrandbits(16)
    rng = mersenne_twister.MT19937_RNG(seed)
    test_ciphertext = encrypt_with_rng(rng, EXAMPLE_PLAIN_BYTES)
    rng = mersenne_twister.MT19937_RNG(seed)
    test_plaintext = encrypt_with_rng(rng, test_ciphertext)
    assert test_plaintext == EXAMPLE_PLAIN_BYTES

    seed = random.getrandbits(16)
    my_bytes = b"A" * 14
    ciphertext = encrypt_with_random_prefix(mersenne_twister.MT19937_RNG(seed), my_bytes)
    cipher_chunks = util.chunks(ciphertext, 4)
    # Get bytes from last 2 chunks, excluding last chunk, which may not have
    # 4 bytes, and therefore may not allow me to determine the keystream
    # numbers.
    ciphertext_with_my_bytes = b"".join(cipher_chunks[-3:-1])
    keystream = util.apply_repeating_xor_key(ciphertext_with_my_bytes, b"A")
    keystream_numbers = struct.unpack(">LL", keystream)
    untempered_numbers = [mersenne_twister.untemper(x) for x in keystream_numbers]

    for seed_guess in range(2**16):
        if seed_guess % 5000 == 0:
            print("tried {} seeds".format(seed_guess))
        test_rng = mersenne_twister.MT19937_RNG(seed_guess)
        # The obvious way to test whether seed_guess is right is to generate
        # (len(cipher_chunks) - 1) numbers from test_rng and see whether the
        # last 2 match keystream_numbers. However, that is agonizingly slow, so
        # I am twisting as much of the buffer as is necessary to see if it
        # matches untempered_numbers.
        test_rng.twist(limit=len(cipher_chunks) - 1)
        buffer_slice = test_rng.buffer[len(cipher_chunks) - 3 : len(cipher_chunks) - 1]
        if buffer_slice == untempered_numbers:
            print("found seed: {}".format(seed_guess))
            assert seed_guess == seed
            break
    else:
        assert False, "seed not found"


def challenge25():
    """Break "random access read/write" AES CTR"""
    key = block_tools.random_aes_key()
    nonce = os.urandom(8)

    def edit(ciphertext, block_index, new_bytes):
        if len(new_bytes) % 16 != 0:
            raise ValueError("new_bytes must be a multiple of 16 bytes long")
        new_ciphertext = block_tools.aes_encrypt(new_bytes, key, "CTR", nonce, block_index)
        result = bytearray(ciphertext)
        result[16*block_index : 16*block_index + len(new_bytes)] = new_ciphertext
        return bytes(result)

    # 25.txt is identical to 7.txt
    with open("text_files/25.txt") as f:
        temp_bytes = base64.b64decode(f.read())
    plain_bytes = block_tools.aes_decrypt(temp_bytes, key=b"YELLOW SUBMARINE", mode="ECB")
    ciphertext = block_tools.aes_encrypt(plain_bytes, key, "CTR", nonce)

    keystream = edit(ciphertext, 0, bytes([0]) * len(plain_bytes))
    recovered_plaintext = util.xor_bytes(ciphertext, keystream)
    assert recovered_plaintext == plain_bytes


def challenge26():
    """CTR bitflipping"""
    key = block_tools.random_aes_key()
    nonce = os.urandom(8)

    query_string = make_user_query_string("A" * 16)
    ciphertext = block_tools.aes_encrypt(query_string, key, "CTR", nonce)
    new_ciphertext = bytearray(ciphertext)
    new_ciphertext[32:48] = util.xor_bytes(
        b"A" * 16, b"ha_ha;admin=true", new_ciphertext[32:48])
    new_ciphertext = bytes(new_ciphertext)

    new_plaintext = block_tools.aes_decrypt(new_ciphertext, key, "CTR", nonce)
    assert b";admin=true;" in new_plaintext


def challenge27():
    """Recover the key from CBC with IV=Key"""
    key = block_tools.random_aes_key()
    iv = key

    def encrypt(user_bytes):
        return block_tools.aes_encrypt(user_bytes, key, "CBC", iv, pad=True)

    def decrypt(ciphertext):
        # If plaintext has any non-ASCII bytes, raise exception, else do nothing
        block_tools.aes_decrypt(ciphertext, key, "CBC", iv).decode("ascii")

    ciphertext = encrypt(EXAMPLE_PLAIN_BYTES)
    modified_ciphertext = ciphertext[:16] + bytes([0] * 16) + ciphertext

    try:
        decrypt(modified_ciphertext)
    except UnicodeDecodeError as e:
        plain_bytes = e.args[1]
        recovered_key = util.xor_bytes(plain_bytes[0:16], plain_bytes[32:48])
        assert recovered_key == key
    else:
        assert False


def challenge28():
    """Implement a SHA-1 keyed MAC"""
    key = os.urandom(16)
    assert sha1(key + b"message1").digest() != sha1(key + b"message2").digest()


def challenge29():
    """Break a SHA-1 keyed MAC using length extension"""
    key = os.urandom(16)
    query_string = make_user_query_string("foo")
    mac = sha1(key + query_string).digest()

    glue_padding = pure_python_sha1.padding(len(key + query_string))
    new_param = b";admin=true"
    modified_hash_fn = pure_python_sha1.Sha1Hash(
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
    query_string = make_user_query_string("foo")
    mac = MD4(key + query_string)
    hash_fn = hashlib.new("md4")
    hash_fn.update(key + query_string)
    assert hash_fn.digest() == mac

    glue_padding = md4_padding(len(key + query_string))
    new_param = b";admin=true"
    new_hash = MD4(new_param,
                   fake_byte_len=len(key + query_string + glue_padding + new_param),
                   state=struct.unpack("<4I", mac))

    expected_hash = MD4(key + query_string + glue_padding + new_param)
    assert new_hash == expected_hash


def challenge31(dummy_server=False):
    """Implement and break HMAC-SHA1 with an artificial timing leak"""
    hmac_key = os.urandom(16)
    filename = "text_files/hamlet.txt"
    with open(filename, "rb") as f:
        hmac = util.calculate_hmac(hmac_key, f.read())
    print("looking for {}\n".format(util.pretty_hex_bytes(hmac)))

    if dummy_server:
        def validate_signature(sig):
            return timing_attack.insecure_compare(sig, hmac, delay=0.05)

        signature = timing_attack.recover_signature(
            validate_signature, thread_count=300, threshold=0.0075, attempt_limit=5,
            retry_limit=20)
    else:
        def compare_sigs(a, b):
            return timing_attack.insecure_compare(a, b, delay=0.05)

        server_address = ("localhost", 31415)

        def validate_signature(sig):
            return timing_attack.server_approves_of_signature(
                server_address, filename, sig)

        server = timing_attack.Server(server_address, hmac_key, compare_sigs)
        try:
            Thread(target=server.serve_forever).start()
            signature = timing_attack.recover_signature(
                validate_signature, thread_count=35, threshold=0.0075, attempt_limit=5,
                retry_limit=20)
        finally:
            server.shutdown()
            server.server_close()

    assert signature == hmac


def challenge32(dummy_server=False):
    """Break HMAC-SHA1 with a slightly less artificial timing leak"""
    hmac_key = os.urandom(16)
    filename = "text_files/hamlet.txt"
    with open(filename, "rb") as f:
        hmac = util.calculate_hmac(hmac_key, f.read())
    print("looking for {}\n".format(util.pretty_hex_bytes(hmac)))

    if dummy_server:
        def validate_signature(sig):
            return timing_attack.insecure_compare(sig, hmac, delay=0.025)

        signature = timing_attack.recover_signature(
            validate_signature, thread_count=300, threshold=0.006, attempt_limit=10,
            retry_limit=10)
    else:
        def compare_sigs(a, b):
            return timing_attack.insecure_compare(a, b, delay=0.025)

        server_address = ("localhost", 31415)

        def validate_signature(sig):
            return timing_attack.server_approves_of_signature(
                server_address, filename, sig)

        server = timing_attack.Server(server_address, hmac_key, compare_sigs)
        try:
            Thread(target=server.serve_forever).start()
            signature = timing_attack.recover_signature(
                validate_signature, thread_count=15, threshold=0.006, attempt_limit=10,
                retry_limit=10)
        finally:
            server.shutdown()
            server.server_close()

    assert signature == hmac


def challenge33():
    """Implement Diffie-Hellman"""
    alice = diffie_hellman.User(p=37, g=5)
    bob = diffie_hellman.User(p=37, g=5)
    assert alice.get_shared_key_for(bob) == bob.get_shared_key_for(alice)

    alice = diffie_hellman.User()
    bob = diffie_hellman.User()
    assert alice.get_shared_key_for(bob) == bob.get_shared_key_for(alice)


def challenge34():
    """Implement a MITM key-fixing attack on Diffie-Hellman with parameter injection"""
    alice = diffie_hellman.User()
    bob = diffie_hellman.User()
    alice.send_echo_request(bob, EXAMPLE_PLAIN_BYTES)
    assert EXAMPLE_PLAIN_BYTES in bob.inbox[alice]

    alice = diffie_hellman.User()
    bob = diffie_hellman.User()
    mallory = diffie_hellman.User()
    mallory.public_key = mallory.p
    assert alice.get_shared_key_for(mallory) == 0
    mallory._shared_keys[alice] = 0
    assert bob.get_shared_key_for(mallory) == 0
    mallory._shared_keys[bob] = 0
    alice.send_echo_request(mallory, EXAMPLE_PLAIN_BYTES)
    # Mallory decrypts request without real key.
    assert EXAMPLE_PLAIN_BYTES in mallory.inbox[alice]
    mallory.send_echo_request(bob, EXAMPLE_PLAIN_BYTES)
    assert EXAMPLE_PLAIN_BYTES in bob.inbox[mallory]


def challenge35():
    """Implement DH with negotiated groups, and break with malicious "g" parameters"""
    # Mallory tricks Alice and Bob into using g=1
    alice = diffie_hellman.User(g=1)
    bob = diffie_hellman.User(g=1)
    mallory = diffie_hellman.User(g=1)
    assert mallory.public_key == 1
    assert alice.get_shared_key_for(mallory) == 1
    assert bob.get_shared_key_for(mallory) == 1
    alice.send_echo_request(mallory, EXAMPLE_PLAIN_BYTES)
    # Mallory decrypts request without real key.
    assert EXAMPLE_PLAIN_BYTES in mallory.inbox[alice]
    mallory.send_echo_request(bob, EXAMPLE_PLAIN_BYTES)
    assert EXAMPLE_PLAIN_BYTES in bob.inbox[mallory]

    # Mallory tricks Alice and Bob into using g=IETF_PRIME
    alice = diffie_hellman.User(g=util.IETF_PRIME)
    bob = diffie_hellman.User(g=util.IETF_PRIME)
    mallory = diffie_hellman.User(g=util.IETF_PRIME)
    assert mallory.public_key == 0
    assert alice.get_shared_key_for(mallory) == 0
    assert bob.get_shared_key_for(mallory) == 0
    alice.send_echo_request(mallory, EXAMPLE_PLAIN_BYTES)
    # Mallory decrypts request without real key.
    assert EXAMPLE_PLAIN_BYTES in mallory.inbox[alice]
    mallory.send_echo_request(bob, EXAMPLE_PLAIN_BYTES)
    assert EXAMPLE_PLAIN_BYTES in bob.inbox[mallory]

    # Mallory tricks Alice and Bob into using g=IETF_PRIME - 1
    alice = diffie_hellman.User(g=util.IETF_PRIME - 1)
    bob = diffie_hellman.User(g=util.IETF_PRIME - 1)
    # Private key must be even.
    mallory = diffie_hellman.User(g=util.IETF_PRIME - 1,
                                  private_key=random.randrange(0, util.IETF_PRIME, 2))
    assert mallory.public_key == 1
    assert alice.get_shared_key_for(mallory) == 1
    assert bob.get_shared_key_for(mallory) == 1
    alice.send_echo_request(mallory, EXAMPLE_PLAIN_BYTES)
    # Mallory decrypts request without real key.
    assert EXAMPLE_PLAIN_BYTES in mallory.inbox[alice]
    mallory.send_echo_request(bob, EXAMPLE_PLAIN_BYTES)
    assert EXAMPLE_PLAIN_BYTES in bob.inbox[mallory]


def challenge36():
    """Implement Secure Remote Password (SRP)"""
    username = "peter.gregory@piedpiper.com"
    password = "letmein"
    wrong_password = "qwerty"

    server = srp.Server()
    client = srp.Client()
    client.sign_up(server, username, password)

    assert client.log_in(server, username, password)
    assert not client.log_in(server, username, wrong_password)


def challenge37():
    """Break SRP with a zero key"""
    username = "peter.gregory@piedpiper.com"
    password = "letmein"

    server = srp.Server()
    client = srp.Client()
    client.sign_up(server, username, password)

    for i in range(10):
        # Attacker tricks server into computing easily derivable session key
        salt, _, _ = server._respond_to_login_request(username, i * util.IETF_PRIME)
        # Attacker derives shared session key without password
        shared_session_key = sha256(util.int_to_bytes(0)).digest()
        hmac = util.calculate_hmac(shared_session_key, salt, sha256)
        # Attacker logs in without password
        assert server._verify_hmac(hmac, username)


def challenge38():
    """Offline dictionary attack on simplified SRP"""
    username = "peter.gregory@piedpiper.com"
    password = "letmein"
    wrong_password = "qwerty"

    server = srp.Server()
    client = srp.Client()
    client.sign_up(server, username, password)
    assert client.log_in(server, username, password, k=0)
    assert not client.log_in(server, username, wrong_password, k=0)

    server = srp.Server()
    mallory_server = srp.MitmServer(server)
    client.sign_up(server, username, password)
    login_is_valid = client.log_in(mallory_server, username, password, k=0)
    assert login_is_valid
    assert mallory_server.users[username]["password"] == password


def challenge39():
    """Implement RSA"""
    assert util.mod_inv(17, 3120) == 2753

    public_key, private_key = rsa.KeyPair.random()

    ciphertext = rsa.encrypt(EXAMPLE_PLAIN_BYTES, public_key)

    # rsa.encrypt left-pads its result to make it as long as the modulus.
    # The call to lstrip is needed to undo this.
    plaintext = rsa.decrypt(ciphertext, private_key).lstrip(b"\x00")
    assert plaintext == EXAMPLE_PLAIN_BYTES


def challenge40():
    """Implement an E=3 RSA Broadcast attack"""
    ciphertext_data = []
    modulus_product = 1
    for i in range(3):
        public_key, _ = rsa.KeyPair.random()
        ciphertext = rsa.encrypt(EXAMPLE_PLAIN_BYTES, public_key)
        ciphertext_data.append({
            "modulus": public_key.modulus,
            "cipher_int": int.from_bytes(ciphertext, byteorder="big"),
        })
        modulus_product *= public_key.modulus

    assert all(gcd(x["modulus"], y["modulus"]) == 1
               for x, y in itertools.combinations(ciphertext_data, 2))

    cube = 0
    for x in ciphertext_data:
        # strange name picked for similarity to notation in challenge
        m_s_ = modulus_product // x["modulus"]
        cube += x["cipher_int"] * m_s_ * util.mod_inv(m_s_, x["modulus"])
    cube %= modulus_product
    assert all(x["cipher_int"] == cube % x["modulus"] for x in ciphertext_data)

    root = round(util.big_int_cube_root(cube))
    assert root ** 3 == cube
    plaintext = util.int_to_bytes(root)
    assert plaintext == EXAMPLE_PLAIN_BYTES


def challenge41():
    """Implement unpadded message recovery oracle"""
    seen_message_hashes = set()
    public_key, private_key = rsa.KeyPair.random()

    class AccessDeniedError(Exception):
        pass

    def decrypt(ciphertext):
        plaintext = rsa.decrypt(ciphertext, private_key)
        plaintext_hash = sha256(plaintext).digest()
        if plaintext_hash in seen_message_hashes:
            raise AccessDeniedError()
        seen_message_hashes.add(plaintext_hash)
        return plaintext

    ciphertext = rsa.encrypt(EXAMPLE_PLAIN_BYTES, public_key)
    plaintext = decrypt(ciphertext)
    try:
        decrypt(ciphertext)
    except AccessDeniedError:
        pass
    else:
        assert False

    modulus = public_key.modulus
    S = random.randint(2, modulus - 1)
    oracle_ciphertext = rsa.multiply(ciphertext, S**public_key.exponent, modulus)
    oracle_plaintext = decrypt(oracle_ciphertext)
    S_inverse = util.mod_inv(S, modulus)
    recovered_plaintext = rsa.multiply(oracle_plaintext, S_inverse, modulus)
    assert recovered_plaintext == plaintext


def challenge42():
    """Bleichenbacher's e=3 RSA Attack"""
    # aka BERserk
    # Details about how this works can be found at the following URLs:
    # https://www.ietf.org/mail-archive/web/openpgp/current/msg00999.html
    # http://www.withouthat.org/~sid/me/wp-content/uploads/2008/09/document.pdf
    modulus_length = 128
    public_key, private_key = rsa.KeyPair.random(bit_length=modulus_length * 8)

    message = b"hi mom"

    ciphertext = rsa.pad_and_encrypt(message, public_key)
    assert rsa.unpad(rsa.decrypt(ciphertext, private_key)) == message

    sig = rsa.sign(message, private_key)
    assert rsa.verify(message, public_key, sig)

    digest_info = rsa.create_digest_asn1(message)
    padded_sig = rsa.pad(digest_info, len(digest_info) + 11, block_type=1)
    sig_block = padded_sig.ljust(modulus_length, b"\x00")
    sig_block_int = int.from_bytes(sig_block, byteorder="big")
    forged_sig_int = ceil(util.big_int_cube_root(sig_block_int))
    forged_sig = forged_sig_int.to_bytes(length=modulus_length, byteorder="big")

    assert rsa.decrypt(forged_sig, public_key).startswith(padded_sig)
    assert not rsa.verify(message, public_key, forged_sig)
    assert rsa.verify(message, public_key, forged_sig, secure=False)


def challenge43():
    """DSA key recovery from nonce"""
    message = EXAMPLE_PLAIN_BYTES
    public_key, private_key = dsa.KeyPair.random()
    sig = dsa.sign(message, private_key)
    assert dsa.verify(message, public_key, sig)

    sig, k = dsa.sign_and_leak_k(message, private_key)
    assert dsa.recover_private_key(k, message, sig) == private_key

    public_key = int("84ad4719d044495496a3201c8ff484feb45b962e7302e56a392aee4abab3e4bdebf"
                     "2955b4736012f21a08084056b19bcd7fee56048e004e44984e2f411788efdc837a0"
                     "d2e5abb7b555039fd243ac01f0fb2ed1dec568280ce678e931868d23eb095fde9d3"
                     "779191b8c0299d6e07bbb283e6633451e535c45513b2d33c99ea17", 16)
    message = (b"For those that envy a MC it can be hazardous to your health\n"
               b"So be friendly, a matter of life and death, just like a etch-a-sketch\n")
    assert sha1(message).hexdigest() == "d2d0714f014a9784047eaeccf956520045c45265"
    sig = dsa.Signature(
        r=548099063082341131477253921760299949438196259240,
        s=857042759984254168557880549501802188789837994940)
    assert dsa.verify(message, public_key, sig)
    for k_guess in range(2**16):
        private_key_guess = dsa.recover_private_key(k_guess, message, sig)
        private_key_hash = sha1("{:x}".format(private_key_guess).encode()).hexdigest()
        if private_key_hash == "0954edd5e0afe5542a4adf012611a91912a3ec16":
            assert pow(dsa.g, private_key_guess, dsa.p) == public_key
            print("private key found: {}".format(private_key_guess))
            print("k: {}".format(k_guess))
            return
    assert False, "private key not found"


def challenge44():
    """DSA nonce recovery from repeated nonce"""
    messages = []
    with open("text_files/44.txt") as f:
        message_data = {}
        for line in f.readlines():
            key, value = re.match("^(.+): (.+)$", line).groups()
            if key in message_data:
                digest = sha1(message_data["msg"].encode()).hexdigest()
                assert digest == message_data["m"].rjust(40, "0")
                messages.append({
                    "message": message_data["msg"].encode(),
                    "sig": dsa.Signature(int(message_data["r"]), int(message_data["s"])),
                    "hash": int(message_data["m"], 16),
                })
                message_data = {}
            message_data[key] = value
    for message1, message2 in itertools.combinations(messages, 2):
        if message1["sig"].r == message2["sig"].r:
            s_diff_inverse = util.mod_inv(message1["sig"].s - message2["sig"].s, dsa.q)
            k = ((message1["hash"] - message2["hash"]) * s_diff_inverse) % dsa.q
            guess1 = dsa.recover_private_key(k, message1["message"], message1["sig"])
            guess2 = dsa.recover_private_key(k, message2["message"], message2["sig"])
            assert guess1 == guess2
            public_key = int("2d026f4bf30195ede3a088da85e398ef869611d0f68f0713d51c9c1a3a2"
                             "6c95105d915e2d8cdf26d056b86b8a7b85519b1c23cc3ecdc6062650462"
                             "e3063bd179c2a6581519f674a61f1d89a1fff27171ebc1b93d4dc57bceb"
                             "7ae2430f98a6a4d83d8279ee65d71c1203d2c96d65ebbf7cce9d32971c3"
                             "de5084cce04a2e147821", 16)
            assert pow(dsa.g, guess1, dsa.p) == public_key
            private_key_hash = sha1("{:x}".format(guess1).encode()).hexdigest()
            assert private_key_hash == "ca8f6f7c66fa362d40760d135b763eb8527d3d52"

            print("private key found: {}".format(guess1))
            print("messages with repeated k:")
            pprint(message1)
            pprint(message2)
            return
    assert False, "private key not found"


def challenge45():
    """DSA parameter tampering"""
    message = EXAMPLE_PLAIN_BYTES
    public_key, private_key = dsa.KeyPair.random()

    sig = dsa.sign(message, private_key, g=0, secure=False)
    assert dsa.verify(message, public_key, sig, g=0, secure=False)

    bad_message = b"The quick brown fox jumps over the lazy dog."
    bad_sig = dsa.sign(bad_message, private_key, g=0, secure=False)
    assert dsa.verify(bad_message, public_key, bad_sig, g=0, secure=False)

    for _ in range(10):
        random_message = os.urandom(random.randint(1, 1000))
        random_sig = dsa.Signature(r=0, s=random.randint(1, dsa.q - 1))
        assert dsa.verify(random_message, public_key, random_sig, g=0, secure=False)

    for i in range(10):
        bad_g = i*dsa.p + 1
        z = random.randint(1, dsa.q - 1)
        r = pow(public_key, z, dsa.p) % dsa.q
        s = (r * util.mod_inv(z, dsa.q)) % dsa.q
        magic_sig = dsa.Signature(r, s)
        assert dsa.verify(b"Hello world", public_key, magic_sig, g=bad_g)
        assert dsa.verify(b"Goodbye, world", public_key, magic_sig, g=bad_g)


def challenge46():
    """RSA parity oracle"""
    public_key, private_key = rsa.KeyPair.random()

    def plaintext_is_odd(ciphertext):
        return rsa.decrypt(ciphertext, private_key)[-1] & 1 == 1

    message = base64.b64decode(b"VGhhdCdzIHdoeSBJIGZvdW5kIHlvdSBkb24ndCBwbGF5IG"
                               b"Fyb3VuZCB3aXRoIHRoZSBGdW5reSBDb2xkIE1lZGluYQ==")

    ciphertext = rsa.pad_and_encrypt(message, public_key)

    recovered_padded_plaintext = rsa.crack_parity_oracle(
        ciphertext, public_key, plaintext_is_odd, verbose=False)
    recovered_plaintext = rsa.unpad(recovered_padded_plaintext)
    assert recovered_plaintext == message


def challenge47():
    """Bleichenbacher's PKCS 1.5 Padding Oracle (Simple Case)"""
    public_key, private_key = rsa.KeyPair.random(bit_length=256)

    def padding_looks_ok(ciphertext):
        return rsa.decrypt(ciphertext, private_key)[:2] == b"\x00\x02"

    message = b"kick it, CC"
    ciphertext = rsa.pad_and_encrypt(message, public_key)
    assert padding_looks_ok(ciphertext)

    recovered_padded_plaintext = rsa.crack_padding_oracle(
        ciphertext, public_key, padding_looks_ok)
    recovered_plaintext = rsa.unpad(recovered_padded_plaintext)
    assert recovered_plaintext == message


def challenge48():
    """Bleichenbacher's PKCS 1.5 Padding Oracle (Complete Case)"""
    public_key, private_key = rsa.KeyPair.random(bit_length=768)

    def padding_looks_ok(ciphertext):
        return rsa.decrypt(ciphertext, private_key)[:2] == b"\x00\x02"

    message = b"kick it, CC"
    ciphertext = rsa.pad_and_encrypt(message, public_key)
    assert padding_looks_ok(ciphertext)

    recovered_padded_plaintext = rsa.crack_padding_oracle(
        ciphertext, public_key, padding_looks_ok)
    recovered_plaintext = rsa.unpad(recovered_padded_plaintext)
    assert recovered_plaintext == message


def challenge49():
    """CBC-MAC Message Forgery"""
    key = block_tools.random_aes_key()
    block_size = 16

    def transaction_message(from_id, to_id, amount):
        return urlencode([("from", from_id), ("to", to_id), ("amount", amount)]).encode()

    def transaction_list_message(from_id, transactions):
        tx_list = ";".join("{to}:{amount}".format(**tx) for tx in transactions)
        return urlencode([("from", from_id), ("tx_list", tx_list)], safe=":;").encode()

    def message_mac(message, iv=b"\x00"*block_size):
        return block_tools.aes_encrypt(message, key, "CBC", iv, pad=True)[-block_size:]

    def request_is_valid(message, expected_mac, iv=b"\x00"*block_size):
        return expected_mac == message_mac(message, iv)

    iv = os.urandom(block_size)
    message1 = transaction_message(
        from_id="DarkHelmet", to_id="Pizza_The_Hutt", amount=1000000)
    assert message1 == b"from=DarkHelmet&to=Pizza_The_Hutt&amount=1000000"
    mac1 = message_mac(message1, iv)
    assert request_is_valid(message1, mac1, iv)

    wrong_mac = os.urandom(block_size)
    assert not request_is_valid(message1, wrong_mac, iv)

    assert message1[:block_size] == b"from=DarkHelmet&"
    new_block = b"from=Lone_Starr&"
    forged_message1 = new_block + message1[block_size:]
    assert forged_message1 == b"from=Lone_Starr&to=Pizza_The_Hutt&amount=1000000"
    attacker_iv = util.xor_bytes(iv, message1[:block_size], new_block)
    assert request_is_valid(forged_message1, mac1, attacker_iv)

    message2 = transaction_list_message(
        from_id="Roland",
        transactions=[
            {"to": "Lone_Starr", "amount": 248},
            {"to": "Prince_Murray", "amount": 50000}])
    assert message2 == b"from=Roland&tx_list=Lone_Starr:248;Prince_Murray:50000"
    mac2 = message_mac(message2)

    extension = b";Pizza_The_Hutt:1000000"
    modified_extension = (util.xor_bytes(mac2, extension[:block_size]) +
                          extension[block_size:])
    forged_message2 = block_tools.pkcs7_pad(message2) + extension
    # TODO: try to forge a message without padding in the middle. Also
    # calculate MAC without calculating MAC of modified_extension.
    assert request_is_valid(forged_message2, message_mac(modified_extension))


def challenge50():
    """Hashing with CBC-MAC"""
    key = b"YELLOW SUBMARINE"

    def encrypt(message):
        return block_tools.aes_encrypt(message, key, "CBC", iv=b"\x00"*16)

    def decrypt(message):
        return block_tools.aes_decrypt(message, key, "CBC", iv=b"\x00"*16)

    def mac_hash(message):
        return encrypt(block_tools.pkcs7_pad(message))[-16:]

    def comment_piece_is_valid(piece_bytes):
        try:
            piece_bytes.decode()
        except UnicodeDecodeError:
            return False
        else:
            return all(x not in b"/*\r\a" for x in piece_bytes)

    snippet = b"alert('MZA who was that?');\n"
    mac = mac_hash(snippet)
    assert mac.hex() == "296b8d7cb78a243dda4d0a61d33bbdd1"
    print("snippet:\n{}".format(snippet.decode()))

    valid_chars = string.ascii_letters + string.digits
    forged_snippet_end = b"**************/"
    nonsense_input = decrypt(
        util.xor_bytes(
            block_tools.pkcs7_pad(forged_snippet_end),
            decrypt(mac)))
    while True:
        comment_begin = b"".join(random.choice(valid_chars).encode() for _ in range(15))
        forged_snippet_begin = b"alert('Ayo, the Wu is back!');\n/*" + comment_begin
        nonsense = util.xor_bytes(nonsense_input, encrypt(forged_snippet_begin)[-16:])
        if comment_piece_is_valid(nonsense):
            forged_snippet = forged_snippet_begin + nonsense + forged_snippet_end
            break
    print("forged snippet:\n{}".format(forged_snippet.decode()))
    assert mac_hash(forged_snippet) == mac


def challenge51():
    """Compression Ratio Side-Channel Attacks"""
    session_id = b"TmV2ZXIgcmV2ZWFsIHRoZSBXdS1UYW5nIFNlY3JldCE="
    assert base64.b64decode(session_id) == b"Never reveal the Wu-Tang Secret!"

    def format_request(payload):
        return b"\n".join([
            b"POST / HTTP/1.1",
            b"Host: hapless.com",
            b"Cookie: sessionid=" + session_id,
            b"Content-Length: " + str(len(payload)).encode(),
            payload
        ])

    def ctr_oracle_fn(payload):
        key = block_tools.random_aes_key()
        plaintext = gzip.compress(format_request(payload))
        return len(block_tools.aes_encrypt(plaintext, key, "CTR", nonce=os.urandom(8)))

    def cbc_oracle_fn(payload):
        key = block_tools.random_aes_key()
        iv = os.urandom(16)
        plaintext = gzip.compress(format_request(payload))
        return len(block_tools.aes_encrypt(plaintext, key, "CBC", iv, pad=True))

    def crack_compression_oracle(oracle_fn):
        base64_alphabet = [bytes([x]) for x in b"ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                           b"abcdefghijklmnopqrstuvwxyz0123456789+/=\n"]
        result = bytearray()
        while True:
            for i in itertools.count(start=0):
                prefix = os.urandom(i) + b"sessionid=" + result
                length_map = {x: oracle_fn(prefix + x) for x in base64_alphabet}
                min_length = min(length_map.values())
                good_guesses = [x for x in length_map if length_map[x] == min_length]
                if good_guesses == [b"\n"]:
                    return bytes(result)
                elif len(good_guesses) == 1:
                    result += good_guesses[0]
                    break

    for oracle_fn in [ctr_oracle_fn, cbc_oracle_fn]:
        recovered_session_id = crack_compression_oracle(oracle_fn)
        assert recovered_session_id == session_id


def challenge52():
    """Iterated Hash Function Multicollisions"""
    # Details of how this works can be found at the following URL:
    # http://math.boisestate.edu/~liljanab/Math509Spring10/JouxAttackSHA-1.pdf
    def find_multiple_collisions(hash_fn, n):
        """Return 2**n messages, each with length n * hash_fn.block_size, that have
        the same hash.
        """
        state = hash_fn.initial_state
        block_pairs = []
        for _ in range(n):
            collision_map = defaultdict(set)
            for block in hash_fn.random_unique_blocks():
                test_state = hash_fn.compress(state, block)
                collision_map[test_state].add(block)
                if len(collision_map[test_state]) > 1:
                    state = test_state
                    block_pairs.append(collision_map[test_state])
                    break
        return (b"".join(x) for x in itertools.product(*block_pairs))

    def find_cascaded_collision(cheap_hash_fn, expensive_hash_fn):
        n = expensive_hash_fn.digest_size * 8 // 2
        while True:
            collision_map = defaultdict(set)
            for message in find_multiple_collisions(cheap_hash_fn, n):
                expensive_hash = expensive_hash_fn(message)
                collision_map[expensive_hash].add(message)
                if len(collision_map[expensive_hash]) > 1:
                    return list(collision_map[expensive_hash])

    hash_fn = merkle_damgard.HashFunction(digest_size=2)
    n = 10
    messages = list(find_multiple_collisions(hash_fn, n))
    assert len(messages) == 2**n
    assert len(set(hash_fn(x) for x in messages)) == 1
    print("Generated {} messages with hash {}.\n".format(
        len(messages), util.pretty_hex_bytes(hash_fn(messages[0]))))

    cheap_hash_fn = merkle_damgard.HashFunction(digest_size=2)
    expensive_hash_fn = merkle_damgard.HashFunction(digest_size=4)
    expensive_hash_fn.compress = functools.lru_cache(maxsize=None)(expensive_hash_fn.compress)
    print("Looking for collision on cascaded hash function")
    messages = find_cascaded_collision(cheap_hash_fn, expensive_hash_fn)
    assert len(set(cheap_hash_fn(x) + expensive_hash_fn(x) for x in messages)) == 1
    print("The following messages have combined hash [{}] + [{}]:".format(
        util.pretty_hex_bytes(cheap_hash_fn(messages[0])),
        util.pretty_hex_bytes(expensive_hash_fn(messages[0]))))
    print("\n\n".join(util.pretty_hex_bytes(m) for m in messages))


def challenge53():
    """Kelsey and Schneier's Expandable Messages"""
    # Details about how this works can be found at the following URL:
    # https://www.schneier.com/academic/paperfiles/paper-preimages.pdf

    def make_fixed_point_message_pieces(hash_fn):
        trial_block_count = 2**(hash_fn.digest_size * 8 // 2)
        for first_block in hash_fn.random_unique_blocks():
            state = hash_fn(first_block, pad=False)
            for repeatable_block in hash_fn.random_unique_blocks(trial_block_count):
                if hash_fn.compress(state, repeatable_block) == state:
                    return (first_block, repeatable_block)

    def make_fixed_point_message(message_pieces, block_count):
        first_block, repeatable_block = message_pieces
        return first_block + ((block_count - 1) * repeatable_block)

    def make_unequal_length_collision(block_count, hash_fn, state):
        """Produce 2 messages with the same hash. The first will be one block long
        and the second will be block_count blocks long.
        """
        message_trial_count = 2**(hash_fn.digest_size * 8 // 2)
        for filler_block in hash_fn.random_unique_blocks():
            filler = filler_block * (block_count - 1)
            filler_state = hash_fn(filler, state, pad=False)
            blocks = set(hash_fn.random_unique_blocks(message_trial_count))
            long_message_ends = {hash_fn.compress(filler_state, b): b for b in blocks}
            for short_message in blocks:
                block_state = hash_fn.compress(state, short_message)
                if block_state in long_message_ends:
                    long_message = filler + long_message_ends[block_state]
                    assert (hash_fn(short_message, state, pad=False) ==
                            hash_fn(long_message, state, pad=False))
                    return ((short_message, long_message), block_state)

    def make_expandable_message_pieces(hash_fn, k, state=None):
        """Make pieces that can be used to make messages containing k to
        (k + 2**k - 1) blocks, inclusive, all with the same hash.
        """
        state = state or hash_fn.initial_state
        result = []
        for i in range(k):
            collision, state = make_unequal_length_collision(2**i + 1, hash_fn, state)
            result.append(collision)
        return result

    def make_expandable_message(message_piece_pairs, block_count):
        """Make a message using pieces from message_piece_pairs, consisting of
        block_count blocks. message_piece_pairs should be produced by
        make_expandable_message_pieces. The message will have the same hash as
        it would if the same message_piece_pairs were passed with a different
        block_count.
        """
        k = len(message_piece_pairs)
        if not (k <= block_count <= 2**k + k - 1):
            raise ValueError(
                "block_count must be between {} and {} for {} message piece pairs".format(
                    k, 2**k + k - 1, block_count))
        bits = [int(x) for x in reversed("{:b}".format(block_count - k).zfill(k))]
        return b"".join(pair[bit] for pair, bit in zip(message_piece_pairs, bits))

    hash_fn = merkle_damgard.HashFunction(digest_size=2)

    fixed_point_pieces = make_fixed_point_message_pieces(hash_fn)
    messages = [make_fixed_point_message(fixed_point_pieces, block_count)
                for block_count in range(1, 101)]
    hashes = set(hash_fn(m, pad=False) for m in messages)
    assert len(hashes) == 1
    fixed_point_state = list(hashes)[0]

    for k in range(1, 7):
        message_piece_pairs = make_expandable_message_pieces(hash_fn, k)
        messages = [make_expandable_message(message_piece_pairs, block_count)
                    for block_count in range(k, 2**k + k)]
        hashes = set(hash_fn(m, pad=False) for m in messages)
        assert len(hashes) == 1

        padded_message_piece_pairs = make_expandable_message_pieces(
            hash_fn, k, fixed_point_state)
        block_count = 2**k + k
        messages = []
        for i in range(k, block_count):
            prefix = make_fixed_point_message(fixed_point_pieces, block_count - i)
            suffix = make_expandable_message(padded_message_piece_pairs, i)
            messages.append(prefix + suffix)
        hashes = set(hash_fn(m) for m in messages)
        assert len(hashes) == 1


def challenge54():
    """Kelsey and Kohno's Nostradamus Attack"""
    # Details about how this works can be found at the following URL:
    # https://homes.cs.washington.edu/~yoshi/papers/EC06/herding.pdf
    class Diamond:
        def __init__(self, hash_fn, k):
            # TODO: make diamond more efficiently, as described in paper

            self.hash_fn = hash_fn
            self.k = k
            self.blocks = {}
            self.states = {(0, i): os.urandom(self.hash_fn.digest_size)
                           for i in range(2**self.k)}

            for level_idx in range(self.k):
                for j in range(2 ** (self.k - level_idx - 1)):
                    block_maps = [{}, {}]
                    for block in self.hash_fn.random_unique_blocks():
                        for i in [0, 1]:
                            state = self.hash_fn.compress(self.states[level_idx, 2*j + i],
                                                          block)
                            if state in block_maps[1 - i]:
                                self.blocks[level_idx, 2*j + i] = block
                                self.blocks[level_idx, 2*j + 1 - i] = block_maps[1 - i][state]
                                self.states[level_idx + 1, j] = state
                                break
                            block_maps[i][state] = block
                        if (level_idx + 1, j) in self.states:
                            break

            self.state_dict = {state: indexes for indexes, state in self.states.items()}

            assert self.is_consistent()

        def is_consistent(self):
            for indexes, state in self.states.items():
                level_idx, node_idx = indexes
                if level_idx < self.k:
                    next_state = self.hash_fn.compress(state, self.blocks[indexes])
                    if next_state != self.states[level_idx + 1, node_idx // 2]:
                        return False
                suffix = self.suffix_for_indexes(indexes)
                if self.hash_fn(suffix, state, pad=False) != self.final_hash:
                    return False
            return True

        @property
        def final_hash(self):
            return self.states[self.k, 0]

        def suffix_for_indexes(self, indexes):
            level_idx, node_idx = indexes
            return b"".join(self.blocks[i, node_idx // 2**(i - level_idx)]
                            for i in range(level_idx, self.k))

        def make_message_with_prefix(self, prefix):
            # TODO: make more meaningful messages, as described in paper

            if len(prefix) % self.hash_fn.block_size != 0:
                raise ValueError(
                    "length of prefix must be a multiple of hash_fn.block_size")
            prefix_state = self.hash_fn(prefix, pad=False)
            for linking_message in self.hash_fn.random_unique_blocks():
                state = self.hash_fn(linking_message, prefix_state, pad=False)
                if state in self.state_dict:
                    suffix = self.suffix_for_indexes(self.state_dict[state])
                    result = prefix + linking_message + suffix
                    assert self.hash_fn(result, pad=False) == self.final_hash
                    return result

    hash_fn = merkle_damgard.HashFunction(digest_size=2)
    diamond = Diamond(hash_fn, k=4)

    prefix = random.choice([
        b"SF Giants win the World Series!!",
        b"Tigers win 2017 World Series 4-1",
        b"Red Sox win '17 World Series 4-2",
    ])
    print(diamond.make_message_with_prefix(prefix))

    # TODO: make this work even if message is padded


def challenge55():
    """MD4 Collisions"""
    # TODO: figure out what I'm supposed to do here
    raise NotImplementedError


def challenge56():
    """RC4 Single-Byte Biases"""
    # Details about how this works can be found at the following URL:
    # http://www.isg.rhul.ac.uk/tls/RC4biases.pdf
    # TODO: make this faster and more accurate
    cookie = base64.b64decode(b"QkUgU1VSRSBUTyBEUklOSyBZT1VSIE9WQUxUSU5F")

    def oracle_fn(attacker_bytes):
        return ARC4.new(key=os.urandom(16)).encrypt(attacker_bytes + cookie)

    def best_cookie_guess(byte_counters):
        return bytes(max(counter, default=ord(b"_"), key=counter.get)
                     for counter in byte_counters)

    def most_likely_keystream_byte(pos):
        if pos % 16 == 15 and 15 <= pos <= 111:
            return 256 - (pos + 1)
        elif 4 <= pos <= 30:
            return pos + 1
        elif pos == 0:
            return 144
        elif pos == 2:
            return 131
        else:
            return 0

    def show_progress(byte_counters, i):
        if i % 10000 == 0:
            recovered_so_far = best_cookie_guess(byte_counters)
            print("{:10,} {}".format(i, repr(recovered_so_far.decode(errors="replace"))))

    # Speed optimization: use defaultdicts instead of Counters.
    byte_counters = [defaultdict(lambda: 0) for _ in range(len(cookie))]
    # Speed optimization: save keystream byte guesses in a variable instead of
    # calling most_likely_keystream_byte in inner loop.
    keystream_guess = [most_likely_keystream_byte(i) for i in range(256)]
    for i in range(int(1e7)):
        show_progress(byte_counters, i)
        for j in range(16):
            ciphertext = oracle_fn(b"\x00" * j)
            for k in range(len(cookie)):
                byte_counters[k][ciphertext[j + k] ^ keystream_guess[j + k]] += 1
    recovered_cookie = best_cookie_guess(byte_counters)
    print(repr(recovered_cookie.decode(errors="replace")))
    assert recovered_cookie == cookie


class ChallengeNotFoundError(ValueError):
    pass


def get_challenges(challenge_nums):
    result = []
    for num in challenge_nums:
        fn = globals().get("challenge" + str(num))
        if not callable(fn):
            raise ChallengeNotFoundError("challenge {} not found".format(num))
        result.append(fn)
    return result


def get_all_challenges():
    challenges = {}
    for name, var in globals().items():
        try:
            num = int(re.findall(r"^challenge(\d+)$", name)[0])
        except IndexError:
            pass
        else:
            if callable(var):
                challenges[num] = var
    return [challenges[num] for num in sorted(challenges)]


def main():
    parser = ArgumentParser(description="Solve the Cryptopals crypto challenges.")
    parser.add_argument(
        "challenges", nargs="*",
        help="Challenge(s) to run. If not specified, all challenges will be run.")
    parser.add_argument(
        "-p", "--profile", help="Profile challenges.", action="store_true")
    parser.add_argument(
        "-q", "--quiet", help="Don't show challenge output.", action="store_true")
    parser.add_argument(
        "-d", "--dummy-server",
        help="Use faster and more reliable dummy server for timing attacks instead of "
             "actual web server", action="store_true")
    args = parser.parse_args()
    try:
        challenges = get_challenges(args.challenges) or get_all_challenges()
    except ChallengeNotFoundError as e:
        parser.error(e)

    profile = cProfile.Profile() if args.profile else None
    try:
        with open(os.devnull, "w") as null_stream:
            output_stream = null_stream if args.quiet else sys.stdout
            for challenge in challenges:
                num = re.findall(r"^challenge(.+)$", challenge.__name__)[0]
                print("Running challenge {}: {}".format(num, challenge.__doc__))
                try:
                    challenge_args = {name: value for name, value in vars(args).items()
                                      if name in inspect.signature(challenge).parameters}
                    with redirect_stdout(output_stream):
                        if profile:
                            profile.runcall(challenge, **challenge_args)
                        else:
                            challenge(**challenge_args)
                except Exception:
                    traceback.print_exc()
                else:
                    print("Challenge {} passed.".format(num))
    finally:
        if profile:
            print()
            profile.print_stats(sort="cumulative")


if __name__ == "__main__":
    main()
