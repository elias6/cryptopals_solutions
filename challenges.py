#!/usr/bin/env python3

# standard library modules
import base64
import cProfile
import gzip
import os
import pprint as pprint_module
import re
import struct
import traceback
import warnings

from argparse import ArgumentParser
from collections import Counter, defaultdict
from contextlib import ExitStack, redirect_stdout
from hashlib import sha1, sha256
from heapq import nlargest
from itertools import combinations, count, product, repeat
from math import ceil, gcd
from sys import stdout
from threading import Thread
from time import time
from urllib.parse import parse_qs, quote as url_quote, urlencode


# third-party modules
from Crypto.Cipher import AES
from md4 import MD4
from sha1.sha1 import Sha1Hash as PurePythonSha1


# modules in this project
import diffie_hellman
import dsa
import english
import merkle_damgard
import mersenne_twister
import rsa
import srp
import timing_attack

from block_tools import (crack_ecb_oracle, ctr_counter, ctr_iterator, guess_block_size,
    looks_like_ecb, pkcs7_pad, pkcs7_padding_is_valid, pkcs7_unpad, random_aes_key)
from mersenne_twister import MT19937_RNG
from util import (IETF_PRIME, big_int_cube_root, calculate_hmac, chunks, int_to_bytes,
    mod_inv, pretty_hex_bytes, random, xor_bytes, xor_encrypt)


warnings.simplefilter("default", BytesWarning)
warnings.simplefilter("default", ResourceWarning)
warnings.simplefilter("default", DeprecationWarning)

EXAMPLE_PLAIN_BYTES = (b"Give a man a beer, he'll waste an hour. "
    b"Teach a man to brew, he'll waste a lifetime.")


def pprint(*args, width=120, **kwargs):
    pprint_module.pprint(*args, width=width, **kwargs)


def encrypted_query_string(cipher, user_data):
    query_string = ("comment1=cooking%20MCs;userdata=" + url_quote(user_data) +
        ";comment2=%20like%20a%20pound%20of%20bacon")
    bytes_to_encrypt = pkcs7_pad(query_string.encode())
    return cipher.encrypt(bytes_to_encrypt)


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
    score_data = english.iter_xor_score_data(ciphertext)
    best_data = nlargest(5, score_data, key=lambda x: x["score"])
    pprint(best_data)
    print(best_data[0]["message"].decode())
    assert best_data[0]["message"] == b"Cooking MC's like a pound of bacon"


def challenge4():
    """Detect single-character XOR"""
    with open("text_files/4.txt") as f:
        ciphertexts = [bytes.fromhex(line.strip()) for line in f.readlines()]
    decoded_string_data = enumerate(english.best_score_data(c) for c in ciphertexts)
    best_decodings = nlargest(3, decoded_string_data, key=lambda d: d[1]["score"])
    pprint(best_decodings)
    assert best_decodings[0][1]["message"] == b"Now that the party is jumping\n"


def challenge5():
    """Implement repeating-key XOR"""
    stanza = ("Burning 'em, if you ain't quick and nimble\n"
        "I go crazy when I hear a cymbal")
    result = xor_encrypt(stanza.encode(), b"ICE").hex()
    assert result == ("0b3637272a2b2e63622c2e69692a23693a2a3c6324202d623d63343"
        "c2a26226324272765272a282b2f20430a652e2c652a3124333a653e2b2027630c692b"
        "20283165286326302e27282f")
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
    key = english.crack_common_xor_key(chunks(ciphertext, best_key_size))
    plaintext = xor_encrypt(ciphertext, key).decode()
    print("key: {}".format(key.decode()))
    print()
    print(plaintext)
    assert "white boy" in plaintext


def challenge7():
    """AES in ECB mode"""
    with open("text_files/7.txt") as f:
        ciphertext = base64.b64decode(f.read())
    message = AES.new(b"YELLOW SUBMARINE", AES.MODE_ECB).decrypt(ciphertext)
    print(message.decode())
    assert b"white boy" in message


def challenge8():
    """Detect AES in ECB mode"""
    with open("text_files/8.txt") as f:
        ciphertexts = [bytes.fromhex(line.strip()) for line in f.readlines()]
    ecb_texts = []
    for i, ciphertext in enumerate(ciphertexts, start=1):
        if looks_like_ecb(ciphertext):
            ecb_texts.append(ciphertext)
            print("ECB-like ciphertext found on line {}".format(i))
            pprint([pretty_hex_bytes(x) for x in chunks(ciphertext)])
    assert len(ecb_texts) == 1


def challenge9():
    """Implement PKCS#7 padding"""
    assert pkcs7_pad(b"YELLOW SUBMARINE", 20) == b"YELLOW SUBMARINE\x04\x04\x04\x04"


def challenge10():
    """Implement CBC mode"""
    def cbc_encrypt(key, iv, plain_bytes):
        result = bytearray()
        prev_cipher_block = iv
        for plain_block in chunks(plain_bytes):
            combined_block = xor_bytes(prev_cipher_block, plain_block)
            cipher_block = AES.new(key, AES.MODE_ECB).encrypt(combined_block)
            result.extend(cipher_block)
            prev_cipher_block = cipher_block
        return bytes(result)

    def cbc_decrypt(key, iv, ciphertext):
        result = bytearray()
        prev_cipher_block = iv
        for cipher_block in chunks(ciphertext):
            decrypted_block = AES.new(key, AES.MODE_ECB).decrypt(cipher_block)
            plain_block = xor_bytes(prev_cipher_block, decrypted_block)
            result.extend(plain_block)
            prev_cipher_block = cipher_block
        return bytes(result)

    with open("text_files/10.txt") as f:
        ciphertext = base64.b64decode(f.read())
    key = b"YELLOW SUBMARINE"
    iv = b"\x00" * 16

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
        mode = random.choice(["MODE_CBC", "MODE_ECB"])
        # iv is ignored for MODE_ECB
        iv = os.urandom(16)
        prefix = os.urandom(random.randint(5, 10))
        suffix = os.urandom(random.randint(5, 10))
        bytes_to_encrypt = pkcs7_pad(prefix + plain_bytes + suffix)
        return (AES.new(key, getattr(AES, mode), iv).encrypt(bytes_to_encrypt), mode)

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
        apparent_mode = "MODE_ECB" if looks_like_ecb(ciphertext) else "MODE_CBC"
        assert mode == apparent_mode


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
    assert looks_like_ecb(oracle_fn(b"A" * 100), block_size)

    plaintext = crack_ecb_oracle(oracle_fn, block_size)
    print(plaintext.decode())
    assert plaintext == unknown_bytes


def challenge13():
    """ECB cut-and-paste"""
    cipher = AES.new(random_aes_key(), mode=AES.MODE_ECB)

    def encrypted_user_profile(email_address):
        profile_data = [("email", email_address), ("uid", "10"), ("role", "user")]
        return cipher.encrypt(pkcs7_pad(urlencode(profile_data).encode()))

    def decrypt_profile(encrypted_profile):
        return pkcs7_unpad(cipher.decrypt(encrypted_profile)).decode()

    profile1 = encrypted_user_profile("peter.gregory@piedpiper.com")
    profile1_blocks = chunks(profile1)

    profile2 = encrypted_user_profile("zach.woods@piedpiper.comadmin")
    profile2_blocks = chunks(profile2)

    profile3 = encrypted_user_profile("a@a.com")
    padding_only_block = chunks(profile3)[-1]

    new_profile = b"".join(profile1_blocks[:3]) + profile2_blocks[2] + padding_only_block
    decrypted_new_profile = decrypt_profile(new_profile)
    assert parse_qs(decrypted_new_profile)["role"] == ["admin"]
    print(decrypted_new_profile)


def challenge14():
    """Byte-at-a-time ECB decryption (Harder)"""
    cipher = AES.new(random_aes_key(), AES.MODE_ECB)
    random_bytes = os.urandom(random.randint(0, 64))
    target_bytes = EXAMPLE_PLAIN_BYTES

    def oracle_fn(attacker_bytes):
        plaintext = pkcs7_pad(random_bytes + attacker_bytes + target_bytes)
        return cipher.encrypt(plaintext)

    block_size = guess_block_size(oracle_fn)
    assert block_size == 16
    assert looks_like_ecb(oracle_fn(b"A" * 100), block_size)

    blocks = chunks(oracle_fn(b"A" * 3*block_size))
    attacker_block, attacker_block_count = Counter(blocks).most_common(1)[0]
    assert attacker_block_count >= 2
    attacker_block_pos = block_size * blocks.index(attacker_block)
    for i in range(block_size):
        blocks = chunks(oracle_fn(b"A" * (3*block_size - i - 1)))
        if blocks.count(attacker_block) < attacker_block_count:
            prefix_length = attacker_block_pos - (-i % block_size)
            break
    # TODO: make prefix_length calculation work reliably even if attacker
    # bytes look like random bytes or target bytes.

    plaintext = crack_ecb_oracle(oracle_fn, block_size, prefix_length)
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

    key = random_aes_key()

    def encrypt(plaintext):
        iv = os.urandom(16)
        return (iv, AES.new(key, AES.MODE_CBC, iv).encrypt(pkcs7_pad(plaintext)))

    def has_valid_padding(iv, ciphertext):
        plain_bytes = AES.new(key, AES.MODE_CBC, bytes(iv)).decrypt(ciphertext)
        return pkcs7_padding_is_valid(plain_bytes)

    def recover_plain_byte(prev_cipher_block, cipher_block, recovered_so_far):
        block_size = len(cipher_block)
        pos = block_size - len(recovered_so_far) - 1
        padding = bytes([len(recovered_so_far) + 1]) * (len(recovered_so_far) + 1)
        test_iv = bytearray(xor_bytes(
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
        for cipher_block in chunks(ciphertext):
            result += recover_plain_block(prev_cipher_block, cipher_block)
            prev_cipher_block = cipher_block
        return pkcs7_unpad(result)

    for plaintext in plaintexts:
        iv, ciphertext = encrypt(plaintext)
        recovered_plaintext = crack_padding_oracle(iv, ciphertext)
        assert recovered_plaintext == plaintext
        print(recovered_plaintext.decode())


def challenge18():
    """Implement CTR, the stream cipher mode"""
    ciphertext = base64.b64decode("L77na/nrFsKvynd6HzOoG7GHTLXsTVu9qvY/"
        "2syLXzhPweyyMTJULu/6/kXX0KSvoOLSFQ==")
    key = b"YELLOW SUBMARINE"
    ecb_cipher = AES.new(key, AES.MODE_ECB)
    nonce = 0

    plaintext = bytearray()
    for counter_value, block in zip(ctr_iterator(nonce), chunks(ciphertext)):
        keystream = ecb_cipher.encrypt(counter_value)
        plaintext += xor_bytes(keystream[:len(block)], block)
    print(plaintext.decode())

    ctr_cipher = AES.new(key, AES.MODE_CTR, counter=ctr_counter(nonce))
    assert plaintext == ctr_cipher.decrypt(ciphertext)


def challenge19():
    """Break fixed-nonce CTR mode using substitutions"""
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

    recovered_key = english.crack_common_xor_key(ciphertexts)
    print("\n".join(xor_encrypt(c, recovered_key).decode() for c in ciphertexts))


def challenge20():
    """Break fixed-nonce CTR statistically"""
    key = random_aes_key()

    def encrypt(ciphertext):
        cipher = AES.new(key, AES.MODE_CTR, counter=ctr_counter(0))
        return cipher.encrypt(ciphertext)

    with open("text_files/20.txt") as f:
        plaintexts = [base64.b64decode(x) for x in f.readlines()]
    ciphertexts = [encrypt(x) for x in plaintexts]
    recovered_key = english.crack_common_xor_key(ciphertexts)
    print("\n".join(xor_encrypt(c, recovered_key).decode() for c in ciphertexts))


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
    rng2.buffer = [mersenne_twister.untemper(x) for x in numbers]
    rng2.index = 0
    numbers2 = [rng2.get_number() for _ in range(624)]
    assert numbers == numbers2


def challenge24():
    """Create the MT19937 stream cipher and break it"""
    def encrypt_with_rng(rng, ciphertext):
        result = bytearray()
        for chunk in chunks(ciphertext, 4):
            # Create 4-byte chunk from rng
            keystream_bytes = struct.pack(">L", rng.get_number())
            result += xor_bytes(chunk, keystream_bytes[:len(chunk)])
        return bytes(result)

    def encrypt_with_random_prefix(rng, plain_bytes):
        prefix = os.urandom(random.randint(0, 64))
        return encrypt_with_rng(rng, prefix + plain_bytes)

    seed = random.getrandbits(16)
    test_ciphertext = encrypt_with_rng(MT19937_RNG(seed), EXAMPLE_PLAIN_BYTES)
    test_plaintext = encrypt_with_rng(MT19937_RNG(seed), test_ciphertext)
    assert test_plaintext == EXAMPLE_PLAIN_BYTES

    seed = random.getrandbits(16)
    my_bytes = b"A" * 14
    ciphertext = encrypt_with_random_prefix(MT19937_RNG(seed), my_bytes)
    cipher_chunks = chunks(ciphertext, 4)
    # Get bytes from last 2 chunks, excluding last chunk, which may not have
    # 4 bytes, and therefore may not allow me to determine the keystream
    # numbers.
    ciphertext_with_my_bytes = b"".join(cipher_chunks[-3:-1])
    keystream = xor_encrypt(ciphertext_with_my_bytes, b"A")
    keystream_numbers = struct.unpack(">LL", keystream)
    untempered_numbers = [mersenne_twister.untemper(x) for x in keystream_numbers]

    for seed_guess in range(2**16):
        if seed_guess % 5000 == 0:
            print("tried {} seeds".format(seed_guess))
        test_rng = MT19937_RNG(seed_guess)
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
    with open("text_files/25.txt") as f:
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
        # If plaintext has any non-ASCII bytes, raise exception, else do nothing
        AES.new(key, AES.MODE_CBC, iv).decrypt(ciphertext).decode("ascii")

    ciphertext = encrypt(EXAMPLE_PLAIN_BYTES)
    modified_ciphertext = ciphertext[:16] + bytes([0] * 16) + ciphertext

    try:
        decrypt(modified_ciphertext)
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
    their_padding = PurePythonSha1().update(EXAMPLE_PLAIN_BYTES)._produce_padding()
    assert their_padding == my_padding

    key = os.urandom(16)
    query_string = (b"comment1=cooking%20MCs;userdata=foo;"
        b"comment2=%20like%20a%20pound%20of%20bacon")
    mac = sha1(key + query_string).digest()

    glue_padding = sha1_padding(len(key + query_string))
    new_param = b";admin=true"
    modified_hash_fn = PurePythonSha1(
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
    hmac_key = os.urandom(16)
    filename = "text_files/hamlet.txt"
    with open(filename, "rb") as f:
        hmac = calculate_hmac(hmac_key, f.read())
    print("looking for {}\n".format(pretty_hex_bytes(hmac)))

    def compare_sigs(a, b):
        return timing_attack.insecure_compare(a, b, delay=0.05)

    server_address = ("localhost", 31415)

    def validate_signature(sig):
        return timing_attack.server_approves_of_signature(server_address, filename, sig)

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


def challenge32():
    """Break HMAC-SHA1 with a slightly less artificial timing leak"""
    hmac_key = os.urandom(16)
    filename = "text_files/hamlet.txt"
    with open(filename, "rb") as f:
        hmac = calculate_hmac(hmac_key, f.read())
    print("looking for {}\n".format(pretty_hex_bytes(hmac)))

    def compare_sigs(a, b):
        return timing_attack.insecure_compare(a, b, delay=0.025)

    server_address = ("localhost", 31415)

    def validate_signature(sig):
        return timing_attack.server_approves_of_signature(server_address, filename, sig)

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
    assert EXAMPLE_PLAIN_BYTES in bob._decrypted_messages[alice]

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
    assert EXAMPLE_PLAIN_BYTES in mallory._decrypted_messages[alice]
    mallory.send_echo_request(bob, EXAMPLE_PLAIN_BYTES)
    assert EXAMPLE_PLAIN_BYTES in bob._decrypted_messages[mallory]


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
    assert EXAMPLE_PLAIN_BYTES in mallory._decrypted_messages[alice]
    mallory.send_echo_request(bob, EXAMPLE_PLAIN_BYTES)
    assert EXAMPLE_PLAIN_BYTES in bob._decrypted_messages[mallory]

    # Mallory tricks Alice and Bob into using g=IETF_PRIME
    alice = diffie_hellman.User(g=IETF_PRIME)
    bob = diffie_hellman.User(g=IETF_PRIME)
    mallory = diffie_hellman.User(g=IETF_PRIME)
    assert mallory.public_key == 0
    assert alice.get_shared_key_for(mallory) == 0
    assert bob.get_shared_key_for(mallory) == 0
    alice.send_echo_request(mallory, EXAMPLE_PLAIN_BYTES)
    # Mallory decrypts request without real key.
    assert EXAMPLE_PLAIN_BYTES in mallory._decrypted_messages[alice]
    mallory.send_echo_request(bob, EXAMPLE_PLAIN_BYTES)
    assert EXAMPLE_PLAIN_BYTES in bob._decrypted_messages[mallory]

    # Mallory tricks Alice and Bob into using g=IETF_PRIME - 1
    alice = diffie_hellman.User(g=IETF_PRIME - 1)
    bob = diffie_hellman.User(g=IETF_PRIME - 1)
    # Private key must be even.
    mallory = diffie_hellman.User(g=IETF_PRIME - 1,
        private_key=random.randrange(0, IETF_PRIME, 2))
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
        salt, _, _ = server._respond_to_login_request(username, i * IETF_PRIME)
        # Attacker derives shared session key without password
        shared_session_key = sha256(int_to_bytes(0)).digest()
        hmac = calculate_hmac(shared_session_key, salt, sha256)
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
    assert mod_inv(17, 3120) == 2753

    public_key, private_key = rsa.generate_key_pair()

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
        public_key, _ = rsa.generate_key_pair()
        ciphertext = rsa.encrypt(EXAMPLE_PLAIN_BYTES, public_key)
        ciphertext_data.append({
            "modulus": public_key.modulus,
            "cipher_int": int.from_bytes(ciphertext, byteorder="big"),
        })
        modulus_product *= public_key.modulus

    assert all(gcd(x["modulus"], y["modulus"]) == 1
        for x, y in combinations(ciphertext_data, 2))

    cube = 0
    for x in ciphertext_data:
        m_s_ = 1    # strange name picked for similarity to notation in challenge
        for y in ciphertext_data:
            if x != y:
                m_s_ *= y["modulus"]
        cube += x["cipher_int"] * m_s_ * mod_inv(m_s_, x["modulus"])
    cube %= modulus_product
    assert all(x["cipher_int"] == cube % x["modulus"] for x in ciphertext_data)

    root = round(big_int_cube_root(cube))
    assert root ** 3 == cube
    plaintext = int_to_bytes(root)
    assert plaintext == EXAMPLE_PLAIN_BYTES


def challenge41():
    """Implement unpadded message recovery oracle"""
    seen_message_hashes = set()
    public_key, private_key = rsa.generate_key_pair()

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
    recovered_plaintext = rsa.multiply(oracle_plaintext, mod_inv(S, modulus), modulus)
    assert recovered_plaintext == plaintext


def challenge42():
    """Bleichenbacher's e=3 RSA Attack"""
    # aka BERserk
    # Details about how this works can be found at the following URLs:
    # https://www.ietf.org/mail-archive/web/openpgp/current/msg00999.html
    # http://www.withouthat.org/~sid/me/wp-content/uploads/2008/09/document.pdf
    modulus_length = 128
    public_key, private_key = rsa.generate_key_pair(bit_length=modulus_length * 8)

    message = b"hi mom"

    ciphertext = rsa.pad_and_encrypt(message, public_key)
    assert rsa.unpad(rsa.decrypt(ciphertext, private_key)) == message

    sig = rsa.sign(message, private_key)
    assert rsa.verify(message, public_key, sig)

    digest_info = rsa.create_digest_asn1(message)
    padded_sig = rsa.pad(digest_info, len(digest_info) + 11, block_type=1)
    sig_block = padded_sig.ljust(modulus_length, b"\x00")
    sig_block_int = int.from_bytes(sig_block, byteorder="big")
    forged_sig_int = ceil(big_int_cube_root(sig_block_int))
    forged_sig = forged_sig_int.to_bytes(length=modulus_length, byteorder="big")

    assert rsa.decrypt(forged_sig, public_key).startswith(padded_sig)
    assert not rsa.verify(message, public_key, forged_sig)
    assert rsa.verify(message, public_key, forged_sig, secure=False)


def challenge43():
    """DSA key recovery from nonce"""
    message = EXAMPLE_PLAIN_BYTES
    public_key, private_key = dsa.generate_key_pair()
    sig = dsa.sign(message, private_key)
    assert dsa.verify(message, public_key, sig)

    sig, k = dsa.sign_and_leak_k(message, private_key)
    assert dsa.recover_private_key(k, message, sig) == private_key

    public_key = int("84ad4719d044495496a3201c8ff484feb45b962e7302e56a392aee4ab"
        "ab3e4bdebf2955b4736012f21a08084056b19bcd7fee56048e004e44984e2f411788ef"
        "dc837a0d2e5abb7b555039fd243ac01f0fb2ed1dec568280ce678e931868d23eb095fd"
        "e9d3779191b8c0299d6e07bbb283e6633451e535c45513b2d33c99ea17", 16)
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
    for message1, message2 in combinations(messages, 2):
        if message1["sig"].r == message2["sig"].r:
            s_diff_inverse = mod_inv(message1["sig"].s - message2["sig"].s, dsa.q)
            k = ((message1["hash"] - message2["hash"]) * s_diff_inverse) % dsa.q
            guess1 = dsa.recover_private_key(k, message1["message"], message1["sig"])
            guess2 = dsa.recover_private_key(k, message2["message"], message2["sig"])
            assert guess1 == guess2
            public_key = int("2d026f4bf30195ede3a088da85e398ef869611d0f68f0713d"
                "51c9c1a3a26c95105d915e2d8cdf26d056b86b8a7b85519b1c23cc3ecdc606"
                "2650462e3063bd179c2a6581519f674a61f1d89a1fff27171ebc1b93d4dc57"
                "bceb7ae2430f98a6a4d83d8279ee65d71c1203d2c96d65ebbf7cce9d32971c"
                "3de5084cce04a2e147821", 16)
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
    public_key, private_key = dsa.generate_key_pair()

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
        s = (r * mod_inv(z, dsa.q)) % dsa.q
        magic_sig = dsa.Signature(r, s)
        assert dsa.verify(b"Hello world", public_key, magic_sig, g=bad_g)
        assert dsa.verify(b"Goodbye, world", public_key, magic_sig, g=bad_g)


def challenge46():
    """RSA parity oracle"""
    public_key, private_key = rsa.generate_key_pair()

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
    public_key, private_key = rsa.generate_key_pair(bit_length=256)

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
    public_key, private_key = rsa.generate_key_pair(bit_length=768)

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
    key = random_aes_key()
    block_size = 16

    def transaction_message(from_id, to_id, amount):
        return urlencode([("from", from_id), ("to", to_id), ("amount", amount)]).encode()

    def transaction_list_message(from_id, transactions):
        tx_list = ";".join("{to}:{amount}".format(**tx) for tx in transactions)
        return urlencode([("from", from_id), ("tx_list", tx_list)], safe=":;").encode()

    def message_mac(message, iv=b"\x00"*block_size):
        return AES.new(key, AES.MODE_CBC, iv).encrypt(pkcs7_pad(message))[-block_size:]

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
    attacker_iv = xor_bytes(iv, message1[:block_size], new_block)
    assert request_is_valid(forged_message1, mac1, attacker_iv)

    message2 = transaction_list_message(
        from_id="Roland",
        transactions=[
            {"to": "Lone_Starr", "amount": 248},
            {"to": "Prince_Murray", "amount": 50000}])
    assert message2 == b"from=Roland&tx_list=Lone_Starr:248;Prince_Murray:50000"
    mac2 = message_mac(message2)

    extension = b";Pizza_The_Hutt:1000000"
    modified_extension = xor_bytes(mac2, extension[:block_size]) + extension[block_size:]
    forged_message2 = pkcs7_pad(message2) + extension
    # TODO: try to forge a message without padding in the middle. Also
    # calculate MAC without calculating MAC of modified_extension.
    assert request_is_valid(forged_message2, message_mac(modified_extension))


def challenge50():
    """Hashing with CBC-MAC"""
    key = b"YELLOW SUBMARINE"

    def encrypt(message):
        return AES.new(key, AES.MODE_CBC, IV=b"\x00"*16).encrypt(message)

    def decrypt(message):
        return AES.new(key, AES.MODE_CBC, IV=b"\x00"*16).decrypt(message)

    def mac_hash(message):
        return encrypt(pkcs7_pad(message))[-16:]

    snippet = b"alert('MZA who was that?');\n"
    mac = mac_hash(snippet)
    assert mac.hex() == "296b8d7cb78a243dda4d0a61d33bbdd1"
    print("snippet:\n{}".format(snippet.decode()))

    forged_snippet_begin = b"alert('Ayo, the Wu is back!');\n/****************"
    forged_snippet_end = b"**************/"
    nonsense = xor_bytes(
        decrypt(xor_bytes(pkcs7_pad(forged_snippet_end), decrypt(mac))),
        encrypt(forged_snippet_begin)[-16:]
    )
    forged_snippet = forged_snippet_begin + nonsense + forged_snippet_end
    print("forged snippet:\n{}".format(forged_snippet.decode(errors="replace")))
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
        nonce = random.randint(0, 2**64 - 1)
        cipher = AES.new(random_aes_key(), AES.MODE_CTR, counter=ctr_counter(nonce))
        return len(cipher.encrypt(gzip.compress(format_request(payload))))

    def cbc_oracle_fn(payload):
        cipher = AES.new(random_aes_key(), AES.MODE_CBC, IV=os.urandom(16))
        return len(cipher.encrypt(pkcs7_pad(gzip.compress(format_request(payload)))))

    def crack_compression_oracle(oracle_fn):
        base64_alphabet = [bytes([x]) for x in b"ABCDEFGHIJKLMNOPQRSTUVWXYZ"
            b"abcdefghijklmnopqrstuvwxyz0123456789+/=\n"]
        result = b""
        while True:
            for i in count(start=0):
                prefix = os.urandom(i) + b"sessionid=" + result
                length_map = {x: oracle_fn(prefix + x) for x in base64_alphabet}
                min_length = min(length_map.values())
                good_guesses = [x for x in length_map if length_map[x] == min_length]
                if good_guesses == [b"\n"]:
                    return result
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
    def find_collision(hash_fn, messages, state=None):
        state = state or hash_fn.default_initial_state
        collision_map = defaultdict(set)
        for message in messages:
            message_hash = hash_fn.compress(state, message)
            collision_map[message_hash].add(message)
            if len(collision_map[message_hash]) > 1:
                return (collision_map[message_hash], message_hash)
        raise ValueError("couldn't find collision")

    def find_multiple_collisions(hash_fn, n):
        """Generate 2**n messages, each with length n * hash_fn.block_size, that
        have the same hash. Return a tuple with a list of the messages and the
        hash.
        """
        state = hash_fn.default_initial_state
        block_pairs = []
        infinite_messages = (os.urandom(len(state)) for _ in repeat(None))
        for i in range(n):
            collision, state = find_collision(hash_fn, infinite_messages, state)
            block_pairs.append(collision)
        return ([b"".join(x) for x in product(*block_pairs)], state)

    hash_fn = merkle_damgard.HashFunction(block_size=2)
    n = 10
    colliding_messages, message_hash = find_multiple_collisions(hash_fn, n)
    assert len(colliding_messages) == 2**n
    print("Generated {} messages with hash {}.\n".format(
        len(colliding_messages), pretty_hex_bytes(message_hash)))

    cheap_hash_fn = merkle_damgard.HashFunction(block_size=2)
    expensive_hash_fn = merkle_damgard.HashFunction(block_size=5)
    n = ceil(expensive_hash_fn.block_size * 8 / 2)
    while True:
        cheap_collisions, cheap_hash = find_multiple_collisions(cheap_hash_fn, n)
        try:
            messages, expensive_hash = find_collision(expensive_hash_fn, cheap_collisions)
        except ValueError:
            print("Collision not found, trying again")
        else:
            print("The following messages have combined hash [{}] + [{}]:".format(
                pretty_hex_bytes(cheap_hash), pretty_hex_bytes(expensive_hash)))
            print("\n\n".join(pretty_hex_bytes(m) for m in messages))
            break


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
            num = int(re.findall("^challenge(\d+)$", name)[0])
        except IndexError:
            pass
        else:
            if callable(var):
                challenges[num] = var
    return [challenges[num] for num in sorted(challenges)]


def run_challenges(challenges, output_stream=stdout):
    for challenge in challenges:
        num = re.findall("^challenge(.+)$", challenge.__name__)[0]
        print("Running challenge {}: {}".format(num, challenge.__doc__),
            file=output_stream)
        try:
            challenge()
        except Exception as e:
            traceback.print_exc(file=output_stream)
        else:
            print("Challenge {} passed.".format(num), file=output_stream)


if __name__ == "__main__":
    parser = ArgumentParser(description="Solve the Matasano crypto challenges.")
    parser.add_argument(
        "challenges", nargs="*",
        help="Challenge(s) to run. If not specified, all challenges will be run.")
    parser.add_argument(
        "-p", "--profile", help="Profile challenges.", action="store_true")
    parser.add_argument(
        "-q", "--quiet", help="Don't show challenge output.", action="store_true")
    ARGS = parser.parse_args()
    try:
        challenges = get_challenges(ARGS.challenges) or get_all_challenges()
    except ChallengeNotFoundError as e:
        parser.error(e)
    with ExitStack() as stack:
        if ARGS.profile:
            profile = cProfile.Profile()
            stack.callback(profile.print_stats, sort="cumtime")
        if ARGS.quiet:
            null_stream = open(os.devnull, "w")
            stack.enter_context(null_stream)
            stack.enter_context(redirect_stdout(null_stream))
        if ARGS.profile:
            profile.runcall(run_challenges, challenges)
        else:
            run_challenges(challenges)
