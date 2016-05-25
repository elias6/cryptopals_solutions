#!/usr/bin/env python3

# standard library modules
import base64
import cProfile
import os
import pprint as pprint_module
import re
import struct
import traceback
import warnings

from argparse import ArgumentParser
from collections import Counter
from contextlib import ExitStack, redirect_stdout
from hashlib import sha256
from heapq import nlargest
from itertools import combinations
from sys import stdout
from threading import Thread
from time import time
from urllib.parse import parse_qs, quote as url_quote, urlencode


# third-party modules
from Crypto.Cipher import AES
from md4 import MD4
from sha1.sha1 import Sha1Hash


# modules in this project
import diffie_hellman
import english
import rsa
import srp

from block_cipher import (crack_ecb_oracle, ctr_counter, ctr_iterator, guess_block_size,
    looks_like_ecb, random_aes_key)
from mersenne_twister import MT19937_RNG
from timing_server import (TimingServer, make_insecure_compare_fn, recover_signature,
    server_approves_of_signature)
from util import (IETF_PRIME, big_int_cube_root, chunks, gcd, get_hmac, int_to_bytes,
    mod_inv, pkcs7_pad, pkcs7_unpad, random, sha1, sliding_pairs, xor_bytes, xor_encrypt)


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
    bytes_to_encrypt = pkcs7_pad(query_string.encode("utf-8"))
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
    score_data = english.iter_score_data(ciphertext)
    best_data = nlargest(5, score_data, key=lambda x: x["score"])
    pprint(best_data)
    print(best_data[0]["message"].decode())
    assert best_data[0]["message"] == b"Cooking MC's like a pound of bacon"


def challenge4():
    """Detect single-character XOR"""
    with open("4.txt") as f:
        ciphertexts = [bytes.fromhex(line.strip()) for line in f.readlines()]
    decoded_string_data = enumerate(english.best_score_data(c) for c in ciphertexts)
    best_decodings = nlargest(3, decoded_string_data, key=lambda d: d[1]["score"])
    pprint(best_decodings)
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
        data_chunks = chunks(data, key_size)
        result = 0
        for i in range(len(data_chunks) - 1):
            result += hamming_distance(data_chunks[i], data_chunks[i + 1])
        return result / key_size / len(data_chunks)

    assert hamming_distance(b"this is a test", b"wokka wokka!!!") == 37

    with open("6.txt") as f:
        ciphertext = base64.b64decode(f.read())

    best_key_size = min(range(2, 41), key=lambda x: index_of_coincidence(ciphertext, x))
    cipher_chunks = chunks(ciphertext, best_key_size)
    plain_chunks, key = english.crack_common_xor_key(cipher_chunks)
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
    pprint(ecb_texts)
    assert len(ecb_texts) == 1


def challenge9():
    """Implement PKCS#7 padding"""
    assert pkcs7_pad(b"YELLOW SUBMARINE", 20) == b"YELLOW SUBMARINE\x04\x04\x04\x04"


def challenge10():
    """Implement CBC mode"""
    def cbc_encrypt(key, iv, plain_bytes):
        cipher = AES.new(key, AES.MODE_ECB, iv)
        last_cipher_block = iv
        result = bytearray()
        for plain_block in chunks(plain_bytes):
            combined_block = xor_bytes(last_cipher_block, plain_block)
            cipher_block = cipher.encrypt(combined_block)
            result.extend(cipher_block)
            last_cipher_block = cipher_block
        return bytes(result)

    def cbc_decrypt(key, iv, ciphertext):
        cipher = AES.new(key, AES.MODE_ECB, iv)
        last_cipher_block = iv
        result = bytearray()
        for cipher_block in chunks(ciphertext):
            decrypted_block = cipher.decrypt(cipher_block)
            plain_block = xor_bytes(last_cipher_block, decrypted_block)
            result.extend(plain_block)
            last_cipher_block = cipher_block
        return bytes(result)

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
    assert looks_like_ecb(oracle_fn(b"A" * 5 * block_size), block_size)

    plaintext = crack_ecb_oracle(oracle_fn, block_size)
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
    profile1_blocks = chunks(profile1)

    profile2 = encrypted_user_profile("zach.woods@piedpiper.comadmin")
    profile2_blocks = chunks(profile2)

    profile3 = encrypted_user_profile("a@a.com")
    padding_only_block = chunks(profile3)[-1]

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
        plaintext = pkcs7_pad(random_bytes + attacker_bytes + target_bytes)
        return cipher.encrypt(plaintext)

    block_size = guess_block_size(oracle_fn)
    assert block_size == 16
    assert looks_like_ecb(oracle_fn(b"A" * 5 * block_size), block_size)

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

    def recover_block(prev_cipher_block, cipher_block):
        result = bytes()
        for pos in reversed(range(16)):
            assert len(result) == 15 - pos
            cipher_slice = prev_cipher_block[pos + 1:]
            padding = bytes([len(result) + 1] * len(result))
            iv_end = xor_bytes(cipher_slice, padding, result)
            new_iv = bytearray(prev_cipher_block[:pos] + b"\x00" + iv_end)
            for guess in english.all_bytes_by_frequency:
                new_iv[pos] = prev_cipher_block[pos] ^ guess ^ (16 - pos)
                if has_valid_padding(new_iv, cipher_block):
                    if pos == 15:
                        new_iv[14] ^= 2
                        if not has_valid_padding(new_iv, cipher_block):
                            continue
                    result = bytes([guess]) + result
                    break
        return result

    # The following code does a padding oracle attack. Details of how it
    # works can be found at
    # https://blog.skullsecurity.org/2013/padding-oracle-attacks-in-depth
    for unknown_string in unknown_strings:
        recovered_plaintext = bytearray()
        cipher_blocks = chunks(iv + encrypt(unknown_string))
        for prev_cipher_block, cipher_block in sliding_pairs(cipher_blocks):
            recovered_plaintext += recover_block(prev_cipher_block, cipher_block)
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

    recovered_plaintexts, recovered_key = english.crack_common_xor_key(ciphertexts)
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
    recovered_plaintexts, recovered_key = english.crack_common_xor_key(ciphertexts)
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
        for chunk in chunks(ciphertext, 4):
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
    hmac_key = os.urandom(16)
    with open("hamlet.txt", "rb") as f:
        data = f.read()
    hmac = get_hmac(hmac_key, data)

    print("looking for {}".format(list(hmac)))
    print()
    server = TimingServer(
        ("localhost", 31415), hmac_key, make_insecure_compare_fn(0.05))
    try:
        Thread(target=server.serve_forever).start()
        print("Server is running on {}".format(server.server_address))
        print()
        signature = recover_signature(
            server_approves_of_signature,
            thread_count=15,
            threshold=0.01,
            attempt_limit=20)
    finally:
        server.shutdown()
        server.server_close()

    assert signature == hmac


def challenge32():
    """Break HMAC-SHA1 with a slightly less artificial timing leak"""
    hmac_key = os.urandom(16)
    with open("hamlet.txt", "rb") as f:
        data = f.read()
    hmac = get_hmac(hmac_key, data)

    print("looking for {}".format(list(hmac)))
    print()
    server = TimingServer(
        ("localhost", 31415), hmac_key, make_insecure_compare_fn(0.025))
    try:
        Thread(target=server.serve_forever).start()
        print("Server is running on {}".format(server.server_address))
        print()
        signature = recover_signature(
            server_approves_of_signature,
            thread_count=15,
            threshold=0.006,
            attempt_limit=20)
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
        hmac = get_hmac(shared_session_key, salt, sha256)
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
    # This is equivalent to padding with block type 0. rsa.unpad is needed
    # to properly recover the plaintext.
    plaintext = rsa.unpad(rsa.decrypt(ciphertext, private_key))
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
    # rsa.encrypt left-pads its result to make it as long as the modulus.
    # This is equivalent to padding with block type 0. rsa.unpad is needed
    # to properly recover the plaintext.
    plaintext = rsa.unpad(decrypt(ciphertext))
    try:
        decrypt(ciphertext)
    except AccessDeniedError:
        pass
    else:
        assert False

    cipher_int = int.from_bytes(ciphertext, byteorder="big")
    modulus = public_key.modulus
    random_number = random.randint(2, modulus - 1)
    modified_cipher_int = (cipher_int * random_number**public_key.exponent) % modulus
    modified_ciphertext = int_to_bytes(modified_cipher_int)
    oracle_int = int.from_bytes(decrypt(modified_ciphertext), byteorder="big")
    recovered_plain_int = (oracle_int * mod_inv(random_number, modulus)) % modulus
    recovered_plaintext = int_to_bytes(recovered_plain_int)
    assert recovered_plaintext == plaintext


def test_all_challenges(output_stream=stdout):
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
    parser = ArgumentParser(description="Solve the Matasano crypto challenges.")
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
        real_stdout = stdout
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
