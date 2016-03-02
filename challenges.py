#!/usr/bin/env python3

import base64
import cProfile
import os
import pprint
import re
import sys

from Crypto.Cipher import AES
from collections import Counter, defaultdict
from copy import copy
from fractions import gcd
from itertools import cycle, zip_longest
from random import SystemRandom
from urllib.parse import parse_qs, urlencode

random = SystemRandom()

printer = pprint.PrettyPrinter(width=120)
pp = printer.pprint

ALL_BYTES = [bytes([i]) for i in range(256)]

def hex_to_base64(hex_string):
    return base64.b64encode(bytes.fromhex(hex_string))


def bytes_to_string(b):
    return b.decode("utf-8", errors="replace")


def xor_bytes(bytes1, bytes2):
    if len(bytes1) != len(bytes2):
        raise ValueError("strings must be of equal length")
    return bytes(a ^ b for a, b in zip(bytes1, bytes2))


def xor_encrypt(input_bytes, key):
    return bytes(a ^ b for a, b in zip(input_bytes, cycle(key)))


def edit_distance(bytes1, bytes2):
    result = 0
    for byte1, byte2 in zip(bytes1, bytes2):
        result += sum(1 for i in range(8) if byte1 & (1 << i) != byte2 & (1 << i))
    return result


def byte_chunks(input_bytes, chunk_size=16):
    return [input_bytes[i : i + chunk_size]
        for i in range(0, len(input_bytes), chunk_size)]


def english_like_score(text):
    # Character frequencies taken from raw letter averages at
    # http://www.macfreek.nl/memory/Letter_Distribution, then rounded to
    # 6 decimal places for readability.
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
        # Number 5.4e-4 was empirically observed to produce the best
        # ratio of score for English text to score for incorrectly
        # decrypted text.
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
    # TODO: use birthday paradox to calculate an estimate for the
    # expected number of duplicate blocks so this function works on big
    # ciphertexts.
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


def create_random_aes_key():
    return os.urandom(16)


def encrypt_with_random_key_and_random_mode(plain_bytes):
    key = create_random_aes_key()
    mode = random.choice([AES.MODE_CBC, AES.MODE_ECB])
    # iv is ignored for MODE_ECB
    iv = os.urandom(16)
    prefix = os.urandom(random.randint(5, 10))
    suffix = os.urandom(random.randint(5, 10))
    bytes_to_encrypt = pkcs7_pad(prefix + plain_bytes + suffix)
    return (AES.new(key, mode, iv).encrypt(bytes_to_encrypt), mode)


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


def create_encrypted_user_profile(email_address, cipher):
    profile_data = [("email", email_address), ("uid", "10"), ("role", "user")]
    return cipher.encrypt(pkcs7_pad(urlencode(profile_data).encode("utf-8")))


def decrypt_profile(encrypted_profile, cipher):
    return bytes_to_string(pkcs7_unpad(cipher.decrypt(encrypted_profile)))


def challenge1():
    """Convert hex to base64"""
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
    assert edit_distance(b"this is a test", b"wokka wokka!!!") == 37
    cipher_bytes = base64.b64decode(open("6.txt").read())
    edit_distances = {}
    test_chunk_count = 10
    for key_size in range(2, 41):
        chunks = byte_chunks(cipher_bytes, key_size)
        edit_distances[key_size] = 0
        for i in range(test_chunk_count):
            edit_distances[key_size] += edit_distance(chunks[i], chunks[i + 1])
        edit_distances[key_size] /= key_size
    key_sizes = sorted(edit_distances, key=lambda key_size: edit_distances[key_size])
    best_key_size = key_sizes[0]

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
    iv = bytes([0] * 16)

    plain_bytes = AES.new("YELLOW SUBMARINE", AES.MODE_CBC, iv).decrypt(cipher_bytes)
    assert b"white boy" in plain_bytes
    # Create new cipher object because using cipher object messes up
    # internal IV state
    cbc_result = AES.new("YELLOW SUBMARINE", AES.MODE_CBC, iv).encrypt(plain_bytes)
    assert cbc_result == cipher_bytes

    last_cipher_chunk = iv
    cipher = AES.new("YELLOW SUBMARINE", AES.MODE_ECB, iv)
    result = bytearray()
    for plain_chunk in byte_chunks(plain_bytes):
        combined_chunk = xor_bytes(last_cipher_chunk, plain_chunk)
        cipher_chunk = cipher.encrypt(combined_chunk)
        result.extend(cipher_chunk)
        last_cipher_chunk = cipher_chunk
    assert result == cipher_bytes


def challenge11():
    """An ECB/CBC detection oracle"""
    # hamlet.txt from http://erdani.com/tdpl/hamlet.txt
    # This seems to work perfectly when encrypting 2923 or more bytes of
    # hamlet.txt, but frequently guesses incorrectly with 2922 bytes or
    # fewer. Different files produce different results but for any given
    # file, there seems to be a precise amount of data at which this
    # function works reliably, and below which it frequently thinks ECB
    # is CBC.
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

    def call_oracle(attacker_bytes):
        return cipher.encrypt(pkcs7_pad(attacker_bytes + unknown_bytes))

    assert appears_to_produce_ecb(call_oracle)
    block_size = guess_block_size(call_oracle)
    assert block_size == 16

    plaintext = bytearray()
    while True:
        short_input_block = b"A" * ((block_size - len(plaintext) - 1) % block_size)
        short_block_output = call_oracle(short_input_block)
        block_index = len(plaintext) // block_size
        block_to_look_for = byte_chunks(short_block_output)[block_index]
        for test_byte in ALL_BYTES:
            test_input = short_input_block + plaintext + test_byte
            output = call_oracle(test_input)
            telltale_chunk = byte_chunks(output)[block_index]
            if telltale_chunk == block_to_look_for:
                plaintext += test_byte
                break
        else:
            # if no byte matches
            break
    plaintext = pkcs7_unpad(plaintext)
    print(bytes_to_string(plaintext))
    assert plaintext == unknown_bytes


def challenge13():
    """ECB cut-and-paste"""
    cipher = AES.new(create_random_aes_key(), mode=AES.MODE_ECB)

    profile1 = create_encrypted_user_profile("peter.gregory@piedpiper.com", cipher)
    profile1_chunks = byte_chunks(profile1)

    profile2 = create_encrypted_user_profile("zach.woods@piedpiper.comadmin", cipher)
    profile2_chunks = byte_chunks(profile2)

    profile3 = create_encrypted_user_profile("a@a.com", cipher)
    padding_only_chunk = byte_chunks(profile3)[-1]

    new_profile = b"".join(profile1_chunks[:3]) + profile2_chunks[2] + padding_only_chunk
    decrypted_new_profile = decrypt_profile(new_profile, cipher)
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

    def call_oracle(attacker_bytes):
        return cipher.encrypt(pkcs7_pad(random_bytes + attacker_bytes + target_bytes))

    assert appears_to_produce_ecb(call_oracle)
    block_size = guess_block_size(call_oracle)
    assert block_size == 16

    chunks = byte_chunks(call_oracle(b"A" * 3*block_size))
    attacker_block, attacker_block_count = Counter(chunks).most_common(1)[0]
    assert attacker_block_count >= 2
    attacker_block_pos = block_size * chunks.index(attacker_block)
    for i in range(block_size):
        chunks = byte_chunks(call_oracle(b"A" * (3*block_size - i - 1)))
        if Counter(chunks)[attacker_block] < attacker_block_count:
            prefix_length = attacker_block_pos - (-i % block_size)
            break
    # TODO: make prefix_length calculation work reliably even if
    # attacker bytes look like random bytes or target bytes.

    plaintext = bytearray()
    while True:
        short_block_length = (block_size - len(plaintext) - 1 - prefix_length) % block_size
        short_input_block = b"A" * short_block_length
        short_block_output = call_oracle(short_input_block)
        block_index = (len(plaintext) + prefix_length) // block_size
        block_to_look_for = byte_chunks(short_block_output)[block_index]
        for test_byte in ALL_BYTES:
            test_input = short_input_block + plaintext + test_byte
            output = call_oracle(test_input)
            telltale_chunk = byte_chunks(output)[block_index]
            if telltale_chunk == block_to_look_for:
                plaintext += test_byte
                break
        else:
            # if no byte matches
            break
    plaintext = pkcs7_unpad(plaintext)
    assert plaintext == target_bytes


def test_all_challenges():
    challenges = {}
    for name, var in globals().copy().items():
        try:
            num = int(re.findall("challenge(\d+)", name)[0])
        except (IndexError, ValueError):
            pass
        else:
            if callable(var):
                challenges[num] = var
    old_stdout = sys.stdout
    sys.stdout = open(os.devnull, "w")
    new_printer = copy(printer)
    printer._stream = sys.stdout
    for num in sorted(challenges):
        print("running challenge {}".format(num), file=old_stdout)
        challenges[num]()
    sys.stdout = old_stdout


if __name__ == "__main__":
    try:
        challenge = globals()["challenge" + sys.argv[1]]
    except IndexError:
        test_all_challenges()
        # cProfile.run("test_all_challenges()", sort="cumtime")
    else:
        challenge()
        # cProfile.run("challenge()", sort="cumtime")
