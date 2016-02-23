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
from itertools import cycle, zip_longest
from random import SystemRandom

random = SystemRandom()

printer = pprint.PrettyPrinter(width=120)
pp = printer.pprint

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

def byte_chunks(input_bytes, chunk_size):
    return [input_bytes[i : i + chunk_size] for i in range(0, len(input_bytes), chunk_size)]

def english_like_score(text):
    # Character frequencies from http://www.data-compression.com/english.html
    frequencies = {
        "a": 0.0651738, "b": 0.0124248, "c": 0.0217339, "d": 0.0349835, "e": 0.1041442,
        "f": 0.0197881, "g": 0.0158610, "h": 0.0492888, "i": 0.0558094, "j": 0.0009033,
        "k": 0.0050529, "l": 0.0331490, "m": 0.0202124, "n": 0.0564513, "o": 0.0596302,
        "p": 0.0137645, "q": 0.0008606, "r": 0.0497563, "s": 0.0515760, "t": 0.0729357,
        "u": 0.0225134, "v": 0.0082903, "w": 0.0171272, "x": 0.0013692, "y": 0.0145984,
        "z": 0.0007836, " ": 0.1918182}
    text_length = len(text)
    # Use defaultdict instead of Counter because Counter is slow
    char_counts = defaultdict(int)
    for char in text.lower():
        char_counts[char] += 1
    chi2 = 0
    for char, count in char_counts.items():
        expected = text_length * frequencies.get(char, 8e-4)
        difference = count - expected
        chi2 += difference**2 / expected
    total_letter_count = sum(1 for char in text.lower() if char in frequencies)
    return total_letter_count / chi2 / text_length

def all_english_like_scores_data(cipher_bytes):
    result = []
    for i in range(256):
        key = bytes([i])
        message = bytes_to_string(xor_encrypt(cipher_bytes, key))
        score = english_like_score(message)
        result.append({
            "key": list(key),
            "key_binary": ["{:08b}".format(b) for b in key],
            "message": message,
            "original": cipher_bytes,
            "score": score})
    return result

def best_english_like_score_data(text, num=1):
    return sorted(all_english_like_scores_data(text), key=lambda m: m["score"], reverse=True)[:num]

def looks_like_ecb(cipher_bytes):
    chunk_counter = Counter(byte_chunks(cipher_bytes, 16))
    return chunk_counter.most_common(1)[0][1] > 1

def pkcs7_pad(input_bytes, block_size=16):
    padding_length = -len(input_bytes) % block_size
    if padding_length == 0:
        padding_length = block_size
    return input_bytes + bytes([padding_length] * padding_length)

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
    best_data = best_english_like_score_data(ciphertext, num=5)
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
    stanza = "Burning 'em, if you ain't quick and nimble\n" + "I go crazy when I hear a cymbal"
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
        plaintext += "".join(char for char in message if char is not None)
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
    # Create new cipher object because using cipher object messes up internal IV state
    cbc_result = AES.new("YELLOW SUBMARINE", AES.MODE_CBC, iv).encrypt(plain_bytes)
    assert cbc_result == cipher_bytes

    last_cipher_chunk = iv
    cipher = AES.new("YELLOW SUBMARINE", AES.MODE_ECB, iv)
    result = bytearray()
    for plain_chunk in byte_chunks(plain_bytes, 16):
        combined_chunk = xor_bytes(last_cipher_chunk, plain_chunk)
        cipher_chunk = cipher.encrypt(combined_chunk)
        result.extend(cipher_chunk)
        last_cipher_chunk = cipher_chunk
    assert result == cipher_bytes

def challenge11():
    """An ECB/CBC detection oracle"""
    # hamlet.txt from http://erdani.com/tdpl/hamlet.txt
    # This seems to work perfectly when encrypting 2923 or more bytes of hamlet.txt, but frequently
    # guesses incorrectly with 2922 bytes or fewer. Different files produce different results but
    # for any given file, there seems to be a precise amount of data at which this function works
    # reliably, and below which it frequently thinks ECB is CBC.
    plain_bytes = open("hamlet.txt", "rb").read(3000)
    results = Counter()
    for i in range(1000):
        cipher_bytes, mode_number = encrypt_with_random_key_and_random_mode(plain_bytes)
        mode = {1: "ECB", 2: "CBC"}[mode_number]
        apparent_mode = "ECB" if looks_like_ecb(cipher_bytes) else "CBC"
        results[apparent_mode] += 1
        assert mode == apparent_mode, (mode, apparent_mode, results)

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
