#!/usr/bin/env python3

import base64
import cProfile
import pprint
import sys
from collections import Counter
from itertools import chain, cycle, zip_longest

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
    # TODO: return generator instead?
    return [input_bytes[i : i + chunk_size] for i in range(0, len(input_bytes), chunk_size)]

def english_like_score(text):
    # Letter frequencies from http://www.data-compression.com/english.html
    letter_frequencies = {
        "a": 0.0651738, "b": 0.0124248, "c": 0.0217339, "d": 0.0349835, "e": 0.1041442,
        "f": 0.0197881, "g": 0.0158610, "h": 0.0492888, "i": 0.0558094, "j": 0.0009033,
        "k": 0.0050529, "l": 0.0331490, "m": 0.0202124, "n": 0.0564513, "o": 0.0596302,
        "p": 0.0137645, "q": 0.0008606, "r": 0.0497563, "s": 0.0515760, "t": 0.0729357,
        "u": 0.0225134, "v": 0.0082903, "w": 0.0171272, "x": 0.0013692, "y": 0.0145984,
        "z": 0.0007836, " ": 0.1918182}
    text_lower = text.lower()
    letter_counts = Counter(text_lower)
    total_letter_count = sum(1 for char in text_lower if char in letter_frequencies)
    if not total_letter_count:
        return 0
    chi2 = 0
    for letter, count in letter_counts.items():
        expected = len(text) * letter_frequencies.get(letter, 8e-4)
        difference = count - expected
        chi2 += difference**2 / expected
    return total_letter_count / chi2 / len(text)

def old_english_like_score(text):
    result = 0
    for char in text.lower():
        if char in "etaoin":
            result += 2
        elif char in "shrdlu":
            result += 1
    return result

def all_english_like_scores_data(encoded_message, fn=english_like_score):
    result = []
    for i in range(256):
        key = bytes([i])
        message = bytes_to_string(xor_encrypt(encoded_message, key))
        score = fn(message)
        result.append({
            "key": list(key),
            "key_binary": ["{:08b}".format(b) for b in key],
            "message": message,
            "original": encoded_message,
            "score": score})
    return result

def best_english_like_score_data(text, fn=english_like_score, num=1):
    return sorted(
        all_english_like_scores_data(text, fn=fn),
        key=lambda m: m["score"],
        reverse=True)[:num]

def challenge1():
    cipher_hex = ("49276d206b696c6c696e6720796f757220627261696e206c" +
        "696b65206120706f69736f6e6f7573206d757368726f6f6d")
    print(bytes_to_string(hex_to_base64(cipher_hex)))

def challenge2():
    output = xor_bytes(
        bytes.fromhex("1c0111001f010100061a024b53535009181c"),
        bytes.fromhex("686974207468652062756c6c277320657965"))
    print(bytes_to_string(output))
    print(output.hex())

def challenge3():
    cipher_hex = "1b37373331363f78151b7f2b783431333d78397828372d363c78373e783a393b3736"
    ciphertext = bytes.fromhex(cipher_hex)
    best_data = best_english_like_score_data(ciphertext, num=5)
    pp(best_data)
    print(best_data[0]["message"])

def challenge4():
    cipher_hexes = [line.rstrip() for line in open("4.txt").readlines()]
    decoded_string_data = []
    for i, string in enumerate(cipher_hexes):
        cipher_bytes = bytes.fromhex(string)
        decoded_string_data.append(best_english_like_score_data(cipher_bytes)[0])
        decoded_string_data[-1]["index"] = i
    best_decodings = sorted(decoded_string_data, key=lambda d: d["score"], reverse=True)
    result = best_decodings[:3]
    pp(result)

def challenge5():
    stanza = "Burning 'em, if you ain't quick and nimble\n" + "I go crazy when I hear a cymbal"
    print(xor_encrypt(stanza.encode("utf-8"), b"ICE").hex())

def challenge6():
    assert edit_distance(b"this is a test", b"wokka wokka!!!") == 37
    cipher_bytes = base64.b64decode(open("6.txt").read())
    edit_distances = {}
    for keysize in range(2, 41):
        chunk1 = cipher_bytes[:keysize]
        chunk2 = cipher_bytes[keysize : 2 * keysize]
        edit_distances[keysize] = edit_distance(chunk1, chunk2) / keysize
    keysizes = sorted(
        edit_distances,
        key=lambda keysize: edit_distances[keysize],
        reverse=True)
    best_keysize = keysizes[0]
    chunks = byte_chunks(cipher_bytes, best_keysize)
    transposed_blocks = []
    decoding_data = []
    for i in range(best_keysize):
        transposed_blocks.append(bytes(chunk[i] for chunk in chunks if i < len(chunk)))
        decoding_data.append(best_english_like_score_data(transposed_blocks[i]))
    pp(decoding_data)
    key = bytes(chain(*(decoding_data[i]["key"] for i in range(best_keysize))))
    print(key)
    print(bytes(zip(d["message"] for d in decoding_data)))
    # print(bytes_to_string(xor_encrypt(cipher_bytes, key))[:100])
    # pp(transposed_blocks)

if __name__ == "__main__":
    globals()["challenge" + sys.argv[1]]()
    # cProfile.run("challenge" + sys.argv[1] + "()", sort="cumtime")
