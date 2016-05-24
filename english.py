from collections import defaultdict

from util import xor_encrypt

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


def crack_common_xor_key(ciphertexts):
    key = bytearray()
    for i in range(max(len(c) for c in ciphertexts)):
        transposed_block = bytes(c[i] for c in ciphertexts if i < len(c))
        key.append(best_english_like_score_data(transposed_block)["key"])
    plaintexts = [xor_encrypt(c, key) for c in ciphertexts]
    return (plaintexts, key)
