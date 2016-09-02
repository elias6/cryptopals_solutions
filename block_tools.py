from collections import Counter
from math import gcd
from os import urandom

import Cryptodome.Util.Counter
from Cryptodome.Cipher import AES

from english import all_bytes_by_frequency
from util import chunks


def aes_encrypt(plaintext, key, mode, *args, pad=False, **kwargs):
    cipher = globals()["_aes_" + mode + "_cipher"](key, *args, **kwargs)
    return cipher.encrypt(pkcs7_pad(plaintext) if pad else plaintext)


def aes_decrypt(ciphertext, key, mode, *args, unpad=False, **kwargs):
    cipher = globals()["_aes_" + mode + "_cipher"](key, *args, **kwargs)
    plaintext = cipher.decrypt(ciphertext)
    return pkcs7_unpad(plaintext) if unpad else plaintext


def _aes_ECB_cipher(key):
    return AES.new(key, AES.MODE_ECB)


def _aes_CBC_cipher(key, iv):
    return AES.new(key, AES.MODE_CBC, iv)


def _aes_CTR_cipher(key, nonce, block_index=0, little_endian=False):
    if little_endian:
        counter = Cryptodome.Util.Counter.new(
            nbits=64, prefix=nonce, initial_value=block_index, little_endian=True)
        return AES.new(key, AES.MODE_CTR, counter=counter)
    else:
        return AES.new(key, AES.MODE_CTR, nonce=nonce, initial_value=block_index)


def looks_like_ecb(ciphertext, block_size=16):
    # TODO: use birthday paradox to calculate an estimate for the expected
    # number of duplicate blocks so this function works on big ciphertexts.
    return max(Counter(chunks(ciphertext, block_size)).values()) > 1


def random_aes_key():
    return urandom(16)


def guess_block_size(oracle_fn):
    seen_sizes = set()
    for plaintext_size in range(33):
        ciphertext = oracle_fn(urandom(plaintext_size))
        seen_sizes.add(len(ciphertext))
    if len(seen_sizes) >= 2:
        result = 0
        for size in seen_sizes:
            result = gcd(result, size)
        return result
    else:
        raise ValueError("Could not guess block size")


def crack_ecb_oracle(oracle_fn, prefix_length=0):
    block_size = guess_block_size(oracle_fn)
    if not looks_like_ecb(oracle_fn(b"A" * 100), block_size):
        raise ValueError("oracle_fn does not appear to produce ECB mode output")
    result = bytearray()
    while True:
        short_block_length = (block_size - len(result) - 1 - prefix_length) % block_size
        short_input_block = b"A" * short_block_length
        block_index = (len(result) + prefix_length) // block_size
        block_to_look_for = chunks(oracle_fn(short_input_block))[block_index]
        for guess in all_bytes_by_frequency:
            test_input = short_input_block + result + bytes([guess])
            if chunks(oracle_fn(test_input))[block_index] == block_to_look_for:
                result.append(guess)
                break
        else:  # if no byte matches
            return pkcs7_unpad(result)


def pkcs7_pad(input_bytes, block_size=16):
    padding_length = -len(input_bytes) % block_size
    if padding_length == 0:
        padding_length = block_size
    return input_bytes + bytes([padding_length] * padding_length)


def pkcs7_unpad(input_bytes, block_size=16):
    padding_length = input_bytes[-1]
    expected_padding = bytes([padding_length]) * padding_length
    padding = input_bytes[-padding_length:]
    if padding_length > block_size or padding != expected_padding:
        raise ValueError("Invalid padding")
    return input_bytes[:-padding_length]


def pkcs7_padding_is_valid(input_bytes):
    try:
        pkcs7_unpad(input_bytes)
    except ValueError:
        return False
    else:
        return True
