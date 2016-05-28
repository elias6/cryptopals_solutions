import struct

from collections import Counter
from itertools import count
from os import urandom

from english import all_bytes_by_frequency
from util import chunks, gcd, pkcs7_unpad


def looks_like_ecb(ciphertext, block_size=16):
    # TODO: use birthday paradox to calculate an estimate for the expected
    # number of duplicate blocks so this function works on big ciphertexts.
    block_counter = Counter(chunks(ciphertext, block_size))
    return block_counter.most_common(1)[0][1] > 1


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


def crack_ecb_oracle(oracle_fn, block_size=16, prefix_length=0):
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
