from itertools import cycle, islice

import struct

from block_tools import aes_encrypt
from util import chunks

class HashFunction:
    byte_pattern = bytes.fromhex("0123456789abcdef")

    def __init__(self, digest_size, block_size=16):
        self.digest_size = digest_size
        self.block_size = block_size
        self.initial_state = bytes(islice(cycle(self.byte_pattern), digest_size))

    def compress(self, state, block):
        if len(state) != self.digest_size:
            raise ValueError("length of state must equal digest_size")
        if len(block) != self.block_size:
            raise ValueError("length of block must equal block_size")
        key = iv = b"\x00"*16
        return aes_encrypt(state + block, key, "CBC", iv, pad=True)[:self.digest_size]

    def produce_padding(self, message_length):
        length_repr = struct.pack(">Q", message_length * 8)
        padding_length = (-message_length % self.block_size) or self.block_size
        padding = bytearray(length_repr.rjust(padding_length, b"\x00"))
        padding[0] |= (1 << 7)
        return bytes(padding[-self.block_size:])

    def __call__(self, message, state=None):
        state = state or self.initial_state
        padded_message = message + self.produce_padding(len(message))
        for block in chunks(padded_message, self.block_size):
            state = self.compress(state, block)
        return state
