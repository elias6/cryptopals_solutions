from os import urandom

import struct

from Crypto.Cipher import AES

from block_tools import pkcs7_pad, random_aes_key
from util import chunks

class HashFunction:
    def __init__(self, digest_size, block_size=16):
        self.digest_size = digest_size
        self.block_size = block_size
        self.default_initial_state = urandom(digest_size)
        self.key = random_aes_key()
        self.iv = urandom(16)

    def compress(self, state, block):
        if len(state) != self.digest_size:
            raise ValueError("length of state must equal digest_size")
        if len(block) != self.block_size:
            raise ValueError("length of block must equal block_size")
        cipher = AES.new(self.key, AES.MODE_CBC, self.iv)
        return cipher.encrypt(pkcs7_pad(state + block))[:self.digest_size]

    def produce_padding(self, message_length):
        length_repr = struct.pack(">Q", message_length * 8)
        padding_length = (-message_length % self.block_size) or self.block_size
        padding = bytearray(length_repr.rjust(padding_length, b"\x00"))
        padding[0] |= (1 << 7)
        return bytes(padding[-self.block_size:])

    def __call__(self, message, initial_state=None):
        state = initial_state or self.default_initial_state
        padded_message = message + self.produce_padding(len(message))
        for block in chunks(padded_message, self.block_size):
            state = self.compress(state, block)
        return state
