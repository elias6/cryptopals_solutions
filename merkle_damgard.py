from hashlib import sha512
from itertools import cycle, islice
from math import inf
from os import urandom

from util import chunks

class HashFunction:
    byte_pattern = bytes.fromhex("0123456789abcdef")

    def __init__(self, digest_size, block_size=16):
        if digest_size > 64:
            raise ValueError("digest_size must be 64 or less")
        self.digest_size = digest_size
        self.block_size = block_size
        self.initial_state = bytes(islice(cycle(self.byte_pattern), digest_size))

    def compress(self, state, block):
        if len(state) != self.digest_size:
            raise ValueError("length of state must equal digest_size")
        if len(block) != self.block_size:
            raise ValueError("length of block must equal block_size")
        return sha512(state + block).digest()[:self.digest_size]

    def padding(self, message_length):
        result = bytearray((message_length * 8).to_bytes(
            byteorder="big",
            length=(-message_length % self.block_size) or self.block_size))
        result[0] |= (1 << 7)
        return result

    def __call__(self, message, state=None, *, pad=True):
        state = state or self.initial_state
        prepared_message = message + (self.padding(len(message)) if pad else b"")
        assert len(prepared_message) % self.block_size == 0
        for block in chunks(prepared_message, self.block_size):
            state = self.compress(state, block)
        return state

    def random_unique_blocks(self, n=inf):
        seen = set()
        while len(seen) < n:
            block = urandom(self.block_size)
            if block not in seen:
                yield block
                seen.add(block)
