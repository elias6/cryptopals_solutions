from os import urandom

from Crypto.Cipher import AES

from block_tools import pkcs7_pad, random_aes_key
from util import chunks

class HashFunction:
    def __init__(self, block_size):
        self.block_size = block_size
        self.default_initial_state = urandom(block_size)
        self.key = random_aes_key()

    def compress(self, state, block):
        cipher = AES.new(self.key, AES.MODE_ECB)
        return cipher.encrypt(pkcs7_pad(state + block))[:self.block_size]

    def __call__(self, message, initial_state=None):
        state = initial_state or self.default_initial_state
        for block in chunks(message, self.block_size):
            state = self.compress(state, block)
        return state
