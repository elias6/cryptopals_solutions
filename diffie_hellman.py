from collections import defaultdict
from hashlib import sha1
from os import urandom

from block_tools import aes_decrypt, aes_encrypt
from util import IETF_PRIME, int_to_bytes, random


class User:
    def __init__(self, p=IETF_PRIME, g=2, private_key=None):
        self.p = p
        if private_key is None:
            self._private_key = random.randint(1, p - 1)
        else:
            self._private_key = private_key
        self.public_key = pow(g, self._private_key, p)
        self._shared_keys = {}
        self.inbox = defaultdict(list)

    def get_shared_key_for(self, other):
        if other not in self._shared_keys:
            self._shared_keys[other] = pow(other.public_key, self._private_key, other.p)
        return self._shared_keys[other]

    def send_echo_request(self, other, message):
        iv, encrypted_request = self._encrypt_message(message, other)
        new_iv, response = other._respond_to_echo_request(iv, encrypted_request, self)
        assert self._decrypt_message(new_iv, response, other) == message

    def _respond_to_echo_request(self, iv, encrypted_request, other):
        message = self._decrypt_message(iv, encrypted_request, other)
        self.inbox[other].append(message)
        return self._encrypt_message(message, other)

    def _generate_symmetric_key(self, other):
        return sha1(int_to_bytes(self.get_shared_key_for(other))).digest()[:16]

    def _encrypt_message(self, message, other):
        iv = urandom(16)
        key = self._generate_symmetric_key(other)
        return (iv, aes_encrypt(message, key, "CBC", iv, pad=True))

    def _decrypt_message(self, iv, ciphertext, other):
        key = self._generate_symmetric_key(other)
        return aes_decrypt(ciphertext, key, "CBC", iv, unpad=True)
