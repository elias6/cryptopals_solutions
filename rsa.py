import re

from collections import namedtuple
from fractions import Fraction
from hashlib import md5, sha1, sha224, sha256, sha384, sha512
from itertools import count
from math import ceil, floor, gcd

from Cryptodome.Util.asn1 import DerObjectId, DerOctetString, DerSequence
from Cryptodome.Util.number import getPrime, getStrongPrime

from util import mod_inv, random

Key = namedtuple("Key", ["modulus", "exponent"])


class KeyPair(namedtuple("KeyPair", ["public_key", "private_key"])):
    @classmethod
    def random(cls, bit_length=1024):
        if bit_length % 2 != 0:
            raise ValueError("bit_length must be even")
        public_exponent = 3
        p = generate_prime(bit_length // 2, e=public_exponent)
        q = generate_prime(bit_length // 2, e=public_exponent)
        modulus = p * q
        totient = (p - 1) * (q - 1)
        assert totient > public_exponent
        assert gcd(public_exponent, totient) == 1
        private_exponent = mod_inv(public_exponent, totient)
        assert (public_exponent * private_exponent) % totient == 1
        public_key = Key(modulus, public_exponent)
        private_key = Key(modulus, private_exponent)
        return cls(public_key, private_key)


def generate_prime(bit_length, e=None):
    if bit_length >= 512 and bit_length % 128 == 0:
        return getStrongPrime(bit_length, e)
    else:
        while True:
            prime = getPrime(bit_length)
            if gcd(prime - 1, e) == 1 or not e:
                return prime


def calculate(message, key):
    message_int = int.from_bytes(message, byteorder="big")
    if message_int >= key.modulus:
        raise ValueError("message is too big for modulus")
    cipher_int = pow(message_int, key.exponent, key.modulus)
    modulus_length = ceil(key.modulus.bit_length() / 8)
    return cipher_int.to_bytes(length=modulus_length, byteorder="big")


def encrypt(plaintext, key):
    return calculate(plaintext, key)


def decrypt(ciphertext, key):
    return calculate(ciphertext, key)


def pad_and_encrypt(plaintext, key, block_type=2):
    padded_message = pad(plaintext, ceil(key.modulus.bit_length() / 8), block_type)
    return encrypt(padded_message, key)


def create_digest_asn1(message, hash_fn=sha1):
    """Produce unpadded, unencrypted PKCS v1.5 signature"""
    asn1_object_ids = {
        md5: "1.2.840.113549.2.5",
        sha1: "1.3.14.3.2.26",
        sha224: "2.16.840.1.101.3.4.2.4",
        sha256: "2.16.840.1.101.3.4.2.1",
        sha384: "2.16.840.1.101.3.4.2.2",
        sha512: "2.16.840.1.101.3.4.2.3",
    }

    return DerSequence([
        DerObjectId(asn1_object_ids[hash_fn]),
        DerOctetString(hash_fn(message).digest())
    ]).encode()


def sign(message, private_key):
    sig_asn1 = create_digest_asn1(message)
    return pad_and_encrypt(sig_asn1, private_key, block_type=1)


def verify(message, public_key, signature, secure=True):
    """Verify PKCS v1.5 signature"""
    # Setting secure to False emulates RSA implementations that don't
    # properly check that the signature is right-aligned, allowing
    # Bleichenbacher's signature forgery (BERserk).
    sig_data = unpad(decrypt(signature, public_key))
    if secure:
        return sig_data == create_digest_asn1(message)
    else:
        return sig_data.startswith(create_digest_asn1(message))


def pad(message, length, block_type=2):
    # block types 0 and 1 are for private keys, 2 is for public keys.
    # Block type 0 is ambiguous with messages beginning with null bytes and
    # is not recommended.
    if block_type not in [0, 1, 2]:
        raise ValueError("block_type must be 0, 1, or 2")
    if length < 12:
        raise ValueError("length must be at least 12 bytes")
    if len(message) > length - 11:
        raise ValueError("message is too big for length")
    padding_length = length - 3 - len(message)
    padding = {
        0: b"\x00" * padding_length,
        1: b"\xff" * padding_length,
        2: bytes(random.randint(1, 255) for _ in range(padding_length)),
    }[block_type]
    return b"\x00" + bytes([block_type]) + padding + b"\x00" + message


def unpad(message):
    matches = re.fullmatch(b"\x00([\x00-\x02])(.{8,}?)\x00(.*)", message, re.DOTALL)
    if not matches:
        raise ValueError("invalid message")
    block_type_byte, padding, message = matches.groups()
    if block_type_byte == [0] and any(x != 0 for x in padding):
        raise ValueError("invalid padding")
    elif block_type_byte == [1] and any(x != 0xff for x in padding):
        raise ValueError("invalid padding")
    elif block_type_byte == [2] and any(x == 0 for x in padding):
        raise ValueError("invalid padding")
    return message


def multiply(message, number, modulus):
    new_message_int = (int.from_bytes(message, byteorder="big") * number) % modulus
    length = ceil(modulus.bit_length() / 8)
    return new_message_int.to_bytes(byteorder="big", length=length)


def crack_parity_oracle(ciphertext, public_key, plaintext_is_odd, verbose=False):
    modulus = public_key.modulus
    lower_bound = Fraction(0)
    upper_bound = Fraction(modulus)
    modulus_length = ceil(modulus.bit_length() / 8)
    for i in count(start=1):
        test_ciphertext = multiply(ciphertext, 2 ** (i*public_key.exponent), modulus)
        if plaintext_is_odd(test_ciphertext):
            lower_bound = (lower_bound + upper_bound) / 2
        else:
            upper_bound = (lower_bound + upper_bound) / 2
        plain_int = floor(upper_bound)
        recovered_plaintext = plain_int.to_bytes(length=modulus_length, byteorder="big")
        if verbose:
            try:
                print(unpad(recovered_plaintext))
            except ValueError:
                pass
        if ceil(lower_bound) == plain_int:
            return recovered_plaintext


def crack_padding_oracle(ciphertext, public_key, padding_looks_ok):
    # Details of how this function works can be found at
    # http://archiv.infsec.ethz.ch/education/fs08/secsem/Bleichenbacher98.pdf
    if not padding_looks_ok(ciphertext):
        raise ValueError("ciphertext must be PKCS-padded")

    modulus = public_key.modulus    # called "n" in paper
    modulus_length = ceil(modulus.bit_length() / 8)    # called "k" in paper
    B = 2 ** (8*(modulus_length - 2))

    def first_good_s(s_iter):
        for s in s_iter:
            test_ciphertext = multiply(ciphertext, s**public_key.exponent, modulus)
            if padding_looks_ok(test_ciphertext):
                return s
        return None

    def step2a():
        return first_good_s(count(start=ceil(Fraction(modulus, 3*B))))

    def step2b(s):
        return first_good_s(count(start=s + 1))

    def step2c(s, interval):
        a, b = interval
        for r in count(start=ceil(Fraction(2 * (b*s - 2*B), modulus))):
            s_start = ceil(Fraction(2*B + r*modulus, b))
            s_stop = floor(Fraction(3*B + r*modulus, a)) + 1
            s = first_good_s(range(s_start, s_stop))
            if s is not None:
                return s

    def step3(intervals, s):
        result = set()
        for a, b in intervals:
            start = ceil(Fraction(a*s - 3*B + 1, modulus))
            stop = floor(Fraction(b*s - 2*B, modulus)) + 1
            for r in range(start, stop):
                new_a = max(a, ceil(Fraction(2*B + r*modulus, s)))
                new_b = min(b, floor(Fraction(3*B - 1 + r*modulus, s)))
                result.add((new_a, new_b))
        return result

    def step4(intervals):
        single_message_intervals = {x for x in intervals if x[0] == x[1]}
        if len(single_message_intervals) == 1:
            a, b = list(single_message_intervals)[0]
            return a.to_bytes(length=modulus_length, byteorder="big")
        return None

    # TODO: implement step 1 from the paper so this function works on
    # non-PKCS-padded messages.
    intervals = {(2*B, 3*B - 1)}    # called "M" in paper
    for i in count(start=1):
        if i == 1:
            s = step2a()
        else:
            if len(intervals) > 1:
                s = step2b(s)
            else:
                s = step2c(s, list(intervals)[0])
        intervals = step3(intervals, s)
        assert len(intervals) >= 1
        result = step4(intervals)
        if result is not None:
            return result
