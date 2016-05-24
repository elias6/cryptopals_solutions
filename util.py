import decimal
import os
import pprint as pprint_module
import re

from collections import namedtuple
from functools import lru_cache
from hashlib import md5
from itertools import cycle
from random import SystemRandom
from sha1.sha1 import Sha1Hash

from Crypto.Util.number import getStrongPrime

try:
    # Python 3.5
    from math import gcd
except ImportError:
    # older Python versions
    from fractions import gcd

random = SystemRandom()

# prime number specified for 1536-bit modular exponential group in RFC
# at https://datatracker.ietf.org/doc/rfc3526/?include_text=1
IETF_DIFFIE_HELLMAN_PRIME = int("ffffffffffffffffc90fdaa22168c234c4c6628b80dc1c"
    "d129024e088a67cc74020bbea63b139b22514a08798e3404ddef9519b3cd3a431b302b0a6d"
    "f25f14374fe1356d6d51c245e485b576625e7ec6f44c42e9a637ed6b0bff5cb6f406b7edee"
    "386bfb5a899fa5ae9f24117c4b1fe649286651ece45b3dc2007cb8a163bf0598da48361c55"
    "d39a69163fa8fd24cf5f83655d23dca3ad961c62f356208552bb9ed529077096966d670c35"
    "4e4abc9804f1746c08ca237327ffffffffffffffff", 16)


def pprint(*args, width=120, **kwargs):
    pprint_module.pprint(*args, width=width, **kwargs)


def xor_bytes(*bytes_objects):
    lengths = [len(b) for b in bytes_objects]
    if len(set(lengths)) > 1:
        raise ValueError("inputs must be of equal length")
    result = bytearray([0]) * lengths[0]
    for b in bytes_objects:
        for i, byte in enumerate(b):
            result[i] ^= byte
    return bytes(result)


def xor_encrypt(input_bytes, key):
    return bytes(a ^ b for a, b in zip(input_bytes, cycle(key)))


def chunks(x, chunk_size=16):
    return [x[i : i + chunk_size] for i in range(0, len(x), chunk_size)]


def int_to_bytes(x):
    return x.to_bytes(length=(x.bit_length() // 8) + 1, byteorder="big")


def pkcs7_pad(input_bytes, block_size=16):
    padding_length = -len(input_bytes) % block_size
    if padding_length == 0:
        padding_length = block_size
    return input_bytes + bytes([padding_length] * padding_length)


def pkcs7_unpad(ciphertext, block_size=16):
    padding_length = ciphertext[-1]
    expected_padding = bytes([padding_length]) * padding_length
    padding = ciphertext[-padding_length:]
    if padding_length > block_size or padding != expected_padding:
        raise ValueError("Invalid padding")
    return ciphertext[:-padding_length]


def sha1(message):
    return Sha1Hash().update(message)


def calculate_hmac(key, message, hash_fn=sha1):
    key_hash = hash_fn(key).digest()
    o_key_pad = xor_encrypt(key_hash, b"\x5c")
    i_key_pad = xor_encrypt(key_hash, b"\x36")
    return hash_fn(o_key_pad + hash_fn(i_key_pad + message).digest()).digest()

get_hmac = lru_cache()(calculate_hmac)


def extended_gcd(a, b):
    if a == 0:
        return (b, 0, 1)
    else:
        g, y, x = extended_gcd(b % a, a)
        return (g, x - (b // a) * y, y)


def invmod(a, m):
    g, x, y = extended_gcd(a, m)
    if g != 1:
        raise ValueError("modular inverse does not exist")
    else:
        return x % m


RsaKeyPair = namedtuple("RsaKeyPair", ["public_key", "private_key"])
RsaKey = namedtuple("RsaKey", ["modulus", "exponent"])


def generate_rsa_key_pair():
    public_exponent = 3
    p = getStrongPrime(512, e=public_exponent)
    q = getStrongPrime(512, e=public_exponent)
    modulus = p * q
    totient = (p - 1) * (q - 1)
    assert totient > public_exponent
    assert gcd(public_exponent, totient) == 1
    private_exponent = invmod(public_exponent, totient)
    assert (public_exponent * private_exponent) % totient == 1
    public_key = RsaKey(modulus, public_exponent)
    private_key = RsaKey(modulus, private_exponent)
    return RsaKeyPair(public_key, private_key)


def rsa_calculate(message, key):
    message_int = int.from_bytes(message, byteorder="big")
    if message_int >= key.modulus:
        raise ValueError("message is too big for modulus")
    cipher_int = pow(message_int, key.exponent, key.modulus)
    return cipher_int.to_bytes(length=len(int_to_bytes(key.modulus)), byteorder="big")


def rsa_encrypt(plaintext, key):
    return rsa_calculate(plaintext, key)


def rsa_decrypt(ciphertext, key):
    return rsa_calculate(ciphertext, key)


def rsa_create_signature(message):
    """Produce unpadded, unencrypted PKCS v1.5 signature"""
    # TODO: make this handle more hash functions
    
    digest_algorithm_asn1 = (
        b"\x06"         # object identifier
        b"\x08"         # length (8)
        b"\x2a"         # iso (1), member-body (2)
        b"\x86\x48"     # US (840)
        b"\x86\xf7\x0d" # RSA Data Security, Inc.
        b"\x82"         # digestAlgorithm
        b"\x85"         # md5
    )

    digest_asn1 = (
        b"\x04"     # octet string
        b"\x10"     # length
        + md5(message).digest()
    )

    return (
        b"\x10"     # sequence
        b"\x18"     # length
        + digest_algorithm_asn1
        + digest_asn1
    )


def rsa_sign(message, private_key):
    data = rsa_create_signature(message)
    return rsa_encrypt(rsa_pad(data, private_key.modulus, block_type=1), private_key)


def rsa_verify(message, public_key, signature):
    """Verify PKCS v1.5 signature"""
    asn1_stuff = b"\x10\x18\x06\x08\x2a\x86\x48\x86\xf7\x0d\x82\x85\x04\x10"
    data = rsa_unpad(rsa_decrypt(signature, public_key))
    return data == asn1_stuff + md5(message).digest()


def rsa_pad(message, modulus, block_type=2):
    # block types 0 and 1 are for private keys, 2 is for public keys.
    # Block type 0 is ambiguous with messages beginning with null bytes and
    # is not recommended.
    if block_type not in [0, 1, 2]:
        raise ValueError("block_type must be 0, 1, or 2")
    modulus_length = len(int_to_bytes(modulus))
    if modulus_length < 12:
        raise ValueError("modulus must be at least 12 bytes")
    if len(message) > modulus_length - 11:
        raise ValueError("message is too big for modulus")
    padding_length = modulus_length - 3 - len(message)
    padding = {
        0: b"\x00" * padding_length,
        1: b"\xff" * padding_length,
        2: bytes(random.randint(1, 255) for _ in range(padding_length)),
    }[block_type]
    return b"\x00" + bytes([block_type]) + padding + b"\x00" + message


def rsa_unpad(message, secure=True):
    # Setting secure to False emulates RSA implementations that don't
    # properly check the length of the padding, allowing Bleichenbacher's
    # signature forgery.
    matches = re.fullmatch(b"\x00([\x00-\x02])(.*)\x00(.*)", message, re.DOTALL)
    if not matches:
        raise ValueError("invalid message")
    block_type_byte, padding, message = matches.groups()
    if secure and len(padding) < 8:
        raise ValueError("invalid padding")
    if block_type_byte == [0] and any(x != 0 for x in padding):
        raise ValueError("invalid padding")
    elif block_type_byte == [1] and any(x != 0xff for x in padding):
        raise ValueError("invalid padding")
    elif block_type_byte == [2] and any(x == 0 for x in padding):
        raise ValueError("invalid padding")
    return message


def big_int_cube_root(x):
    """Return the cube root of the given number.

    This works with integers that would cause OverflowErrors when trying to
    calculate the cube root the more straightforward way (x ** (1/3)). It
    seems to reliably return the result with enough precision that cubing it
    and rounding the cube produces the original number, although I don't yet
    have any rigorous proof of this.
    """
    with decimal.localcontext() as context:
        # Guesstimate as to how much precision is needed to get the right result
        context.prec = len(str(x)) // 3 + 4
        return decimal.Decimal(x) ** (decimal.Decimal(1) / decimal.Decimal(3))
