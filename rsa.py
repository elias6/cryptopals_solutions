import re

from collections import namedtuple
from hashlib import md5
from math import ceil, gcd

from Crypto.Util.number import getPrime, getStrongPrime

from util import mod_inv, random

KeyPair = namedtuple("KeyPair", ["public_key", "private_key"])
Key = namedtuple("Key", ["modulus", "exponent"])


def generate_key_pair(bit_length=1024):
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
    return KeyPair(public_key, private_key)


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


def create_signature(message):
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


def sign(message, private_key):
    sig_asn1 = create_signature(message)
    return encrypt(pad(sig_asn1, private_key.modulus, block_type=1), private_key)


def verify(message, public_key, signature, secure=True):
    """Verify PKCS v1.5 signature"""
    # Setting secure to False emulates RSA implementations that don't
    # properly check that the signature is right-aligned, allowing
    # Bleichenbacher's signature forgery (BERserk).
    asn1_stuff = b"\x10\x18\x06\x08\x2a\x86\x48\x86\xf7\x0d\x82\x85\x04\x10"
    sig_data = unpad(decrypt(signature, public_key))
    if secure:
        return sig_data == asn1_stuff + md5(message).digest()
    else:
        return sig_data.startswith(asn1_stuff + md5(message).digest())


def pad(message, modulus, block_type=2):
    # block types 0 and 1 are for private keys, 2 is for public keys.
    # Block type 0 is ambiguous with messages beginning with null bytes and
    # is not recommended.
    if block_type not in [0, 1, 2]:
        raise ValueError("block_type must be 0, 1, or 2")
    modulus_length = ceil(modulus.bit_length() / 8)
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
