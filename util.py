import decimal

from functools import lru_cache
from itertools import cycle, tee
from random import SystemRandom
from sha1.sha1 import Sha1Hash

try:
    from math import gcd    # Python 3.5
except ImportError:
    from fractions import gcd    # older Python versions

random = SystemRandom()

# prime number specified for 1536-bit modular exponential group in RFC
# at https://datatracker.ietf.org/doc/rfc3526/?include_text=1. Used for
# Diffie-Hellman and SRP.
IETF_PRIME = int("ffffffffffffffffc90fdaa22168c234c4c6628b80dc1cd129024e088a67c"
    "c74020bbea63b139b22514a08798e3404ddef9519b3cd3a431b302b0a6df25f14374fe1356"
    "d6d51c245e485b576625e7ec6f44c42e9a637ed6b0bff5cb6f406b7edee386bfb5a899fa5a"
    "e9f24117c4b1fe649286651ece45b3dc2007cb8a163bf0598da48361c55d39a69163fa8fd2"
    "4cf5f83655d23dca3ad961c62f356208552bb9ed529077096966d670c354e4abc9804f1746"
    "c08ca237327ffffffffffffffff", 16)


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


def sliding_pairs(iterable):
    # pairwise recipe from https://docs.python.org/3/library/itertools.html
    a, b = tee(iterable)
    next(b, None)
    return zip(a, b)


def int_to_bytes(x):
    return x.to_bytes(length=(x.bit_length() // 8) + 1, byteorder="big")


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


def sha1(message):
    return Sha1Hash().update(message)


def calculate_hmac(key, message, hash_fn=sha1):
    key_hash = hash_fn(key).digest()
    o_key_pad = xor_encrypt(key_hash, b"\x5c")
    i_key_pad = xor_encrypt(key_hash, b"\x36")
    return hash_fn(o_key_pad + hash_fn(i_key_pad + message).digest()).digest()

get_hmac = lru_cache()(calculate_hmac)


def extended_gcd(a, b):
    """Extended Euclidean algorithm.

    Return a tuple of numbers (g, x, y) such that ax + by == g == gcd(a, b).
    """
    if a == 0:
        return (b, 0, 1)
    else:
        g, y, x = extended_gcd(b % a, a)
        return (g, x - (b // a) * y, y)


def mod_inv(a, m):
    """Return the integer x such that (a * x) % m == 1."""
    g, x, _ = extended_gcd(a, m)
    if g != 1:
        raise ValueError("modular inverse does not exist")
    else:
        return x % m


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
