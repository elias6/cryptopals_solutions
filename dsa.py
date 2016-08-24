from collections import namedtuple
from hashlib import sha1

from util import mod_inv, random

p = int("800000000000000089e1855218a0e7dac38136ffafa72eda7859f2171e25e65eac698c1702578b07"
        "dc2a1076da241c76c62d374d8389ea5aeffd3226a0530cc565f3bf6b50929139ebeac04f48c3c84a"
        "fb796d61e5a4f9a8fda812ab59494232c7d2b4deb50aa18ee9e132bfa85ac4374d7f9091abc3d015"
        "efc871a584471bb1", 16)

q = int("f4f47f05794b256174bba6e9b396a7707e563c5b", 16)

g = int("5958c9d3898b224b12672c0b98e06c60df923cb8bc999d119458fef538b8fa4046c8db53039db620"
        "c094c9fa077ef389b5322a559946a71903f990f1f7e0e025e2d7f7cf494aff1a0470f5b64c36b625"
        "a097f1651fe775323556fe00b3608c887892878480e99041be601a62166ca6894bdd41a7054ec89f"
        "756ba9fc95302291", 16)

KeyPair = namedtuple("KeyPair", ["public_key", "private_key"])
Signature = namedtuple("Signature", ["r", "s"])


def generate_key_pair():
    private_key = random.randint(1, q - 1)    # called "x" in literature
    public_key = pow(g, private_key, p)       # called "y" in literature
    return KeyPair(public_key, private_key)


def sign(message, private_key, g=g, secure=True):
    signature, k = sign_and_leak_k(message, private_key, g, secure)
    return signature


def sign_and_leak_k(message, private_key, g=g, secure=True):
    # Setting secure to False will prevent this function from retrying the
    # signature if r == 0, which may happen with invalid signatures, if g is
    # maliciously chosen, or on other rare occasions.
    digest = int.from_bytes(sha1(message).digest(), byteorder="big")
    while True:
        # k == random, per-message number that must be secret
        k = random.randint(1, q - 1)
        r = pow(g, k, p) % q
        if secure and r == 0:
            continue

        s = (mod_inv(k, q) * (digest + r*private_key)) % q
        if s == 0:
            continue
        return (Signature(r, s), k)


def verify(message, public_key, signature, g=g, secure=True):
    # Setting secure to False will prevent this function from rejecting the
    # signature if r is not in the allowed range, which may happen with
    # invalid signatures or if g is maliciously chosen.
    r, s = signature

    if secure and not 0 < r < q:
        raise ValueError("invalid signature")
    if not 0 < s < q:
        raise ValueError("invalid signature")
    digest = int.from_bytes(sha1(message).digest(), byteorder="big")
    w = mod_inv(s, q)
    u1 = (digest * w) % q
    u2 = (r * w) % q
    v = ((pow(g, u1, p) * pow(public_key, u2, p)) % p) % q
    return v == r


def recover_private_key(k, message, signature):
    digest = int.from_bytes(sha1(message).digest(), byteorder="big")
    return ((k*signature.s - digest) * mod_inv(signature.r, q)) % q
