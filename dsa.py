from collections import namedtuple

from util import mod_inv, random, sha1

p = int("800000000000000089e1855218a0e7dac38136ffafa72eda7859f2171e25e65eac698c"
    "1702578b07dc2a1076da241c76c62d374d8389ea5aeffd3226a0530cc565f3bf6b50929139"
    "ebeac04f48c3c84afb796d61e5a4f9a8fda812ab59494232c7d2b4deb50aa18ee9e132bfa8"
    "5ac4374d7f9091abc3d015efc871a584471bb1", 16)

q = int("f4f47f05794b256174bba6e9b396a7707e563c5b", 16)

g = int("5958c9d3898b224b12672c0b98e06c60df923cb8bc999d119458fef538b8fa4046c8db"
    "53039db620c094c9fa077ef389b5322a559946a71903f990f1f7e0e025e2d7f7cf494aff1a"
    "0470f5b64c36b625a097f1651fe775323556fe00b3608c887892878480e99041be601a6216"
    "6ca6894bdd41a7054ec89f756ba9fc95302291", 16)

KeyPair = namedtuple("KeyPair", ["public_key", "private_key"])
Signature = namedtuple("Signature", ["r", "s"])


def generate_key_pair():
    private_key = random.randint(1, q - 1)    # called "x" in literature
    public_key = pow(g, private_key, p)       # called "y" in literature
    return KeyPair(public_key, private_key)


def sign(message, private_key, leak=False):
    digest = int.from_bytes(sha1(message).digest(), byteorder="big")
    while True:
        # k == random, per-message number that must be secret
        k = random.randint(1, q - 1)
        r = pow(g, k, p) % q
        if r == 0:
            continue
        s = (mod_inv(k, q) * (digest + r*private_key)) % q
        if s == 0:
            continue
        if leak:
            return (Signature(r, s), k)
        else:
            return Signature(r, s)


def verify(message, public_key, signature):
    r, s = signature
    if not 0 < r < q or not 0 < s < q:
        raise ValueError("invalid signature")
    w = mod_inv(s, q)
    digest = int.from_bytes(sha1(message).digest(), byteorder="big")
    u1 = (digest * w) % q
    u2 = (r * w) % q
    v = ((pow(g, u1, p) * pow(public_key, u2, p)) % p) % q
    return v == r


def recover_private_key(k, digest, signature):
    return ((k*signature.s - digest) * mod_inv(signature.r, q)) % q
