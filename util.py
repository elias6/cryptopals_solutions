import decimal
import os
import pprint as pprint_module
import re

from collections import defaultdict, namedtuple
from functools import lru_cache
from hashlib import md5, sha256
from heapq import nlargest
from http.server import BaseHTTPRequestHandler, HTTPServer
from itertools import cycle
from multiprocessing.dummy import Pool as ThreadPool
from random import SystemRandom
from sha1.sha1 import Sha1Hash
from socketserver import ThreadingMixIn
from statistics import median
from time import perf_counter, sleep
from urllib.error import HTTPError
from urllib.parse import parse_qs, urlencode, urlparse
from urllib.request import urlopen

from Crypto.Cipher import AES
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


def insecure_compare(data1, data2, delay):
    if len(data1) != len(data2):
        return False
    for byte1, byte2 in zip(data1, data2):
        if byte1 != byte2:
            return False
        sleep(delay)
    return True


class FancyHTTPServer(ThreadingMixIn, HTTPServer):
    request_queue_size = 128


class ValidatingRequestHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        url_components = urlparse(self.path)
        if url_components.path == "/signature_is_valid":
            query_vars = parse_qs(url_components.query)
            try:
                filename = query_vars["file"][0]
                with open(filename, "rb") as file:
                    data = file.read()
                signature = bytes.fromhex(query_vars["signature"][0])
            except (KeyError, ValueError, FileNotFoundError):
                self.send_error(400)
            else:
                hmac = get_hmac(self.server.hmac_key, data)
                if self.server.validate_signature(hmac, signature):
                    self.send_response(200)
                    self.end_headers()
                    self.wfile.write(b"Signature matches.")
                else:
                    self.send_error(500)
        else:
            self.send_error(404)

    def log_message(self, format, *args):
        pass


def server_approves_of_signature(signature):
    query = urlencode({"file": "hamlet.txt", "signature": signature.hex()})
    try:
        urlopen("http://localhost:31415/signature_is_valid?" + query)
    except HTTPError:
        return False
    else:
        return True


class CantRecoverSignatureError(Exception):
    pass


def recover_signature(validate_signature, thread_count, threshold, attempt_limit):
    # TODO: make this function figure out threshold on its own

    def try_signature(signature):
        start_time = perf_counter()
        is_valid = validate_signature(signature)
        duration = perf_counter() - start_time
        return {"signature": signature, "is_valid": is_valid, "duration": duration}

    result = bytearray()
    sig_durations = defaultdict(list)
    with ThreadPool(thread_count) as pool:
        for pos in range(20):
            assert pos == len(result)
            test_sigs = [bytes(result + bytes([b] + [0]*(19 - pos))) for b in range(256)]
            for i in range(attempt_limit):
                for sig_data in pool.imap_unordered(try_signature, test_sigs):
                    signature = sig_data["signature"]
                    if sig_data["is_valid"]:
                        print("signature recovered: {}, "
                            "{} attempt(s) for last byte".format(list(result), i + 1))
                        return signature
                    sig_durations[signature].append(sig_data["duration"])
                slowest_sig, second_slowest_sig = nlargest(
                    2, test_sigs, key=lambda x: median(sig_durations[x]))
                slowest_duration = median(sig_durations[slowest_sig])
                second_slowest_duration = median(sig_durations[second_slowest_sig])
                duration_difference = slowest_duration - second_slowest_duration
                if duration_difference > threshold:
                    result.append(slowest_sig[pos])
                    print("recovered so far: {}, {} attempt(s) for last byte, "
                        "duration difference: {:.3f} ms".format(list(result), i + 1,
                        1000 * duration_difference))
                    break
            else:
                print("recovered so far: {}, {} attempt(s) for last byte, "
                    "duration difference: {:.3f} ms".format(list(result), i + 1,
                    1000 * duration_difference))
                raise CantRecoverSignatureError("can't recover signature")
    raise CantRecoverSignatureError("can't recover signature")


class DiffieHellmanUser:
    def __init__(self, p=IETF_DIFFIE_HELLMAN_PRIME, g=2, private_key=None):
        self.p = p
        if private_key is None:
            self._private_key = random.randint(1, p - 1)
        else:
            self._private_key = private_key
        self.public_key = pow(g, self._private_key, p)
        self._shared_keys = {}
        self._decrypted_messages = defaultdict(list)

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
        self._decrypted_messages[other].append(message)
        return self._encrypt_message(message, other)

    def _generate_symmetric_key(self, other):
        return sha1(int_to_bytes(self.get_shared_key_for(other))).digest()[:16]

    def _encrypt_message(self, message, other):
        iv = os.urandom(16)
        key = self._generate_symmetric_key(other)
        return (iv, AES.new(key, AES.MODE_CBC, iv).encrypt(pkcs7_pad(message)))

    def _decrypt_message(self, iv, ciphertext, other):
        key = self._generate_symmetric_key(other)
        return pkcs7_unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(ciphertext))


def scramble_srp_keys(A, B):
    return int(sha256(int_to_bytes(A) + int_to_bytes(B)).hexdigest(), 16)


class SRPServer:
    N = IETF_DIFFIE_HELLMAN_PRIME
    g = 2

    def __init__(self):
        self.users = {}

    def _respond_to_sign_up_request(self, username, salt, verifier):
        self.users[username] = {"salt": salt, "verifier": verifier}

    def _respond_to_login_request(self, username, A, k=3):
        # A == public ephemeral number from client
        user = self.users[username]
        b = random.randint(1, self.N - 1)  # private ephemeral number
        # B == public ephemeral number. Usually, B depends on the password, but
        # if k == 0, it is a completely random Diffie-Hellman public key, which
        # causes u to be essentially random.
        B = ((k * user["verifier"]) + pow(self.g, b, self.N)) % self.N
        u = scramble_srp_keys(A, B)
        S = pow(A * pow(user["verifier"], u, self.N), b, self.N)
        user["shared_session_key"] = sha256(int_to_bytes(S)).digest()
        return (user["salt"], B, u)

    def _verify_hmac(self, hmac, username):
        user = self.users[username]
        return hmac == get_hmac(user["shared_session_key"], user["salt"], sha256)


class MitmSRPServer(SRPServer):
    def __init__(self, real_server):
        super().__init__()
        self.real_server = real_server

    def _respond_to_login_request(self, username, A, k=3):
        if k != 0:
            raise ValueError("k must be 0")
        salt, _, _ = self.real_server._respond_to_login_request(username, A, k=k)
        b = random.randint(1, self.N - 1)
        self.users[username] = {"salt": salt, "A": A, "b": b}
        u = 1
        B = pow(self.g, b, self.N)
        return (salt, B, u)

    def _verify_hmac(self, hmac, username):
        user = self.users[username]
        # 20 most common passwords according to xato.net
        common_passwords = ["password", "123456", "12345678", "1234", "qwerty", "12345",
            "dragon", "pussy", "baseball", "football", "letmein", "monkey", "696969",
            "abc123", "mustang", "michael", "shadow", "master", "jennifer", "111111"]
        u = 1
        for test_password in common_passwords:
            test_x = SRPClient._generate_private_key(
                username, test_password, user["salt"])
            test_verifier = pow(self.g, test_x, self.N)
            test_S = pow(user["A"] * pow(test_verifier, u, self.N), user["b"], self.N)
            test_session_key = sha256(int_to_bytes(test_S)).digest()
            if get_hmac(test_session_key, user["salt"], sha256) == hmac:
                user["password"] = test_password
                return True
        return False


class SRPClient:
    N = IETF_DIFFIE_HELLMAN_PRIME
    g = 2

    def sign_up(self, server, username, password):
        salt = os.urandom(16)
        x = self._generate_private_key(username, password, salt)
        verifier = pow(self.g, x, self.N)
        server._respond_to_sign_up_request(username, salt, verifier)

    def log_in(self, server, username, password, k=3):
        a = random.randint(1, self.N - 1)  # private ephemeral number
        A = pow(self.g, a, self.N)  # public ephemeral number
        # B == public ephemeral number from server
        salt, B, u = server._respond_to_login_request(username, A, k=k)

        # TODO: figure out if it is possible to make the offline attack work if
        # the following line is uncommented
        # assert u == scramble_srp_keys(A, B)
        x = self._generate_private_key(username, password, salt)
        S = pow(B - k * pow(self.g, x, self.N), a + u*x, self.N)
        shared_session_key = sha256(int_to_bytes(S)).digest()  # called "K" in challenge
        hmac = get_hmac(shared_session_key, salt, sha256)
        return server._verify_hmac(hmac, username)

    @staticmethod
    def _generate_private_key(username, password, salt):
        inner_hash = sha256((username + ":" + password).encode()).digest()
        return int(sha256(salt + inner_hash).hexdigest(), 16)


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
