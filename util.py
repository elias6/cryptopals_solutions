import decimal
import os
import pprint
import re
import struct

from collections import Counter, defaultdict, namedtuple
from functools import lru_cache
from hashlib import md5, sha256
from heapq import nlargest
from http.server import BaseHTTPRequestHandler, HTTPServer
from itertools import count, cycle
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


def pp(*args, width=120, **kwargs):
    pprint.pprint(*args, width=width, **kwargs)


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


# Character frequencies were taken from raw letter averages at
# http://www.macfreek.nl/memory/Letter_Distribution, then rounded to 6
# decimal places for readability. Numbers for control characters (\x00
# through \x1f excluding tab (\x09), newline (\x0a), and carriage return
# (\x0d)) were added by me after observing better results. Text should
# be converted to lowercase before one attempts to analyze it using this
# dictionary.
english_byte_frequencies = defaultdict(
    # The following number will be returned for any byte not explicitly
    # represented. 4e-6 was observed to produce the best ratio of score for
    # English text to score for incorrectly decrypted text.
    lambda: 4e-6,
    {ord(char): freq for char, freq in {
        "\x00": 1e-6, "\x01": 1e-6, "\x02": 1e-6, "\x03": 1e-6, "\x04": 1e-6,
        "\x05": 1e-6, "\x06": 1e-6, "\x07": 1e-6, "\x08": 1e-6, "\x0b": 1e-6,
        "\x0c": 1e-6, "\x0e": 1e-6, "\x0f": 1e-6, "\x10": 1e-6, "\x11": 1e-6,
        "\x12": 1e-6, "\x13": 1e-6, "\x14": 1e-6, "\x15": 1e-6, "\x16": 1e-6,
        "\x17": 1e-6, "\x18": 1e-6, "\x19": 1e-6, "\x1a": 1e-6, "\x1b": 1e-6,
        "\x1c": 1e-6, "\x1d": 1e-6, "\x1e": 1e-6, "\x1f": 1e-6,
        " ": 0.183169, "a": 0.065531, "b": 0.012708, "c": 0.022651, "d": 0.033523,
        "e": 0.102179, "f": 0.019718, "g": 0.016359, "h": 0.048622, "i": 0.057343,
        "j": 0.001144, "k": 0.005692, "l": 0.033562, "m": 0.020173, "n": 0.057031,
        "o": 0.062006, "p": 0.015031, "q": 0.000881, "r": 0.049720, "s": 0.053263,
        "t": 0.075100, "u": 0.022952, "v": 0.007880, "w": 0.016896, "x": 0.001498,
        "y": 0.014700, "z": 0.000598
    }.items()})


def english_like_score(text_bytes):
    # english_byte_frequencies is defined outside of this function as a
    # performance optimization. In my tests, the time spent in this function
    # is less than half of what it would be if english_byte_frequencies were
    # defined inside this function. I am also using a defaultdict instead of
    # a Counter for the byte counts as a performance optimization.
    byte_counts = defaultdict(int)
    for byte in text_bytes.lower():
        byte_counts[byte] += 1
    text_length = len(text_bytes)
    chi_squared = 0
    for byte, byte_count in byte_counts.items():
        expected = text_length * english_byte_frequencies[byte]
        difference = byte_count - expected
        chi_squared += difference * difference / expected
    return 1e6 / chi_squared / text_length


def english_like_score_data(ciphertext):
    result = []
    for i in range(256):
        message = xor_encrypt(ciphertext, bytes([i]))
        score = english_like_score(message)
        result.append({"key": i, "message": message, "score": score})
    return result


def best_english_like_score_data(ciphertext):
    return max(english_like_score_data(ciphertext), key=lambda x: x["score"])


def looks_like_ecb(ciphertext, block_size=16):
    # TODO: use birthday paradox to calculate an estimate for the expected
    # number of duplicate blocks so this function works on big ciphertexts.
    block_counter = Counter(chunks(ciphertext, block_size))
    return block_counter.most_common(1)[0][1] > 1


def crack_common_xor_key(ciphertexts):
    key = bytearray()
    for i in range(max(len(c) for c in ciphertexts)):
        transposed_block = bytes(c[i] for c in ciphertexts if i < len(c))
        key.append(best_english_like_score_data(transposed_block)["key"])
    plaintexts = [xor_encrypt(c, key) for c in ciphertexts]
    return (plaintexts, key)


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


def random_aes_key():
    return os.urandom(16)


def appears_to_produce_ecb(oracle_fn, block_size=16):
    return any(looks_like_ecb(oracle_fn(b"A" * i), block_size) for i in range(1000))


def guess_block_size(oracle_fn):
    seen_sizes = set()
    for plaintext_size in range(33):
        ciphertext = oracle_fn(os.urandom(plaintext_size))
        seen_sizes.add(len(ciphertext))
    if len(seen_sizes) >= 2:
        result = 0
        for size in seen_sizes:
            result = gcd(result, size)
        return result
    else:
        raise ValueError("Could not guess block size")


def crack_ecb_oracle(oracle_fn, block_size=16, prefix_length=0):
    assert appears_to_produce_ecb(oracle_fn, block_size)

    result = bytearray()
    while True:
        short_block_length = (block_size - len(result) - 1 - prefix_length) % block_size
        short_input_block = b"A" * short_block_length
        short_block_output = oracle_fn(short_input_block)
        block_index = (len(result) + prefix_length) // block_size
        block_to_look_for = chunks(short_block_output)[block_index]
        for i in range(256):
            test_input = short_input_block + result + bytes([i])
            output = oracle_fn(test_input)
            telltale_block = chunks(output)[block_index]
            if telltale_block == block_to_look_for:
                result.append(i)
                break
        else:  # if no byte matches
            return pkcs7_unpad(result)


def ctr_iterator(nonce, block_index=0):
    return (struct.pack("<QQ", nonce, i) for i in count(start=block_index))


def ctr_counter(nonce, block_index=0):
    # This is roughly equivalent to the following code:
    # return Crypto.Util.Counter.new(
    #     nbits=64, prefix=struct.pack("<Q", nonce), initial_value=block_index,
    #     little_endian=True)
    # I prefer to use my own implementation because it is simpler, more
    # readable, and good enough for my purposes. The nonce and the counter
    # are encoded as 64-bit little-endian integers. I am returning the
    # iterator's __next__ method instead of the iterator itself because
    # PyCrypto's CTR implementation requires a function that returns a new
    # value each time it is called.
    return ctr_iterator(nonce, block_index).__next__


class MT19937_RNG:
    """Mersenne Twister random number generator"""

    def __init__(self, seed):
        self.index = 624
        buffer = self.buffer = [seed] + [0]*623
        prev = seed
        for i in range(1, 624):
            prev = buffer[i] = 0xffffffff & (1812433253 * (prev ^ (prev >> 30)) + i)

    def get_number(self):
        if self.index >= 624:
            self.twist()
        result = self.temper(self.buffer[self.index])
        self.index += 1
        return result

    def twist(self):
        buffer = self.buffer
        for i in range(624):
            y = ((buffer[i] & 0x80000000) +
                       (buffer[(i + 1) % 624] & 0x7fffffff))
            buffer[i] = buffer[(i + 397) % 624] ^ (y >> 1)

            if y & 1:
                buffer[i] ^= 0x9908b0df
        self.index = 0

    @staticmethod
    def temper(x):
        x ^= (x >> 11)
        x ^= (x << 7) & 0x9d2c5680
        x ^= (x << 15) & 0xefc60000
        x ^= (x >> 18)
        return x

    @staticmethod
    def untemper(x):
        x ^= (x >> 18)

        x ^= (x << 15) & 0xefc60000

        x ^= (x << 7) & 0x9d2c5680
        x ^= (x << 14) & 0x94284000
        x ^= (x << 28) & 0x10000000

        x ^= (x >> 11)
        x ^= (x >> 22)
        return x


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
