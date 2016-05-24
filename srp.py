from hashlib import sha256
from os import urandom

from util import IETF_DIFFIE_HELLMAN_PRIME, get_hmac, int_to_bytes, random

class Server:
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
        u = scramble_keys(A, B)
        S = pow(A * pow(user["verifier"], u, self.N), b, self.N)
        user["shared_session_key"] = sha256(int_to_bytes(S)).digest()
        return (user["salt"], B, u)

    def _verify_hmac(self, hmac, username):
        user = self.users[username]
        return hmac == get_hmac(user["shared_session_key"], user["salt"], sha256)


class MitmServer(Server):
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
            test_x = generate_private_key(username, test_password, user["salt"])
            test_verifier = pow(self.g, test_x, self.N)
            test_S = pow(user["A"] * pow(test_verifier, u, self.N), user["b"], self.N)
            test_session_key = sha256(int_to_bytes(test_S)).digest()
            if get_hmac(test_session_key, user["salt"], sha256) == hmac:
                user["password"] = test_password
                return True
        return False


class Client:
    N = IETF_DIFFIE_HELLMAN_PRIME
    g = 2

    def sign_up(self, server, username, password):
        salt = urandom(16)
        x = generate_private_key(username, password, salt)
        verifier = pow(self.g, x, self.N)
        server._respond_to_sign_up_request(username, salt, verifier)

    def log_in(self, server, username, password, k=3):
        a = random.randint(1, self.N - 1)  # private ephemeral number
        A = pow(self.g, a, self.N)  # public ephemeral number
        # B == public ephemeral number from server
        salt, B, u = server._respond_to_login_request(username, A, k=k)

        # TODO: figure out if it is possible to make the offline attack work if
        # the following line is uncommented
        # assert u == scramble_keys(A, B)
        x = generate_private_key(username, password, salt)
        S = pow(B - k * pow(self.g, x, self.N), a + u*x, self.N)
        shared_session_key = sha256(int_to_bytes(S)).digest()  # called "K" in challenge
        hmac = get_hmac(shared_session_key, salt, sha256)
        return server._verify_hmac(hmac, username)


def generate_private_key(username, password, salt):
    inner_hash = sha256((username + ":" + password).encode()).digest()
    return int(sha256(salt + inner_hash).hexdigest(), 16)


def scramble_keys(A, B):
    return int(sha256(int_to_bytes(A) + int_to_bytes(B)).hexdigest(), 16)
