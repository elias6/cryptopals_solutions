from collections import defaultdict
from heapq import nlargest
from http.server import BaseHTTPRequestHandler, HTTPServer
from multiprocessing.dummy import Pool as ThreadPool
from socketserver import ThreadingMixIn
from statistics import median
from time import perf_counter, sleep
from urllib.error import HTTPError
from urllib.parse import parse_qs, urlencode, urlparse
from urllib.request import urlopen

from util import get_hmac, xor_encrypt


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
