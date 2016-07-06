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

from util import calculate_hmac, chunks, pretty_hex_bytes


def insecure_compare(data1, data2, delay):
    if len(data1) != len(data2):
        return False
    for byte1, byte2 in zip(data1, data2):
        if byte1 != byte2:
            return False
        sleep(delay)
    return True


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
                hmac = calculate_hmac(self.server.hmac_key, data)
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


class Server(ThreadingMixIn, HTTPServer):
    # Increase request_queue_size so server can handle many simultaneous
    # connections without crashing.
    request_queue_size = 128

    def __init__(self, server_address, hmac_key, validate_signature, *args, **kwargs):
        self.hmac_key = hmac_key
        self.validate_signature = validate_signature
        super().__init__(server_address, ValidatingRequestHandler, *args, **kwargs)

    def serve_forever(self, *args, **kwargs):
        print("Server is running on {}".format(self.server_address))
        super().serve_forever(*args, **kwargs)


def server_approves_of_signature(server_address, filename, signature):
    query = urlencode({"file": filename, "signature": signature.hex()})
    url = "http://{}:{}/signature_is_valid?{}".format(
        server_address[0], server_address[1], query)
    try:
        urlopen(url)
    except HTTPError:
        return False
    else:
        return True


class CantRecoverSignatureError(Exception):
    pass


def pretty_status(sig, attempt_count, duration_difference, byte_was_recovered=True):
    return ("recovered so far: {}{}, {} {} for last byte, {:.3f} ms difference").format(
        pretty_hex_bytes(sig),
        "" if byte_was_recovered else " ?",
        attempt_count,
        "attempt" if attempt_count == 1 else "attempts",
        1000 * duration_difference
    )


def recover_signature(validate_signature, thread_count, threshold, attempt_limit, retry_limit):
    # TODO: make this function figure out threshold on its own

    def try_signature(sig):
        start_time = perf_counter()
        is_valid = validate_signature(sig)
        duration = perf_counter() - start_time
        return {"signature": sig, "is_valid": is_valid, "duration": duration}

    result = bytearray()
    sig_durations = defaultdict(list)
    retry_count = 0
    with ThreadPool(thread_count) as pool:
        while True:
            test_sigs = [(bytes(list(result) + [b])).ljust(20, b"\x00") for b in range(256)]
            for i in range(attempt_limit):
                for sig_data in pool.imap_unordered(try_signature, test_sigs):
                    sig = sig_data["signature"]
                    if sig_data["is_valid"]:
                        print("signature recovered: {}".format(pretty_hex_bytes(sig)))
                        return sig
                    sig_durations[sig].append(sig_data["duration"])
                slowest_sig, second_slowest_sig = nlargest(
                    2, test_sigs, key=lambda x: median(sig_durations[x]))
                slowest_duration = median(sig_durations[slowest_sig])
                second_slowest_duration = median(sig_durations[second_slowest_sig])
                duration_difference = slowest_duration - second_slowest_duration
                if duration_difference > threshold:
                    result.append(slowest_sig[len(result)])
                    print(pretty_status(
                        result, len(sig_durations[slowest_sig]), duration_difference))
                    if len(result) >= 20:
                        print("result is too long, starting over, retry count: {}".format(
                            retry_count))
                        retry_count += 1
                        result = bytearray()
                    break
            else:
                print(pretty_status(
                    result, len(sig_durations[slowest_sig]), duration_difference,
                    byte_was_recovered=False))
                if retry_count < retry_limit:
                    retry_count += 1
                    result = bytearray()
                    print("starting over, retry count: {}".format(retry_count))
                else:
                    raise CantRecoverSignatureError("can't recover signature")
