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
        result = temper(self.buffer[self.index])
        self.index += 1
        return result

    def twist(self, limit=624):
        # limit makes this function only twist part of the buffer, instead of
        # the whole buffer. This is a performance optimization for code that
        # cracks the RNG by examining its output, and not intended for normal
        # use of the RNG.
        buffer = self.buffer
        for i in range(limit):
            y = ((buffer[i] & 0x80000000) +
                       (buffer[(i + 1) % 624] & 0x7fffffff))
            buffer[i] = buffer[(i + 397) % 624] ^ (y >> 1)

            if y & 1:
                buffer[i] ^= 0x9908b0df
        self.index = 0


def temper(x):
    x ^= (x >> 11)
    x ^= (x << 7) & 0x9d2c5680
    x ^= (x << 15) & 0xefc60000
    x ^= (x >> 18)
    return x


def untemper(x):
    x ^= (x >> 18)

    x ^= (x << 15) & 0xefc60000

    x ^= (x << 7) & 0x9d2c5680
    x ^= (x << 14) & 0x94284000
    x ^= (x << 28) & 0x10000000

    x ^= (x >> 11)
    x ^= (x >> 22)
    return x
