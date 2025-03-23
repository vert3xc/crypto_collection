import base64
from Crypto.Util.number import long_to_bytes as l2b, bytes_to_long as b2l, GCD
from Crypto.PublicKey import RSA
from Crypto.Cipher import AES
import hashlib
import random
import sys
import math
import string
from itertools import combinations
from base64 import b64decode
import os
import binascii
import secrets
import json
from datetime import *
import requests
#from sage.all import *

sys.set_int_max_str_digits(10000000)

# factor n knowing private and public key
def factorize_knowing_exps(n, e, d):
    k = d * e - 1
    p = -203
    q = -408
    while True:
        g = random.randint(2, n)
        t = k
        while t % 2 == 0:
            t //= 2
            x = pow(g, t, n)
            y = GCD(x - 1, n)
            if x > 1 and y > 1:
                p = y
                q = n // p
                return p, q


CHARACTER_FREQ = {
    'a': 0.0651738, 'b': 0.0124248, 'c': 0.0217339, 'd': 0.0349835, 'e': 0.1041442, 'f': 0.0197881, 'g': 0.0158610,
    'h': 0.0492888, 'i': 0.0558094, 'j': 0.0009033, 'k': 0.0050529, 'l': 0.0331490, 'm': 0.0202124, 'n': 0.0564513,
    'o': 0.0596302, 'p': 0.0137645, 'q': 0.0008606, 'r': 0.0497563, 's': 0.0515760, 't': 0.0729357, 'u': 0.0225134,
    'v': 0.0082903, 'w': 0.0171272, 'x': 0.0013692, 'y': 0.0145984, 'z': 0.0007836, ' ': 0.1918182
}


def get_english_score(input_bytes):
    score = 0
    for byte in input_bytes:
        score += CHARACTER_FREQ.get(chr(byte).lower(), 0)
    return score


def singlechar_xor(input_bytes, key_value):
    output = b''
    for char in input_bytes:
        output += bytes([char ^ key_value])
    return output


def repeating_key_xor(plaintext, key):
    """Implements the repeating-key XOR encryption."""
    ciphertext = b''
    i = 0

    for byte in plaintext:
        ciphertext += bytes([byte ^ key[i]])

        # Cycle i to point to the next byte of the key
        i = i + 1 if i < len(key) - 1 else 0

    return ciphertext


def egcd(a, b):
    if (a == 0):
        return (b, 0, 1)
    else:
        g, y, x = egcd(b % a, a)
        return (g, x - (b // a) * y, y)



def singlechar_xor_brute_force(ciphertext):
    candidates = []
    for key_candidate in range(256):
        plaintext_candidate = singlechar_xor(ciphertext, key_candidate)
        candidate_score = get_english_score(plaintext_candidate)

        result = {
            'key': key_candidate,
            'score': candidate_score,
            'plaintext': plaintext_candidate
        }

        candidates.append(result)
    return sorted(candidates, key=lambda c: c['score'], reverse=True)[0]


def distance(s, s1):
    count = 0
    for i, j in zip(s, s1):
        count += int(i) ^ int(j)
    return count


def break_repeating_key_xor(binary_data):
    """Breaks the repeating key XOR encryption statistically."""
    normalized_distances = {}

    # For each key_size (from the suggested range)
    for key_size in range(2, 41):

        # Take the first four key_size worth of bytes (as suggested as an option)
        chunks = [binary_data[i:i + key_size] for i in range(0, len(binary_data), key_size)][:4]

        # Sum the hamming distances between each pair of chunks
        dist = 0
        pairs = combinations(chunks, 2)
        for (x, y) in pairs:
            dist += distance(x, y)

        # And compute the average distance
        dist /= 6

        # Normalize the result by dividing by key_size
        normalized_distance = dist / key_size

        # Store the normalized distance for the given key_size
        normalized_distances[key_size] = normalized_distance

    # The key_sizes with the smallest normalized edit distances are the most likely ones
    possible_key_sizes = sorted(normalized_distances, key=normalized_distances.get)[:3]
    possible_plaintexts = []

    # Now we can try which one is really the correct one among the top 3 most likely key_sizes
    for d in possible_key_sizes:
        key = b''

        # Break the ciphertext into blocks of key_size length
        for i in range(d):
            block = b''

            # Transpose the blocks: make a block that is the i-th byte of every block
            for j in range(i, len(binary_data), d):
                block += bytes([binary_data[j]])

            # Solve each block as if it was single-character XOR
            key += bytes([singlechar_xor_brute_force(block)['key']])

        # Store the candidate plaintext that we would get with the key that we just found
        possible_plaintexts.append((repeating_key_xor(binary_data, key), key))

    # Return the candidate with the highest English score
    return max(possible_plaintexts, key=lambda k: get_english_score(k[0]))


# padding
def pkcs7(data, block_size=16):
    return data + bytes([block_size - len(data) % block_size] * (block_size - len(data) % block_size))


# find the length of the prefix if given an AES ECB oracle
def find_pref_len(cipher):
    a = cipher.encrypt(b'')
    b = cipher.encrypt(b'a')
    pref_block = -1
    prefix_length = -1
    for i in range(0, len(b), 16):
        if a[i:i + 16] != b[i:i + 16]:
            pref_block = i
    for i in range(100000):
        c = b'a' * (32 + i)
        d = cipher.encrypt(c)
        if d[pref_block + 16: pref_block + 32] == d[pref_block + 32: pref_block + 48]:
            return 16 - i + pref_block


def is_pkcs7_valid(data):
    return all(data[-data[-1]:][i] == len(data[-data[-1]:]) for i in range(len(data[-data[-1]:])))


BLOCK_SIZE = 16


# decrypt 1 block of ciphertext encrypted with CBC given access to an oracle that checks
# whether the provided ciphertext's padding is valid
def single_block_attack(block, oracle):
    zeroing_iv = [0] * BLOCK_SIZE
    print("working..")
    for pad_val in range(1, BLOCK_SIZE + 1):
        print("working1...")
        padding_iv = [pad_val ^ b for b in zeroing_iv]
        for candidate in range(256):
            padding_iv[-pad_val] = candidate
            iv = bytes(padding_iv)
            if oracle(iv, block):
                if pad_val == 1:
                    padding_iv[-2] ^= 1
                    iv = bytes(padding_iv)
                    if not oracle(iv, block):
                        continue
                break
        else:
            raise Exception("no valid padding byte found (is the oracle working correctly?)")
        zeroing_iv[-pad_val] = candidate ^ pad_val
    return zeroing_iv


# decrypt ciphertext encrypted with CBC given access to an oracle that checks
# whether the provided ciphertext's padding is valid
def cbc_oracle_padding(iv, ct, oracle):
    assert len(iv) == BLOCK_SIZE and len(ct) % BLOCK_SIZE == 0
    msg = iv + ct
    blocks = [msg[i:i + BLOCK_SIZE] for i in range(0, len(msg), BLOCK_SIZE)]
    result = b''
    iv = blocks[0]
    for ct in blocks[1:]:
        dec = single_block_attack(ct, oracle)
        print(dec)
        pt = bytes(iv_byte ^ dec_byte for iv_byte, dec_byte in zip(iv, dec))
        result += pt
        iv = ct

    return result


# chinese remainder theorem
def crt(list_a, list_m):
    try:
        assert len(list_a) == len(list_m)
    except:
        print("[+] Length of list_a should be equal to length of list_m")
        return -1
    for i in range(len(list_m)):
        for j in range(len(list_m)):
            if GCD(list_m[i], list_m[j]) != 1 and i != j:
                print("[+] Moduli should be pairwise co-prime")
                return -1
    M = 1
    for i in list_m:
        M *= i
    list_b = [M // i for i in list_m]
    assert len(list_b) == len(list_m)
    list_b_inv = [int(pow(list_b[i], -1, list_m[i])) for i in range(len(list_m))]
    x = 0
    for i in range(len(list_m)):
        x += list_a[i] * list_b[i] * list_b_inv[i]
    return x % M


# not too useful but may be helpful to parse json
def json_recv(r):
    line = r.recvline().decode()
    if '{' != line[0] or '}' != line[-1]:
        return line
    return json.loads(line)


def json_send(r, hsh):
    request = json.dumps(hsh).encode()
    r.sendline(request)


def byte_xor(ba1, ba2):
    return bytes([_a ^ _b for _a, _b in zip(ba1, ba2)])


# vector class used mainly for lattices and reduction techniques
class Vector:
    """
    a simple class for vectors
    """

    def __init__(self, vec: tuple):
        self.vector = vec

    def __add__(self, other):
        return Vector(tuple([self.vector[i] + other.vector[i] for i in range(len(other.vector))]))

    def __mul__(self, other):
        if isinstance(other, Vector):
            res = 0
            for i in range(len(other.vector)):
                res += self.vector[i] * other.vector[i]
        elif isinstance(other, int):
            res = Vector(tuple([self.vector[i] * other for i in range(len(self.vector))]))
        else:
            raise ValueError("not supported")
        return res

    def __rmul__(self, other):
        return Vector(tuple([self.vector[i] * other for i in range(len(self.vector))]))

    def __sub__(self, other):
        return Vector(tuple([self.vector[i] - other.vector[i] for i in range(len(other.vector))]))

    def __repr__(self):
        return f"Vector {self.vector}"

    def size(self):
        return pow(self * self, 0.5)


# sum of a list of vectors
def sum_vec(l: list[Vector]):
    res = Vector(tuple([0] * len(l[0].vector)))
    for i in l:
        res = res + i
    return res


# don't actually remember what this does lol(but might be useful for some operations involving lattices/vectors)
def gram_schmidt(v: list[Vector]):
    u = [v[0]]
    for vi in v[1:]:
        mi = [(vi * uj) / (uj * uj) for uj in u]
        u += [vi - sum_vec([mij * uj for (mij, uj) in zip(mi, u)])]
    return u


# basic lattice reduction algorithm used to solve the shortest vector problem
def gaussian_reduction(v1: Vector, v2: Vector):
    if v1.size() > v2.size():
        v1, v2 = v2, v1
    m = round((v1 * v2) / (v1 * v1))
    if m == 0:
        return v1, v2
    v2 = v2 - m * v1
    return gaussian_reduction(v1, v2)


# function to check whether an elliptic curve is vulnerable to pohlig hellman's attack
def check_pohlig_hellman(curve, generator=None):
    """
    The Pohlig-Hellman algorithm allows for quick (EC)DLP solving if the order of the curve is smooth,
    i.e its order is a product of multiple (small) primes.
    The best general purpose algorithm for finding a discrete logarithm is the Baby-step giant-step
    algorithm, with a running time of O(sqrt(n)).
    If the order of the curve (over a finite field) is smooth, we can however solve the (EC)DLP
    algorithm by solving the (EC)DLP for all the prime powers that make up the order, then using the
    Chinese remainder theorem to compute the (EC)DLP solution to our original order.
    If no generator is provided, we assume a cofactor of 1, and thus a generator subgroup order equal to the curve order.
    """

    if generator:
        order = generator.order()
    else:
        order = curve.order()
    factorization = factor(order)

    # baby-step giant-step complexity is O(sqrt(n))
    naive_complexity = order.nth_root(2, True)[0] + 1

    # for an order N = (p_0)^(e_0) * (p_1)^(e_1) * ... * (p_k)^(e^k) with p prime and e natural the complexity is:
    # O( \sum_{i=0}^k e_i ( log_2(n) + sqrt((p_i)) ) )

    logn = log(order, 2)

    pohlig_hellman_complexity = sum(y * (logn + x.nth_root(2, True)[0]) for x, y in factorization)

    return (pohlig_hellman_complexity, naive_complexity)


# function to check whether an elliptic curve is vulnerable to smart's attack
def check_smart(curve):
    """
    The Smart attack allows for solving the ECDLP in linear time, given that the trace of Frobenius of the curve equals one,
    i.e the order of the curve is equal to the order of the finite field over which the elliptic curve is defined.
    If this is the case, we can create a group isomorphism from our curve E over Fp to the finite field Fp (which preserves addition).
    Solving the discrete 'log' problem in a finite field is easy, when our group is an additive one.
    Finding `m` such that mQ = P given P, Q is hard in an elliptic curve defined over a finite field, but easy over a finite field an sich:
    m = P * modinv(Q)
    """

    return curve.trace_of_frobenius() == 1


# function to check wheter an elliptic curve is vulnerable to MOV's attack
def check_mov(curve):
    """
    The MOV attack (Menezes, Okamoto, Vanstone) allows for solving the ECDLP in subexponential time, given that the trace of frobenius of the curve equals zero,
    i.e the curve is supersingular.
    If this is the case we can reduce the problem to the discrete logarithm problem in the finite field over which the curve is defined. Subexponential attacks are known.
    This differs from the smart attack in the sense that we have to solve the actual multiplicative discrete log problem Q^m = P,
    instead of the additive discrete log problem mQ = P
    """

    return curve.trace_of_frobenius() == 0


# function to check whether an elliptic curve is vulnerable to any of the attacks listed
# NOTE: actually is not too accurate, curves that may seem not vulnerable for this function
# may be vulnerable to attacks listed here
def check(curve, generator=None):
    def print_red(p):
        print("\u001b[41m" + str(p) + "\u001b[0m")

    ph = check_pohlig_hellman(curve, generator)

    if ph[0] < ph[1]:
        quotient = round(float(ph[1] / ph[0]), 2) - 1

        logs = [round(float(log(x, 2)), 2) for x in ph]

        print_red(f"Pohlig-Hellman can make ECDLP solving {quotient} times faster!")
        print(f"O(2^{logs[1]}) -> O(2^{logs[0]})")

    else:
        print("Pohlig-Hellman cannot improve ECDLP solving speed.")

    smart = check_smart(curve)

    if smart:
        print_red("Smart's attack can solve ECDLP in linear time!")
    else:
        print("Smart's attack does not apply.")

    mov = check_mov(curve)

    if mov:
        print_red("MOV attack can solve ECDLP in subexponential time!")
    else:
        print("MOV attack does not apply.")


# function to convert n to base b(used in cipolla's algorithm)
def convertToBase(n, b):
    if (n < 2):
        return [n]
    temp = n
    ans = []
    while (temp != 0):
        ans = [temp % b] + ans
        temp //= b
    return ans


# Takes integer n and odd prime p
# Returns both square roots of n modulo p as a pair (a,b)
# Returns () if no root
# very fast and useful
def cipolla(n, p):
    n %= p
    if (n == 0 or n == 1):
        return (n, -n % p)
    phi = p - 1
    if (pow(n, phi // 2, p) != 1):
        return ()
    if (p % 4 == 3):
        ans = pow(n, (p + 1) // 4, p)
        return (ans, -ans % p)
    aa = 0
    for i in range(1, p):
        temp = pow((i * i - n) % p, phi // 2, p)
        if (temp == phi):
            aa = i
            break
    exponent = convertToBase((p + 1) // 2, 2)

    def cipollaMult(a, b, c, d, w, p):
        return ((a * c + b * d * w) % p, (a * d + b * c) % p)

    x1 = [aa, 1]
    x2 = list(cipollaMult(*x1, *x1, aa * aa - n, p))
    for i in range(1, len(exponent)):
        if (exponent[i] == 0):
            x2 = list(cipollaMult(*x2, *x1, aa * aa - n, p))
            x1 = list(cipollaMult(*x1, *x1, aa * aa - n, p))
        else:
            x1 = list(cipollaMult(*x1, *x2, aa * aa - n, p))
            x2 = list(cipollaMult(*x2, *x2, aa * aa - n, p))
    return (x1[0], -x1[0] % p)


# round function used in pollard's rho discrete logarithm algorithm
def pollard_f(g, h, x, p):
    x %= p
    if x < p // 3:
        return g * x
    elif p // 3 <= x < (2 * p) // 3:
        return x**2
    elif (2 * p) // 3 <= x < p:
        return h * x

# round function used in pollard's rho discrete logarithm algorithm
def pollard_a(a, xi, p):
    a %= (p - 1)
    if 0 <= xi < p // 3:
        return (a + 1) % (p - 1)
    elif p // 3 <= xi < (2 * p) // 3:
        return (a * 2) % (p - 1)
    elif (2 * p) // 3 <= xi < p:
        return a % (p - 1)


# round function used in pollard's rho discrete logarithm algorithm
def pollard_b(b, xi, p):
    b %= (p - 1)
    if 0 <= xi < p // 3:
        return b % (p - 1)
    elif p // 3 <= xi < (2 * p) // 3:
        return (b * 2) % (p - 1)
    elif (2 * p) // 3 <= xi < p:
        return (b + 1) % (p - 1)


# complete pollard's rho algorithm for solving discrete logarithms(not too useful)
def pollard_rho(g, h, p):
    xi = 1
    yi = 1
    ai = 0
    bi = 0
    gi = 0
    si = 0
    while yi != xi:
        xi = pollard_f(g, h, xi, p)
        yi = pollard_f(g, h, pollard_f(g, h, yi, p), p)
        ai = pollard_a(ai, xi, p)
        bi = pollard_b(bi, xi, p)
        gi = pollard_a(pollard_a(gi, xi, p), xi, p)
        si = pollard_b(pollard_b(si, xi, p), si, p)
    u = (ai - gi) % (p - 1)
    v = (si - bi) % (p - 1)
    if GCD(v, p - 1) == 1:
        return (u * pow(v, -1, p - 1)) % (p - 1)
    else:
        d = GCD(v, p - 1)
        s = egcd(v, p - 1)[1]
        assert (s * v) % (p - 1) == d % (p - 1)
        x = ((s * u) % (p - 1)) // d
        while pow(g, x, p) != h % p:
            x = x + ((p - 1) // d)
        return x


# function to extend a fraction to a continued one
def continued_fraction(num, den):
    cf = []
    while den != 0:
        q = num // den
        cf.append(q)
        num, den = den, num - q * den
    return cf


# derive convergents from a continued fraction
def convergents_from_cf(cf):
    n0, d0 = 0, 1
    n1, d1 = 1, 0
    yield (n0, d0)
    yield (n1, d1)
    for a_k in cf:
        n2 = a_k * n1 + n0
        d2 = a_k * d1 + d0
        yield (n2, d2)
        n0, d0 = n1, d1
        n1, d1 = n2, d2


def main():
    g = 2
    h = 424242
    p = 1726565507
    x = pollard_rho(g, h, p)
    print(x)
    print(pow(g, x, p) == h)

if __name__ == "__main__":
    main()
