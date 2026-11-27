# Covering search for OEIS A000225 "only if" half.
# For modulus E, use primes p with ord_p(2) | E (prime factors of 2^E - 1).
# For L ≡ r (mod E), p | 2^L - 1 - 2^j - 2^k depends only on (j mod e, k mod e, r mod e).
# A covering = every residue pair (a, b) in (Z/E)^2 is hit by some p. Then every L ≡ r (mod E)
# with L large enough would make all the numbers composite (counterexample unless L is a power of 2).
# Usage: python3 cover.py [END] [START]   (default periods 2..64)
import sys
from math import gcd

def factor_small(n, bound=2_000_000):
    fs = []
    p = 2
    while p * p <= n and p < bound:
        while n % p == 0:
            fs.append(p); n //= p
        p += 1 if p == 2 else 2
    return fs, n  # n = leftover cofactor (1 or unfactored/prime)

def is_probable_prime(n):
    if n < 2: return False
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % a == 0: return n == a
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True

def order2(p):
    e, x = 1, 2 % p
    while x != 1:
        x = x * 2 % p; e += 1
    return e

results = []
START = int(sys.argv[2]) if len(sys.argv) > 2 else 2
END = int(sys.argv[1]) if len(sys.argv) > 1 else 64
for E in range(START, END + 1):
    fs, rest = factor_small(2**E - 1)
    primes = sorted(set(fs) | ({rest} if rest > 1 and is_probable_prime(rest) and rest < 10**12 else set()))
    primes = [p for p in primes if p > 2]
    for r in range(E):
        covered = set()
        for p in primes:
            e = order2(p)
            target = (pow(2, r, p) - 1) % p
            for a in range(E):
                for b in range(E):
                    if (pow(2, a, p) + pow(2, b, p)) % p == target:
                        covered.add((a, b))
        if len(covered) == E * E:
            results.append((E, r, primes))
            print("COVERING FOUND: E=%d, L ≡ %d (mod %d), primes %s" % (E, r, E, primes)); sys.stdout.flush()
print("searched E = %d..%d; coverings found: %d" % (START, END, len(results)))
for E, r, ps in results:
    print(" E=%d r=%d (L ≡ r mod E; powers of 2 in this class: %s)" % (E, r, [2**t for t in range(1, 12) if 2**t % E == r]))
