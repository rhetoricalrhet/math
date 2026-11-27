"""Check perm(M_n) = 2^n + 1 for small n, M(j, k) = -floor((j - k - 2)/(n + 1)).

Evidence only, not proof. Run with: python3 check.py
"""

import itertools
import math
from fractions import Fraction


def permanent(m):
    n = len(m)
    return sum(math.prod(m[i][s[i]] for i in range(n)) for s in itertools.permutations(range(n)))


def main() -> None:
    for n in range(8):
        size = n + 1
        m = [[-math.floor(Fraction(j - k - 2, size)) for k in range(size)] for j in range(size)]
        p = permanent(m)
        print(n, p, 2**n + 1, "ok" if p == 2**n + 1 else "MISMATCH")


if __name__ == "__main__":
    main()
