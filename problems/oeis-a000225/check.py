"""List m such that 2^(m+1) - 2^j - 2^k - 1 is not prime for all 0 <= j < k <= m.

Evidence only, not proof. Run with: python3 check.py
"""

LIMIT = 80


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in small:  # deterministic for n < 3.3 * 10^24
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def has_property(m: int) -> bool:
    top = 2 ** (m + 1) - 1
    return all(not is_prime(top - 2**j - 2**k) for k in range(m + 1) for j in range(k))


def main() -> None:
    print([m for m in range(LIMIT + 1) if has_property(m)])


if __name__ == "__main__":
    main()
