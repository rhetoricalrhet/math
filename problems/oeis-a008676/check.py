"""Numerical checks of the three conjectured comments on OEIS A008676.

Evidence only; the proofs are in NOTES.md and lean/. Run with: python3 check.py
"""


def a(n: int) -> int:
    """Number of (a, b) >= 0 with 3a + 5b = n."""
    return sum(1 for b in range(n // 5 + 1) if (n - 5 * b) % 3 == 0) if n >= 0 else 0


def layman(n: int) -> int:
    return (2 * (n + 3)) // 3 - (3 * (n + 3)) // 5


def akinari(n: int) -> int:
    return (2 * n + 5) // 5 - (n + 2) // 3


def multisets(n: int) -> int:
    m = n - 1
    return sum(1 for q in range(m + 1) for r in range(m + 1 - q) if -2 * (m - q - r) + 3 * q + 4 * r == 2)


def triples(n: int, lo: int) -> int:
    return sum(1 for y in range(lo, n + 1) for z in range(lo, n + 1 - y)
               if (x := n - y - z) >= lo and 2 * x == 3 * y + 4 * z)


def main() -> None:
    print("claim 1, Layman formula, n < 5000:", all(a(n) == layman(n) for n in range(5000)))
    print("Akinari formula, n < 5000:", all(a(n) == akinari(n) for n in range(5000)))
    print("claim 2, multisets, 1 <= n < 200:", all(multisets(n) == a(n) for n in range(1, 200)))
    print("claim 3, nonnegative parts give a(n), n < 200:", all(triples(n, 0) == a(n) for n in range(200)))
    print("claim 3, positive parts give a(n-8), n < 200:", all(triples(n, 1) == a(n - 8) for n in range(200)))
    print("claim 3 as worded (positive parts give a(n)):", all(triples(n, 1) == a(n) for n in range(200)))


if __name__ == "__main__":
    main()
