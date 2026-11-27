"""Search for n = P(a) + P(b) + P(c), P(k) = k(k+1)(2k+1)/6, k any integer.

Evidence only, not proof. Run with: python3 check.py
"""

BOUND = 200  # |index| bound; raise it for stubborn n (memory grows like BOUND^2)


def P(k: int) -> int:
    return k * (k + 1) * (2 * k + 1) // 6


def main() -> None:
    vals = sorted({P(k) for k in range(-BOUND, BOUND + 1)})
    pairs = {a + b for a in vals for b in vals}
    missing = [n for n in range(0, 301) if not any(n - c in pairs for c in vals)]
    print(f"n in 0..300 with no representation, |index| <= {BOUND}:", missing)


if __name__ == "__main__":
    main()
