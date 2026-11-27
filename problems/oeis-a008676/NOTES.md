# Notes

Let N(n) = #{(a, b) ∈ ℕ² : 3a + 5b = n}. This is the coefficient of x^n in
1/((1-x^3)(1-x^5)) = (Σ x^(3a))(Σ x^(5b)), so a(n) = N(n).

## Rule check (not already resolved)

Live OEIS entry read on 2026-11-27: Layman's floor formula is still marked "Conjecture" (2009), and
the two other comments say "it appears" / "appears to be". No proof is recorded for any of them.
However:

- the page also lists a(n) = floor((2n+5)/5) - floor((n+2)/3) (Tani Akinari, 2013) as a plain
  formula (no proof given), which equals Layman's formula for every n (see below);
- Popoviciu's theorem (1953) gives N(n) = n/15 - {2n/3} - {2n/5} + 1 for 3a + 5b = n
  ({x} = fractional part), from which both floor formulas follow by algebra.

So claim 1 is open as recorded but implied by known results.

## Claim 1: a(n) = ⌊2(n+3)/3⌋ - ⌊3(n+3)/5⌋

Let R(n) be the right side.

1. **N(n + 15) = N(n) + 1.** Split the solutions of 3a + 5b = n + 15 by a.
   - a ≥ 5: (a, b) ↦ (a - 5, b) is a bijection onto the solutions of 3a + 5b = n.
   - a ≤ 4: we need 5 | n + 15 - 3a. As a runs over 0..4, 3a runs over all residues mod 5, so
     exactly one a works, and then b = (n + 15 - 3a)/5 ≥ 0 since n + 15 - 3a ≥ 3.
   So there is exactly one more solution.
2. **R(n + 15) = R(n) + 1:** ⌊2(n+18)/3⌋ = ⌊2(n+3)/3⌋ + 10 and ⌊3(n+18)/5⌋ = ⌊3(n+3)/5⌋ + 9.
3. **Base cases n = 0..14:** N = 1,0,0,1,0,1,1,0,1,1,1,1,1,1,1 and R gives the same values.

By induction on n in steps of 15, N(n) = R(n) for all n. ∎ The same argument proves Tani
Akinari's formula T(n) = ⌊(2n+5)/5⌋ - ⌊(n+2)/3⌋ (also T(n+15) = T(n) + 1, same base values).

## Claim 2: multisets of n-1 numbers from {-2, 3, 4} summing to 2

A multiset is determined by the counts p, q, r ≥ 0 of -2, 3, 4, with p + q + r = n - 1 and
-2p + 3q + 4r = 2. Eliminating p = n - 1 - q - r gives 5q + 6r = 2n, so q is even, q = 2s, and
5s + 3r = n. Conversely any (s, r) with 3r + 5s = n gives q = 2s, p = n - 1 - 2s - r, and
p ≥ 0 because 2s + r ≤ 5s + 3r - 1 = n - 1 unless s = r = 0 (then n = 0, excluded as n ≥ 1).
So the multisets are in bijection with the solutions of 3r + 5s = n: their number is a(n). ∎

## Claim 3: ordered triples with 2x = 3y + 4z

With x + y + z = n: substituting x = n - y - z gives 2n = 5y + 6z, so y = 2u and n = 5u + 3z.

- Nonnegative x, y, z: (u, z) ranges over the solutions of 3z + 5u = n (and x = n - 2u - z ≥ 0
  holds automatically, as above), so the count is a(n).
- Positive x, y, z (compositions, as in A357489): u, z ≥ 1 and x ≥ 1, so with u' = u - 1,
  z' = z - 1: 3z' + 5u' = n - 8, and x = 3u + 2z ≥ 1 automatically. The count is **a(n-8)**.

So Wiseman's comment, read with A357489's positive parts, should say a(n-8) (or "summing to
n+8"). Checked numerically: the positive-part counts for n = 0..19 are
0,0,0,0,0,0,0,0,1,0,0,1,0,1,1,0,1,1,1,1 = a(n-8).

## Lean progress

- [ ] Claim 1 (`lean/Math/OEIS/A008676.lean`).
- [ ] Claim 2.
- [ ] Claim 3 (both versions).
- [ ] Optional: N(n) equals the power-series coefficient of 1/((1-x^3)(1-x^5)).

## Attempts

## References

- OEIS A008676, A357489.
- Popoviciu's theorem (T. Popoviciu, 1953), as presented in M. Beck and S. Robins, *Computing the
  Continuous Discretely*, Chapter 1.
