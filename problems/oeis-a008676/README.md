# OEIS A008676: partitions into 3s and 5s

**Source:** [OEIS A008676](https://oeis.org/A008676): expansion of 1/((1-x^3)(1-x^5)), i.e. the
number of ways to write n = 3a + 5b with a, b ≥ 0.
**Type:** open conjecture (three conjectured comments on the OEIS page)
**Status:** ✅ fully Lean-checked (`lean/Math/OEIS/A008676.lean`): all three claims, the corrected
version of claim 3, and that `a(n)` is the coefficient of x^n in 1/((1-x^3)(1-x^5)).

## The three claims

1. **Layman (2009), conjecture:** a(n) = ⌊2(n+3)/3⌋ - ⌊3(n+3)/5⌋.
2. **Layman (2009), "it appears":** a(n) is the number of multisets of n-1 integers from
   {-2, 3, 4} whose sum is 2.
3. **Wiseman (2022), "appears to be":** a(n) is the number of ordered triples summing to n with
   2x = 3y + 4z, ranked by A357489 (whose triples are compositions, i.e. positive parts).

## Results

1. **True.** Proof by periodicity modulo 15 (see `NOTES.md`). Caveat: an equivalent formula,
   a(n) = ⌊(2n+5)/5⌋ - ⌊(n+2)/3⌋ (Tani Akinari, 2013), is already listed on the page as a formula,
   and both follow from Popoviciu's theorem (1953) on the number of solutions of ax + by = n. So this
   is open as recorded on OEIS, but not new mathematics.
2. **True.** Short bijection (see `NOTES.md`).
3. **False as stated, true after a shift:** with positive parts (as in A357489), the number of such
   triples summing to n is **a(n-8)**. With nonnegative parts it is a(n).

## Links

- OEIS entry: <https://oeis.org/A008676>
- Checks: `check.py`
