# Notes

Conjecture (Chai Wah Wu): for `L = m + 1`, every number `2^L - 1 - 2^j - 2^k` (`0 ≤ j < k < L`)
is not prime **iff** `L` is a power of 2 and `L ≠ 4`.

In binary: `2^L - 1` is `L` ones; subtracting `2^j + 2^k` switches two of them off. The question
is for which lengths `L` every such number is not prime.

## The "if" half: proved (informal)

Let `L = 2^t` with `L ≥ 8`, and `0 ≤ j < k < L`. Write `k - j = 2^i · u` with `u` odd; then
`i < t`. Let `F_i = 2^(2^i) + 1` (a Fermat number).

1. `2^(2^i) ≡ -1 (mod F_i)`, so `2^(k-j) = (2^(2^i))^u ≡ (-1)^u = -1`, hence
   `F_i | 2^j (2^(k-j) + 1) = 2^j + 2^k`.
2. `2^L - 1 = 2^(2^t) - 1 = F_0 F_1 ⋯ F_(t-1)`, so `F_i | 2^L - 1` (as `i < t`).
3. So `F_i` divides `v = 2^L - 1 - 2^j - 2^k`.
4. `F_i ≤ F_(t-1) = 2^(L/2) + 1` and `v ≥ 2^L - 1 - 2^(L-2) - 2^(L-1) = 2^(L-2) - 1`. For `L ≥ 8`,
   `2^(L-2) - 1 > 2^(L/2) + 1`, so `1 < F_i < v` and `v` is composite.

Small cases: `L = 1` (no pairs) and `L = 2` (only `v = 0`) hold trivially; `L = 4` fails because
`v` can equal a Fermat number itself (`15 - 2 - 8 = 5 = F_1`, prime). This is why `a(2) = 3` is
excluded.

Checked numerically for every `j < k < L`, `L = 8, 16, ..., 128`.

## The "only if" half: open

For every `L` that is not a power of 2 (`L ≥ 3`), some `2^L - 1 - 2^j - 2^k` should be prime.

- Evidence: true for every such `L` from 3 to 399 (probable-prime test).
- Why it is hard: it asserts that a prime exists in a family of numbers for every `L`, like
  Sierpinski/Riesel-type questions, for which no general method is known.
- How it could be disproved: a length `L` (not a power of 2) with a finite set of primes covering
  every pair `(j, k)`, the way the Fermat numbers do for `L = 2^t`. Searching for such a covering
  is the realistic way to resolve the conjecture.

### Partial result: the Fermat-style covering only works for powers of 2

Claim: if `L` is not a power of 2, no prime factor of `2^L - 1` divides any of the numbers with
gap `k - j = 2^s`, where `s = v_2(L)`.

Proof: such `p` would need `2^(k-j) ≡ -1 (mod p)` (because `p | 2^L - 1` turns the condition into
`p | 2^j + 2^k`). Then `p | 2^(2d) - 1` and `p | 2^L - 1` with `d = 2^s`, so
`p | 2^g - 1` for `g = gcd(2d, L) = 2^s` (as `L / 2^s` is odd). So `2^d ≡ 1`, contradicting
`2^d ≡ -1` for odd `p`. Since `L` is not a power of 2, `d = 2^s < L`, so such pairs exist. ∎

So a counterexample would have to use primes that do **not** divide `2^L - 1`.

### Covering search (`cover.py`)

For a period `E`, take the primes `p` with `ord_p(2) | E`. For `L ≡ r (mod E)`, whether
`p | 2^L - 1 - 2^j - 2^k` depends only on `(j, k, r) mod ord_p(2)`. A covering of all residue
pairs `(a, b) ∈ (Z/E)^2` would make every large `L ≡ r (mod E)` a counterexample.
The search was validated by recovering the Fermat covering at `L = 8, 16, 32`.

## Lean progress

- [ ] "if" half: for `L = 2^t ≥ 8`, every `2^L - 1 - 2^j - 2^k` with `j < k < L` is not prime.
- [ ] Small cases `m = 0, 1` and the failure at `m = 3`.

## Attempts

- m in 0..80 checked (Miller-Rabin): exactly 2^n - 1 except 3.
- "only if" half: for every length L = 3..399 that is not a power of 2, a probable prime of the
  form 2^L - 1 - 2^j - 2^k was found.
- Covering search over periods E = 2..90: no covering exists (so no counterexample of that kind
  with period ≤ 90).

## References

- OEIS A000225.
- Fermat numbers: `2^(2^t) - 1 = F_0 F_1 ⋯ F_(t-1)`.
