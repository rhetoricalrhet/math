# Notes

Status of this problem: the statement is a **known result** (OEIS says Sela Fried proved the
corrected Luschny conjecture). A Lean proof here is "known result formalized", not an open
problem solved.

## Informal proof

Let `N = n + 1`, rows and columns `j, k ∈ {0, ..., n}`, and `d = j - k ∈ [-n, n]`.

**Step 1: the entries.** `M(j, k) = -⌊(d - 2)/(n + 1)⌋` is

- `2` when `d = -n`, i.e. `j = 0` and `k = n` (the top-right corner): `(d - 2)/(n+1) = -1 - 1/(n+1)`,
  floor `-2`;
- `1` when `-n < d ≤ 1`, i.e. `j ≤ k + 1` otherwise: `(d - 2)/(n+1) ∈ [-1, 0)`, floor `-1`;
- `0` when `d ≥ 2`, i.e. `j ≥ k + 2`: `(d - 2)/(n+1) ∈ [0, 1)`, floor `0`.

So `M` is the all-ones upper Hessenberg matrix (ones on and above the subdiagonal) with the corner
entry `1` replaced by `2`.

**Step 2: split the permanent.** `perm M = Σ_σ Π_i M(σ i, i)`. A term is nonzero iff
`σ(i) ≤ i + 1` for all `i`, and it equals `2` when moreover `σ(n) = 0` (the corner is used),
`1` otherwise. Hence

    perm M = #{σ : σ(i) ≤ i+1 ∀i} + #{σ : σ(i) ≤ i+1 ∀i, σ(n) = 0}.

**Step 3a: the second set has exactly one element.** If `σ(n) = 0` then `σ(0) ≠ 0`, so
`σ(0) = 1`; then `σ(1) ∉ {0, 1}` forces `σ(1) = 2`; and so on: `σ(i) = i + 1` for `i < n`.

**Step 3b: the first set has `2^n` elements.** Such permutations are exactly products of
cycles `(a, a+1, ..., b)` on consecutive blocks partitioning `{0, ..., n}` (each block maps
`i ↦ i + 1` and its last element back to its first). A permutation is determined by where the
blocks break, i.e. by a subset of the `n` gaps between consecutive numbers: `2^n` choices.

So `perm M = 2^n + 1`. ∎

## Lean progress

In `lean/Math/OEIS/A000051.lean` (complete, no sorry): **`permanent_luschnyMatrix` is proved**
(axioms: propext, Classical.choice, Quot.sound).

- [x] Step 1, `luschny_entry`: each entry is `2`, `1` or `0` as above.
- [x] Step 2, `prod_luschny_entry`: work with the transpose (`Matrix.permanent_transpose`), so a
      term is `∏ i, M i (σ i)`; it equals `[Valid σ] + [Valid σ ∧ σ 0 = n]` where
      `Valid σ := ∀ j, j ≤ σ j + 1`.
- [x] Step 3a, `valid_corner_forced` + `sum_valid_corner`: the unique valid `σ` with `σ 0 = n`
      is `(finRotate (n+1)).symm` (downward strong induction on `j`).
- [x] Step 3b, `valid_decomposeFin_symm` + `sum_valid`: via `Equiv.Perm.decomposeFin`
      (`σ ↔ (σ 0, e)`), `σ` is valid iff `e` is valid and `σ 0 ∈ {0, (e 0).succ}`; so the count
      doubles at each step.

## Attempts

- Transposing first (condition `j ≤ σ j + 1` instead of `σ i ≤ i + 1`) makes the special point
  `0`, which matches Mathlib's `decomposeFin`; this worked on the first try, no failed routes.

## References

- OEIS A000051; Zhi-Wei Sun's related conjecture in A036968; Sela Fried's proof (linked from OEIS).
