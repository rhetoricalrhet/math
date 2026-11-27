import Mathlib

/-!
# OEIS A008676: number of ways to write `n` as `3a + 5b`

`a n` is the number of pairs `(x, y) ∈ ℕ²` with `3x + 5y = n`, i.e. the coefficient of `x^n` in
`1/((1-x^3)(1-x^5))` (see `coeff_inv`). This file proves the three claims recorded in
`problems/oeis-a008676/NOTES.md`:

1. Layman's floor formula `a n = ⌊2(n+3)/3⌋ - ⌊3(n+3)/5⌋` (`layman`), and Tani Akinari's
   `a n = ⌊(2n+5)/5⌋ - ⌊(n+2)/3⌋` (`akinari`). Proof: `a (n + 15) = a n + 1`
   (`a_add_fifteen`: split the solutions on whether `x ≥ 5`), both right sides also grow by `1`,
   and the base cases `n < 15` are checked by `decide` (`eq_a_of_add_fifteen`).
2. For `n ≥ 1`, `a n` is the number of multisets of `n - 1` elements of `{-2, 3, 4}` with sum `2`
   (`multisets` via the counts `(p, q, r)` of `-2`, `3`, `4`; `multisets_encard` for the set of
   multisets itself).
3. The number of triples `(x, y, z) ∈ ℕ³` with `x + y + z = n` and `2x = 3y + 4z` is `a n`
   (`triples_nonneg`); with positive parts it is `a (n - 8)` for `n ≥ 8` (`triples_pos`) and `0`
   for `n < 8` (`triples_pos_small`), so the positive-part reading of the comment fails as
   worded (`triples_pos_as_worded_fails`).

It also proves the generating function: `(∑ a(n) x^n) (1 - x^3) (1 - x^5) = 1` over any
commutative ring (`mk_a_mul`), and `a n` is the `n`-th coefficient of `((1 - X^3)(1 - X^5))⁻¹`
in `ℚ⟦X⟧` (`coeff_inv`).

Conventions: the floors in claim 1 are written with `ℕ` division, which is the floor for
these nonnegative quantities, and the difference is taken in `ℤ` (no truncated subtraction).
All counts are cardinalities of finsets cut out of `range` boxes; the boxes are large enough
that the bound is implied by the equations, so nothing is lost.
-/

open PowerSeries

namespace Math.OEIS.A008676

/-- Number of `(x, y) ∈ ℕ²` with `3x + 5y = n` (the coefficient of `x^n` in
`1/((1-x^3)(1-x^5))`, see `coeff_inv`). Both coordinates are at most `n`, so the box
`range (n + 1) ×ˢ range (n + 1)` contains every solution. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter (fun p => 3 * p.1 + 5 * p.2 = n)).card

/-- Membership in the solution set of `3x + 5y = n`: the box bound is automatic. -/
theorem mem_sol {n : ℕ} {p : ℕ × ℕ} :
    p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => 3 * p.1 + 5 * p.2 = n) ↔ 3 * p.1 + 5 * p.2 = n := by
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-! ## Claim 1: the floor formulas -/

/-- `a (n + 15) = a n + 1`. Solutions of `3x + 5y = n + 15` with `x ≥ 5` correspond to solutions
of `3x + 5y = n` via `x ↦ x - 5`; exactly one solution has `x ≤ 4`, namely `x = 2n mod 5`. -/
theorem a_add_fifteen (n : ℕ) : a (n + 15) = a n + 1 := by
  unfold a
  rw [← Finset.card_filter_add_card_filter_not (fun p : ℕ × ℕ => 5 ≤ p.1),
    Finset.filter_filter, Finset.filter_filter]
  congr 1
  · apply Finset.card_nbij' (fun p => (p.1 - 5, p.2)) (fun p => (p.1 + 5, p.2))
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
        Set.mem_ofPred_eq] at hp ⊢
      omega
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
        Set.mem_ofPred_eq] at hp ⊢
      omega
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
        Set.mem_ofPred_eq] at hp ⊢
      ext
      · simp only; omega
      · rfl
    · intro p _
      simp
  · rw [Finset.card_eq_one]
    refine ⟨((2 * n) % 5, (n + 15 - 3 * ((2 * n) % 5)) / 5), ?_⟩
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_singleton,
      Prod.mk.injEq]
    omega

/-- Any `f : ℕ → ℤ` with `f (n + 15) = f n + 1` that agrees with `a` below `15` equals `a`. -/
theorem eq_a_of_add_fifteen (f : ℕ → ℤ) (hf : ∀ n, f (n + 15) = f n + 1)
    (h0 : ∀ n < 15, (a n : ℤ) = f n) (n : ℕ) : (a n : ℤ) = f n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 15 with hn | hn
    · exact h0 n hn
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 15 := ⟨n - 15, by omega⟩
      rw [a_add_fifteen, hf, Nat.cast_add, ih m (by omega), Nat.cast_one]

/-- Layman's conjectured formula: `a n = ⌊2(n+3)/3⌋ - ⌊3(n+3)/5⌋` for every `n`
(`ℕ` division is the floor here; the subtraction is in `ℤ`). -/
theorem layman (n : ℕ) : (a n : ℤ) = (2 * (n + 3) / 3 : ℕ) - (3 * (n + 3) / 5 : ℕ) := by
  refine eq_a_of_add_fifteen (fun n => ((2 * (n + 3) / 3 : ℕ) : ℤ) - (3 * (n + 3) / 5 : ℕ))
    (fun n => ?_) (by decide) n
  have h1 : 2 * (n + 15 + 3) / 3 = 2 * (n + 3) / 3 + 10 := by omega
  have h2 : 3 * (n + 15 + 3) / 5 = 3 * (n + 3) / 5 + 9 := by omega
  simp only [h1, h2]
  push_cast
  ring

/-- Tani Akinari's formula: `a n = ⌊(2n+5)/5⌋ - ⌊(n+2)/3⌋` for every `n`
(`ℕ` division is the floor here; the subtraction is in `ℤ`). -/
theorem akinari (n : ℕ) : (a n : ℤ) = ((2 * n + 5) / 5 : ℕ) - ((n + 2) / 3 : ℕ) := by
  refine eq_a_of_add_fifteen (fun n => (((2 * n + 5) / 5 : ℕ) : ℤ) - ((n + 2) / 3 : ℕ))
    (fun n => ?_) (by decide) n
  have h1 : (2 * (n + 15) + 5) / 5 = (2 * n + 5) / 5 + 6 := by omega
  have h2 : (n + 15 + 2) / 3 = (n + 2) / 3 + 5 := by omega
  simp only [h1, h2]
  push_cast
  ring

/-! ## Claim 2: multisets of `n - 1` elements of `{-2, 3, 4}` with sum `2` -/

/-- Number of count vectors `(p, q, r) ∈ ℕ³` (multiplicities of `-2`, `3`, `4`) with
`p + q + r = n - 1` and `-2p + 3q + 4r = 2`, written as `3q + 4r = 2p + 2` to stay in `ℕ`.
A multiset of elements of `{-2, 3, 4}` is determined by these counts (see `ofCounts_counts`
and `multisets_encard`). For `n ≥ 1` each count is at most `n - 1`, so the box `range n`
contains every solution. (For `n = 0` there are no multisets of `-1` elements: the claim is
for `n ≥ 1`, and indeed `multisetCount 0 = 0 ≠ 1 = a 0`.) -/
def multisetCount (n : ℕ) : ℕ :=
  ((Finset.range n ×ˢ Finset.range n ×ˢ Finset.range n).filter
    (fun t => t.1 + t.2.1 + t.2.2 = n - 1 ∧ 3 * t.2.1 + 4 * t.2.2 = 2 * t.1 + 2)).card

/-- Claim 2 via counts: for `n ≥ 1`, `multisetCount n = a n`. The bijection is
`(p, q, r) ↦ (r, q / 2)` with inverse `(x, y) ↦ (n - 1 - 2y - x, 2y, x)`. -/
theorem multisets (n : ℕ) (hn : 1 ≤ n) : multisetCount n = a n := by
  unfold multisetCount a
  apply Finset.card_nbij' (fun t => (t.2.2, t.2.1 / 2))
    (fun p => (n - 1 - 2 * p.2 - p.1, 2 * p.2, p.1))
  · rintro ⟨p, q, r⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_ofPred_eq] at h ⊢
    omega
  · rintro ⟨x, y⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_ofPred_eq] at h ⊢
    omega
  · rintro ⟨p, q, r⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_ofPred_eq] at h
    simp only [Prod.mk.injEq, and_true]
    omega
  · rintro ⟨x, y⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_ofPred_eq] at h
    simp only [Prod.mk.injEq, true_and]
    omega

/-- The multiset with `t.1` copies of `-2`, `t.2.1` copies of `3` and `t.2.2` copies of `4`. -/
def ofCounts (t : ℕ × ℕ × ℕ) : Multiset ℤ :=
  Multiset.replicate t.1 (-2) + Multiset.replicate t.2.1 3 + Multiset.replicate t.2.2 4

/-- The counts of `-2`, `3`, `4` in `ofCounts t` are `t`. -/
theorem count_ofCounts (t : ℕ × ℕ × ℕ) :
    (ofCounts t).count (-2) = t.1 ∧ (ofCounts t).count 3 = t.2.1 ∧
      (ofCounts t).count 4 = t.2.2 := by
  simp [ofCounts, Multiset.count_replicate]

/-- Different count vectors give different multisets. -/
theorem ofCounts_injective : Function.Injective ofCounts := by
  intro t t' h
  obtain ⟨h1, h2, h3⟩ := count_ofCounts t
  obtain ⟨h1', h2', h3'⟩ := count_ofCounts t'
  rw [h] at h1 h2 h3
  ext <;> omega

/-- A multiset with all elements in `{-2, 3, 4}` is determined by its counts. -/
theorem ofCounts_counts {m : Multiset ℤ} (hm : ∀ x ∈ m, x = -2 ∨ x = 3 ∨ x = 4) :
    ofCounts (m.count (-2), m.count 3, m.count 4) = m := by
  ext b
  simp only [ofCounts, Multiset.count_add, Multiset.count_replicate]
  by_cases h1 : b = -2
  · subst h1; simp
  by_cases h2 : b = 3
  · subst h2; simp
  by_cases h3 : b = 4
  · subst h3; simp
  have : b ∉ m := fun hb => by rcases hm b hb with h | h | h <;> contradiction
  simp [Ne.symm h1, Ne.symm h2, Ne.symm h3, Multiset.count_eq_zero.mpr this]

/-- `ofCounts (p, q, r)` has `p + q + r` elements. -/
theorem card_ofCounts (t : ℕ × ℕ × ℕ) :
    Multiset.card (ofCounts t) = t.1 + t.2.1 + t.2.2 := by
  simp [ofCounts]

/-- `ofCounts (p, q, r)` has sum `-2p + 3q + 4r`. -/
theorem sum_ofCounts (t : ℕ × ℕ × ℕ) :
    (ofCounts t).sum = -2 * (t.1 : ℤ) + 3 * t.2.1 + 4 * t.2.2 := by
  simp [ofCounts, Multiset.sum_replicate]
  ring

/-- Every element of `ofCounts t` lies in `{-2, 3, 4}`. -/
theorem mem_ofCounts {t : ℕ × ℕ × ℕ} {x : ℤ} (hx : x ∈ ofCounts t) :
    x = -2 ∨ x = 3 ∨ x = 4 := by
  simp only [ofCounts, Multiset.mem_add, Multiset.mem_replicate] at hx
  omega

/-- Claim 2 as stated: for `n ≥ 1`, the set of multisets of `n - 1` integers from `{-2, 3, 4}`
with sum `2` has exactly `a n` elements (`encard` is `⊤` on infinite sets, so this also says
the set is finite). -/
theorem multisets_encard (n : ℕ) (hn : 1 ≤ n) :
    {m : Multiset ℤ | Multiset.card m = n - 1 ∧ (∀ x ∈ m, x = -2 ∨ x = 3 ∨ x = 4) ∧
      m.sum = 2}.encard = a n := by
  have hset : {m : Multiset ℤ | Multiset.card m = n - 1 ∧
      (∀ x ∈ m, x = -2 ∨ x = 3 ∨ x = 4) ∧ m.sum = 2} =
      ↑(((Finset.range n ×ˢ Finset.range n ×ˢ Finset.range n).filter
        (fun t => t.1 + t.2.1 + t.2.2 = n - 1 ∧ 3 * t.2.1 + 4 * t.2.2 = 2 * t.1 + 2)).image
          ofCounts) := by
    ext m
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_filter, Set.mem_image,
      Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨hc, hm, hs⟩
      refine ⟨(m.count (-2), m.count 3, m.count 4), ?_, ofCounts_counts hm⟩
      have hc' := card_ofCounts (m.count (-2), m.count 3, m.count 4)
      have hs' := sum_ofCounts (m.count (-2), m.count 3, m.count 4)
      rw [ofCounts_counts hm] at hc' hs'
      simp only at hc' hs' ⊢
      omega
    · rintro ⟨t, ht, rfl⟩
      refine ⟨?_, fun x hx => mem_ofCounts hx, ?_⟩
      · rw [card_ofCounts]; omega
      · rw [sum_ofCounts]; omega
  rw [hset, Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ ofCounts_injective]
  exact_mod_cast multisets n hn

/-! ## Claim 3: triples with `x + y + z = n` and `2x = 3y + 4z` -/

/-- Number of `(x, y, z) ∈ ℕ³` with `x, y, z ≥ 1`, `x + y + z = n` and `2x = 3y + 4z`. -/
def triplesPos (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun t => 1 ≤ t.1 ∧ 1 ≤ t.2.1 ∧ 1 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n ∧
      2 * t.1 = 3 * t.2.1 + 4 * t.2.2)).card

/-- Number of `(x, y, z) ∈ ℕ³` with `x + y + z = n` and `2x = 3y + 4z`. -/
def triplesNonneg (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun t => t.1 + t.2.1 + t.2.2 = n ∧ 2 * t.1 = 3 * t.2.1 + 4 * t.2.2)).card

/-- Claim 3, nonnegative parts: `triplesNonneg n = a n`, via `(x, y, z) ↦ (z, y / 2)`. -/
theorem triples_nonneg (n : ℕ) : triplesNonneg n = a n := by
  unfold triplesNonneg a
  apply Finset.card_nbij' (fun t => (t.2.2, t.2.1 / 2))
    (fun p => (n - 2 * p.2 - p.1, 2 * p.2, p.1))
  · rintro ⟨x, y, z⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_ofPred_eq] at h ⊢
    omega
  · rintro ⟨x, y⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_ofPred_eq] at h ⊢
    omega
  · rintro ⟨x, y, z⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_ofPred_eq] at h
    simp only [Prod.mk.injEq, and_true]
    omega
  · rintro ⟨x, y⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_ofPred_eq] at h
    simp only [Prod.mk.injEq, true_and]
    omega

/-- Claim 3, positive parts: for `n ≥ 8`, `triplesPos n = a (n - 8)`, via
`(x, y, z) ↦ (z - 1, y / 2 - 1)`. -/
theorem triples_pos (n : ℕ) (hn : 8 ≤ n) : triplesPos n = a (n - 8) := by
  unfold triplesPos a
  apply Finset.card_nbij' (fun t => (t.2.2 - 1, t.2.1 / 2 - 1))
    (fun p => (n - 2 * (p.2 + 1) - (p.1 + 1), 2 * (p.2 + 1), p.1 + 1))
  · rintro ⟨x, y, z⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_ofPred_eq] at h ⊢
    omega
  · rintro ⟨x, y⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_ofPred_eq] at h ⊢
    omega
  · rintro ⟨x, y, z⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_ofPred_eq] at h
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨x, y⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_ofPred_eq] at h
    simp only [Prod.mk.injEq]
    omega

/-- Claim 3, positive parts, small `n`: there are no such triples for `n < 8`. -/
theorem triples_pos_small (n : ℕ) (hn : n < 8) : triplesPos n = 0 := by
  unfold triplesPos
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y, z⟩ - h
  simp only at h
  omega

/-- The positive-part reading of the comment fails as worded, even for `n ≥ 1`:
`triplesPos 3 = 0` but `a 3 = 1` (the only solution being `3 = 3 * 1 + 5 * 0`). -/
theorem triples_pos_as_worded_fails : ¬ ∀ n, 1 ≤ n → triplesPos n = a n := by
  intro h
  have h3 := h 3 (by norm_num)
  rw [triples_pos_small 3 (by norm_num)] at h3
  have : a 3 = 1 := by decide
  omega

/-! ## The generating function -/

/-- `∑_{k ∣ i} x^i` times `1 - x^k` is `1`, for `k = 3` and `k = 5`. -/
theorem geom_mul (R : Type*) [CommRing R] (k : ℕ) (hk : k = 3 ∨ k = 5) :
    (PowerSeries.mk fun i => if k ∣ i then (1 : R) else 0) * (1 - X ^ k) = 1 := by
  ext i
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_one]
  simp only [coeff_mk]
  rcases hk with rfl | rfl <;> split_ifs <;> first | (exfalso; omega) | simp

/-- `a n` counts the pairs `(i, j)` with `i + j = n`, `3 ∣ i` and `5 ∣ j`. -/
theorem a_eq_card_antidiagonal (n : ℕ) :
    a n = ((Finset.HasAntidiagonal.antidiagonal n).filter
      (fun p => 3 ∣ p.1 ∧ 5 ∣ p.2)).card := by
  unfold a
  apply Finset.card_nbij' (fun p => (3 * p.1, 5 * p.2)) (fun p => (p.1 / 3, p.2 / 5))
  · rintro ⟨x, y⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Finset.HasAntidiagonal.mem_antidiagonal, Set.mem_ofPred_eq] at h ⊢
    omega
  · rintro ⟨i, j⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Finset.HasAntidiagonal.mem_antidiagonal, Set.mem_ofPred_eq] at h ⊢
    omega
  · rintro ⟨x, y⟩ h
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨i, j⟩ h
    simp only [Finset.coe_filter, Finset.HasAntidiagonal.mem_antidiagonal,
      Set.mem_ofPred_eq] at h
    simp only [Prod.mk.injEq]
    omega

/-- The generating function of `a` over any commutative ring:
`(∑ a(n) x^n) (1 - x^3) (1 - x^5) = 1`. -/
theorem mk_a_mul (R : Type*) [CommRing R] :
    (PowerSeries.mk fun n => (a n : R)) * ((1 - X ^ 3) * (1 - X ^ 5)) = 1 := by
  have h : (PowerSeries.mk fun n => (a n : R)) =
      (PowerSeries.mk fun i => if 3 ∣ i then (1 : R) else 0) *
        (PowerSeries.mk fun i => if 5 ∣ i then (1 : R) else 0) := by
    ext n
    rw [coeff_mk, coeff_mul]
    simp only [coeff_mk, ite_zero_mul_ite_zero, mul_one]
    rw [Finset.sum_boole, a_eq_card_antidiagonal]
  rw [h]
  calc _ = ((PowerSeries.mk fun i => if 3 ∣ i then (1 : R) else 0) * (1 - X ^ 3)) *
        ((PowerSeries.mk fun i => if 5 ∣ i then (1 : R) else 0) * (1 - X ^ 5)) := by ring
    _ = 1 := by rw [geom_mul R 3 (Or.inl rfl), geom_mul R 5 (Or.inr rfl), one_mul]

/-- `a n` is the coefficient of `x^n` in `1/((1-x^3)(1-x^5))` (over `ℚ`). -/
theorem coeff_inv (n : ℕ) :
    coeff n (((1 - X ^ 3) * (1 - X ^ 5) : ℚ⟦X⟧)⁻¹) = a n := by
  have h0 : constantCoeff ((1 - X ^ 3) * (1 - X ^ 5) : ℚ⟦X⟧) ≠ 0 := by simp
  rw [(PowerSeries.inv_eq_iff_mul_eq_one h0).mpr (mk_a_mul ℚ), coeff_mk]

end Math.OEIS.A008676
