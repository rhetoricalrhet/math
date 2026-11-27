import Mathlib

/-!
# OEIS A000051: the matrix in Luschny's permanent formula

Work toward a Lean proof that the permanent of `luschnyMatrix n` is `2^n + 1`
(see `problems/oeis-a000051/`). This file holds only completed lemmas.

`luschnyMatrix` is the same definition as in the Left To Solve statement `oeis-a000051`.
-/

namespace Math.OEIS.A000051

/-- The `(n+1) × (n+1)` matrix with entries `M(j, k) = -⌊(j - k - 2) / (n + 1)⌋`. -/
def luschnyMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun j k => -⌊(((j : ℕ) : ℚ) - ((k : ℕ) : ℚ) - 2) / ((n : ℚ) + 1)⌋

/-- Step 1: every entry is `2` (top-right corner), `1` (on or above the subdiagonal) or `0`. -/
theorem luschny_entry (n : ℕ) (j k : Fin (n + 1)) :
    luschnyMatrix n j k =
      if (j : ℕ) = 0 ∧ (k : ℕ) = n then 2 else if (j : ℕ) ≤ (k : ℕ) + 1 then 1 else 0 := by
  have hj := j.isLt
  have hk := k.isLt
  have hn : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  unfold luschnyMatrix
  split_ifs with h1 h2
  · obtain ⟨h1, h1'⟩ := h1
    rw [h1, h1']
    have : ⌊(((0 : ℕ) : ℚ) - (n : ℚ) - 2) / ((n : ℚ) + 1)⌋ = -2 := by
      rw [Int.floor_eq_iff]
      constructor
      · rw [le_div_iff₀ hn]; push_cast; nlinarith
      · rw [div_lt_iff₀ hn]; push_cast; nlinarith
    simp only [Nat.cast_zero] at this ⊢
    rw [this]; norm_num
  · have : ⌊(((j : ℕ) : ℚ) - ((k : ℕ) : ℚ) - 2) / ((n : ℚ) + 1)⌋ = -1 := by
      rw [Int.floor_eq_iff]
      have hj' : ((j : ℕ) : ℚ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp hj
      have hk' : ((k : ℕ) : ℚ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp hk
      have h2' : ((j : ℕ) : ℚ) ≤ (k : ℕ) + 1 := by exact_mod_cast h2
      constructor
      · rw [le_div_iff₀ hn]; push_cast
        by_cases hj0 : (j : ℕ) = 0
        · have hkn : (k : ℕ) ≠ n := fun h => h1 ⟨hj0, h⟩
          have : (k : ℕ) < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
          have : ((k : ℕ) : ℚ) + 1 ≤ n := by exact_mod_cast this
          rw [hj0]; push_cast; linarith
        · have : (1 : ℚ) ≤ (j : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
          linarith
      · rw [div_lt_iff₀ hn]; push_cast; linarith
    rw [this]; norm_num
  · have : ⌊(((j : ℕ) : ℚ) - ((k : ℕ) : ℚ) - 2) / ((n : ℚ) + 1)⌋ = 0 := by
      rw [Int.floor_eq_iff]
      have hj' : ((j : ℕ) : ℚ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp hj
      have h2' : ((k : ℕ) : ℚ) + 2 ≤ (j : ℕ) := by exact_mod_cast (by omega : (k : ℕ) + 2 ≤ j)
      constructor
      · push_cast; apply div_nonneg <;> linarith
      · rw [div_lt_iff₀ hn]; push_cast; linarith
    rw [this]; norm_num

end Math.OEIS.A000051
