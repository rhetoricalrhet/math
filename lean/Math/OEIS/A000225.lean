import Mathlib

/-!
# OEIS A000225: the if half of Chai Wah Wu's conjecture

Conjecture (see `problems/oeis-a000225/`): `AllComposite m` holds if and only if
`m = 2^n - 1` for some `n` and `m ≠ 3`. This file proves the reverse direction, see
`allComposite_of_pow` and `allComposite_of_exists`, and records the failure at `m = 3`
(`not_allComposite_three`). The forward direction is open.

Proof for `L = 2^n ≥ 8` and `j < k < L`: write `k - j = 2^i * u` with `u` odd, so `i < n`.
The Fermat number `F = 2^(2^i) + 1` satisfies `2^(2^i) = -1` in `ZMod F`, hence
`2^k = -2^j` and `2^L = 1` there, so `F` divides `v = 2^L - 2^j - 2^k - 1`. Size bounds
give `1 < F < v`.

`AllComposite` is the same definition as in the Left To Solve statement `oeis-a000225`.
-/

namespace Math.OEIS.A000225

/-- The property of the conjecture: `2^(m+1) - 2^j - 2^k - 1` is not prime for all
`0 ≤ j < k ≤ m`. -/
def AllComposite (m : ℕ) : Prop :=
  ∀ j k : ℕ, j < k → k ≤ m → ¬ (2 ^ (m + 1) - 2 ^ j - 2 ^ k - 1).Prime

/-- Modulo the Fermat number `2^(2^i) + 1`, we have `2^(2^i) = -1`. -/
lemma two_pow_two_pow_eq_neg_one (i : ℕ) :
    (2 : ZMod (2 ^ (2 ^ i) + 1)) ^ (2 ^ i) = -1 := by
  have h : ((2 ^ (2 ^ i) + 1 : ℕ) : ZMod (2 ^ (2 ^ i) + 1)) = 0 := ZMod.natCast_self _
  push_cast at h
  exact eq_neg_of_add_eq_zero_left h

/-- The Fermat number `2^(2^i) + 1` divides `v = 2^(2^n) - 2^j - 2^(j + 2^i u) - 1` when
`i < n` and `u` is odd (stated without truncated subtraction). -/
lemma fermat_dvd (n i j u v : ℕ) (hi : i < n) (hu : Odd u)
    (hv : v + 2 ^ j + 2 ^ (j + 2 ^ i * u) + 1 = 2 ^ (2 ^ n)) :
    2 ^ (2 ^ i) + 1 ∣ v := by
  rw [← ZMod.natCast_eq_zero_iff]
  have h1 := two_pow_two_pow_eq_neg_one i
  have h2 : (2 : ZMod (2 ^ (2 ^ i) + 1)) ^ (2 ^ n) = 1 := by
    obtain ⟨e, rfl⟩ : ∃ e, n = i + 1 + e := ⟨n - (i + 1), by omega⟩
    rw [pow_add, pow_succ, pow_mul, pow_mul, h1]
    simp
  have h3 : (2 : ZMod (2 ^ (2 ^ i) + 1)) ^ (j + 2 ^ i * u) = -2 ^ j := by
    rw [pow_add, pow_mul, h1, hu.neg_one_pow]
    ring
  have := congrArg (Nat.cast : ℕ → ZMod (2 ^ (2 ^ i) + 1)) hv
  push_cast at this
  rw [h3, h2] at this
  linear_combination this

/-- The main case: for `L = 2^n` with `n ≥ 3` and `j < k < L`, the number
`2^L - 2^j - 2^k - 1` is not prime. -/
theorem not_prime_of_lt (n : ℕ) (hn : 3 ≤ n) (j k : ℕ) (hjk : j < k) (hk : k < 2 ^ n) :
    ¬ (2 ^ (2 ^ n) - 2 ^ j - 2 ^ k - 1).Prime := by
  obtain ⟨i, u, hu, hd⟩ := Nat.exists_eq_two_pow_mul_odd (n := k - j) (by omega)
  have hk' : k = j + 2 ^ i * u := by omega
  have hu1 : 1 ≤ u := hu.pos
  have hiu : 2 ^ i ≤ 2 ^ i * u := Nat.le_mul_of_pos_right _ hu1
  have hi : i < n := by
    have h2 : 2 ^ i < 2 ^ n := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
  -- Size bounds, with `2^n = M + 3`.
  have hn1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hn4 : 4 ≤ 2 ^ (n - 1) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ n - 1))
  have hin : 2 ^ i ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ n = M + 3 := ⟨2 ^ n - 3, by omega⟩
  have hP : 2 ^ (2 ^ n) = 8 * 2 ^ M := by rw [hM, pow_add]; ring
  have hj2 : 2 ^ j ≤ 2 * 2 ^ M := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hk2 : 2 ^ k ≤ 4 * 2 ^ M := by
    have : 2 ^ k ≤ 2 ^ (M + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_add] at this; omega
  have hF : 2 ^ (2 ^ i) ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hM5 : 32 ≤ 2 ^ M :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 5 ≤ M))
  -- The Fermat number `2^(2^i) + 1` is a proper divisor.
  set v := 2 ^ (2 ^ n) - 2 ^ j - 2 ^ k - 1 with hvdef
  have hv : v + 2 ^ j + 2 ^ (j + 2 ^ i * u) + 1 = 2 ^ (2 ^ n) := by
    rw [← hk']; omega
  have hdvd := fermat_dvd n i j u v hi hu hv
  intro hp
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
  · have : 1 ≤ 2 ^ (2 ^ i) := Nat.one_le_two_pow
    omega
  · omega

/-- The if half of the conjecture: `AllComposite (2^n - 1)` unless `2^n - 1 = 3`.
The cases `n = 0` (no pairs) and `n = 1` (the only value is `0`) are direct. -/
theorem allComposite_of_pow (n : ℕ) (h : 2 ^ n - 1 ≠ 3) : AllComposite (2 ^ n - 1) := by
  intro j k hjk hk
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | rfl | hn
  · simp at hk; omega
  · have hk1 : k = 1 := by simp at hk; omega
    have hj0 : j = 0 := by omega
    subst hk1 hj0
    norm_num
  · simp at h
  · have h1 : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel Nat.one_le_two_pow
    rw [h1]
    exact not_prime_of_lt n hn j k hjk (by omega)

/-- The reverse direction of the conjecture, in the form of the Left To Solve statement. -/
theorem allComposite_of_exists (m : ℕ) (h : (∃ n : ℕ, m = 2 ^ n - 1) ∧ m ≠ 3) :
    AllComposite m := by
  obtain ⟨⟨n, rfl⟩, h3⟩ := h
  exact allComposite_of_pow n h3

/-- The exception `m = 3`: `j = 1`, `k = 3` gives `16 - 2 - 8 - 1 = 5`, a prime. -/
theorem not_allComposite_three : ¬ AllComposite 3 := by
  intro h
  exact h 1 3 (by norm_num) le_rfl (by norm_num)

end Math.OEIS.A000225
