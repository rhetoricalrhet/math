import Mathlib

/-!
# OEIS A000051: the matrix in Luschny's permanent formula

Work toward a Lean proof that the permanent of `luschnyMatrix n` is `2^n + 1`
(see `problems/oeis-a000051/`). The proof is complete: see `permanent_luschnyMatrix`.

`luschnyMatrix` is the same definition as in the Left To Solve statement `oeis-a000051`.
-/

open Equiv

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

/-- `σ` only hits entries on or above the subdiagonal of `(luschnyMatrix n)ᵀ`:
`j ≤ σ j + 1` for every `j` (the transposed form of `σ i ≤ i + 1`). -/
def Valid {m : ℕ} (σ : Perm (Fin (m + 1))) : Prop := ∀ j : Fin (m + 1), (j : ℕ) ≤ (σ j : ℕ) + 1

instance {m : ℕ} : DecidablePred (@Valid m) := fun σ => by unfold Valid; infer_instance

/-- Step 3b, induction step: under `Equiv.Perm.decomposeFin`, `σ = (p, e)` is valid iff `e` is
valid and `p` is `0` (point `0` fixed) or `(e 0).succ` (point `0` glued to the next block). -/
theorem valid_decomposeFin_symm {m : ℕ} (p : Fin (m + 2)) (e : Perm (Fin (m + 1))) :
    Valid (Perm.decomposeFin.symm (p, e)) ↔ Valid e ∧ (p = 0 ∨ p = (e 0).succ) := by
  constructor
  · intro h
    have hp : p = 0 ∨ p = (e 0).succ := by
      by_cases hp0 : p = 0
      · exact Or.inl hp0
      right
      set σ := Perm.decomposeFin.symm (p, e) with hσ
      obtain ⟨j, hj⟩ : ∃ j, σ j = 0 := ⟨σ.symm 0, by simp⟩
      have hj1 : (j : ℕ) ≤ 1 := by have := h j; rw [hj] at this; simpa using this
      have hj0 : j ≠ 0 := by
        rintro rfl; rw [hσ, Perm.decomposeFin_symm_apply_zero] at hj; exact hp0 hj
      have hj1' : j = 1 := by
        apply Fin.ext; have : (j : ℕ) ≠ 0 := fun h' => hj0 (Fin.ext h'); simp; omega
      subst hj1'
      rw [hσ, Perm.decomposeFin_symm_apply_one, swap_apply_eq_iff, swap_apply_left] at hj
      exact hj.symm
    refine ⟨fun x => ?_, hp⟩
    have hx := h x.succ
    rw [Perm.decomposeFin_symm_apply_succ] at hx
    simp only [Fin.val_succ] at hx
    rcases hp with rfl | rfl
    · simp at hx; omega
    · by_cases hx0 : x = 0
      · subst hx0; simp
      · have hne : (e x).succ ≠ (e 0).succ := by
          intro h'; exact hx0 (e.injective (Fin.succ_injective _ h'))
        rw [swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) hne] at hx
        simp at hx; omega
  · rintro ⟨he, hp⟩ j
    refine Fin.cases (by simp) (fun x => ?_) j
    rw [Perm.decomposeFin_symm_apply_succ]
    simp only [Fin.val_succ]
    rcases hp with rfl | rfl
    · simp; have := he x; omega
    · by_cases hx0 : x = 0
      · subst hx0; simp
      · have hne : (e x).succ ≠ (e 0).succ := by
          intro h'; exact hx0 (e.injective (Fin.succ_injective _ h'))
        rw [swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) hne]
        simp; have := he x; omega

/-- Step 3b: there are `2 ^ m` valid permutations of `Fin (m + 1)`. -/
theorem sum_valid (m : ℕ) :
    ∑ σ : Perm (Fin (m + 1)), (if Valid σ then (1 : ℤ) else 0) = 2 ^ m := by
  induction m with
  | zero =>
    show ∑ σ : Perm (Fin 1), _ = _
    rw [Fintype.sum_subsingleton _ 1, if_pos]; · simp
    intro j; simp
  | succ m ih =>
    rw [← Equiv.sum_comp Perm.decomposeFin.symm, Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [valid_decomposeFin_symm]
    have : ∀ e : Perm (Fin (m + 1)),
        ∑ p : Fin (m + 2), (if Valid e ∧ (p = 0 ∨ p = (e 0).succ) then (1 : ℤ) else 0)
          = 2 * (if Valid e then 1 else 0) := by
      intro e
      by_cases he : Valid e
      · simp only [he, true_and, if_true, mul_one]
        rw [Finset.sum_boole]
        have : (Finset.univ.filter fun p : Fin (m + 2) => p = 0 ∨ p = (e 0).succ)
            = {0, (e 0).succ} := by ext p; simp
        rw [this, Finset.card_pair (Fin.succ_ne_zero _).symm]; norm_num
      · simp [he]
    simp_rw [this, ← Finset.mul_sum, ih, pow_succ]; ring

/-- Step 3a: a valid permutation with `σ 0 = n` is forced to be `j ↦ j - 1` on `j ≠ 0`
(downward induction on `j`). -/
theorem valid_corner_forced {n : ℕ} (σ : Perm (Fin (n + 1))) (hv : Valid σ)
    (h0 : (σ 0 : ℕ) = n) (j : Fin (n + 1)) (hj : j ≠ 0) : (σ j : ℕ) + 1 = j := by
  suffices H : ∀ k, ∀ j : Fin (n + 1), (j : ℕ) + k = n → j ≠ 0 → (σ j : ℕ) + 1 = j by
    exact H (n - j) j (by have := j.isLt; omega) hj
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j hjk hj0
    have hvj := hv j
    by_contra hne
    have hge : (j : ℕ) ≤ σ j := by omega
    have hjn : (σ j : ℕ) ≠ n := by
      intro h; apply hj0; apply σ.injective; apply Fin.ext; rw [h, h0]
    have hlt : (σ j : ℕ) + 1 < n + 1 := by have := (σ j).isLt; omega
    have := ih (n - ((σ j : ℕ) + 1)) (by omega) ⟨(σ j : ℕ) + 1, hlt⟩ (by simp; omega)
      (by intro h; simpa using congrArg Fin.val h)
    simp only at this
    have heq : σ ⟨(σ j : ℕ) + 1, hlt⟩ = σ j := Fin.ext (by omega)
    have := congrArg Fin.val (σ.injective heq)
    simp at this; omega

/-- Step 3a: exactly one valid permutation uses the corner, namely `(finRotate (n + 1)).symm`. -/
theorem sum_valid_corner (n : ℕ) :
    ∑ σ : Perm (Fin (n + 1)), (if Valid σ ∧ (σ 0 : ℕ) = n then (1 : ℤ) else 0) = 1 := by
  have hc0 : (finRotate (n + 1)).symm 0 = Fin.last n := by
    rw [Equiv.symm_apply_eq, finRotate_last]
  have hcv : Valid (finRotate (n + 1)).symm := by
    intro j
    obtain ⟨k, rfl⟩ := (finRotate (n + 1)).surjective j
    rw [Equiv.symm_apply_apply, coe_finRotate]
    split_ifs <;> omega
  rw [Fintype.sum_eq_single (finRotate (n + 1)).symm]
  · rw [if_pos ⟨hcv, by rw [hc0]; simp⟩]
  · intro σ hσ
    rw [if_neg]
    rintro ⟨hv, h0⟩
    apply hσ
    refine Equiv.ext fun j => ?_
    rw [Equiv.eq_symm_apply]
    apply Fin.ext
    rw [coe_finRotate]
    by_cases hj : j = 0
    · subst hj
      rw [if_pos (Fin.ext (by simp [h0]))]; rfl
    · have := valid_corner_forced σ hv h0 j hj
      rw [if_neg]
      · exact this
      · intro h; have := congrArg Fin.val h; simp at this; have := j.isLt; omega


/-- Step 2: the term of a permutation in the (transposed) permanent sum. -/
theorem prod_luschny_entry (n : ℕ) (σ : Perm (Fin (n + 1))) :
    ∏ i, luschnyMatrix n i (σ i) =
      (if Valid σ then 1 else 0) + (if Valid σ ∧ (σ 0 : ℕ) = n then 1 else 0) := by
  by_cases hv : Valid σ
  · rw [Fin.prod_univ_succ]
    have hrest : ∀ x : Fin n, luschnyMatrix n x.succ (σ x.succ) = 1 := by
      intro x
      rw [luschny_entry, if_neg (by simp), if_pos (hv x.succ)]
    simp only [hrest, Finset.prod_const_one, mul_one, luschny_entry, hv, true_and, if_true]
    by_cases h0 : (σ 0 : ℕ) = n
    · simp [h0]
    · simp [h0]
  · rw [if_neg hv, if_neg (fun h => hv h.1)]
    obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), ¬ ((j : ℕ) ≤ (σ j : ℕ) + 1) := by
      unfold Valid at hv; simpa using hv
    rw [add_zero]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [luschny_entry, if_neg, if_neg hj]
    rintro ⟨h, -⟩; omega

/-- OEIS A000051: the permanent of `luschnyMatrix n` is `2 ^ n + 1`. -/
theorem permanent_luschnyMatrix (n : ℕ) : (luschnyMatrix n).permanent = 2 ^ n + 1 := by
  rw [← Matrix.permanent_transpose, Matrix.permanent]
  simp only [Matrix.transpose_apply, prod_luschny_entry, Finset.sum_add_distrib, sum_valid,
    sum_valid_corner]

end Math.OEIS.A000051
