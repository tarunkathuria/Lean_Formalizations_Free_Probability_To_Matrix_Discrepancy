import MatrixSpencer.KSDebitCenter
import MatrixSpencer.KSStateRetirement

/-!
# The actual debit determined by retired original labels

The full-cube walk starts with no retired labels and adds `δ Aᵢ + η I`
when label `i` retires. Since each label retires only once, the debit is
an explicit function of the frozen set. This module proves the update and
the Parseval budget; it does not assume that a movement is already legal.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSDebitBudget

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

def debit (A : Fin N → Matrix n n ℂ) (δ η : ℝ) (x : Fin N → ℝ) : Matrix n n ℂ :=
  δ • (∑ i ∈ ksFrozen 1 x, A i) + (((ksFrozen 1 x).card : ℝ) * η) • (1 : Matrix n n ℂ)

theorem frozen_update_endpoint {x : Fin N → ℝ} (i : Fin N)
    (hi : |x i| < 1) {s : ℝ} (hs : IsSign s) :
    ksFrozen 1 (Function.update x i s) = insert i (ksFrozen 1 x) := by
  classical
  have habs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  ext j
  by_cases hj : j = i
  · subst j
    simp [ksFrozen, habs]
  · simp [ksFrozen, Function.update_of_ne hj, hj]

theorem not_frozen_of_live {x : Fin N → ℝ} (i : Fin N) (hi : |x i| < 1) :
    i ∉ ksFrozen 1 x := by
  simp only [ksFrozen, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ne_of_lt hi


theorem debit_update_endpoint (A : Fin N → Matrix n n ℂ) (δ η : ℝ)
    {x : Fin N → ℝ} (i : Fin N) (hi : |x i| < 1) {s : ℝ} (hs : IsSign s) :
    debit A δ η (Function.update x i s) = debit A δ η x + δ • A i + η • (1 : Matrix n n ℂ) := by
  have hn := not_frozen_of_live i hi
  simp only [debit, frozen_update_endpoint i hi hs, Finset.sum_insert hn,
    Finset.card_insert_of_notMem hn, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
    smul_add, add_smul]
  abel

theorem debit_zero (A : Fin N → Matrix n n ℂ) (δ η : ℝ) : debit A δ η 0 = 0 := by
  have he : ksFrozen 1 (0 : Fin N → ℝ) = ∅ := by
    ext i
    simp [ksFrozen]
  simp [debit, he]

theorem sum_frozen_posSemidef (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x : Fin N → ℝ) :
    (∑ i ∈ ksFrozen 1 x, A i).PosSemidef := by
  exact (Finset.sum_nonneg (fun i _ => (hA i).nonneg)).posSemidef

theorem debit_posSemidef (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (x : Fin N → ℝ) : (debit A δ η x).PosSemidef := by
  exact ((sum_frozen_posSemidef A hA x).smul hδ).add
    (Matrix.PosSemidef.one.smul (mul_nonneg (Nat.cast_nonneg _) hη))

theorem sum_frozen_le_one (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hparseval : (∑ i, A i) = 1) (x : Fin N → ℝ) :
    (∑ i ∈ ksFrozen 1 x, A i) ≤ 1 := by
  rw [← hparseval]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => (hA i).nonneg)

theorem smul_le_smul_nonneg {A B : Matrix n n ℂ} (hAB : A ≤ B)
    {t : ℝ} (ht : 0 ≤ t) : t • A ≤ t • B := by
  apply Matrix.le_iff.mpr
  rw [← smul_sub]
  exact (Matrix.le_iff.mp hAB).smul ht

theorem scalar_one_mono {s t : ℝ} (hst : s ≤ t) :
    s • (1 : Matrix n n ℂ) ≤ t • (1 : Matrix n n ℂ) := by
  apply Matrix.le_iff.mpr
  rw [← sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hst)

/-- Parseval and `N η ≤ δ` prove the actual debit bound at every coefficient
state, including query states and the final vertex. -/
theorem debit_le_two_delta (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hparseval : (∑ i, A i) = 1)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hηbudget : (N : ℝ) * η ≤ δ)
    (x : Fin N → ℝ) : debit A δ η x ≤ (2 * δ) • (1 : Matrix n n ℂ) := by
  have hc : ((ksFrozen 1 x).card : ℝ) ≤ N := by exact_mod_cast ksFrozen_card_le 1 x
  have hscalar : ((ksFrozen 1 x).card : ℝ) * η ≤ δ :=
    (mul_le_mul_of_nonneg_right hc hη).trans hηbudget
  have hsum := smul_le_smul_nonneg (sum_frozen_le_one A hA hparseval x) hδ
  have hh := add_le_add hsum (scalar_one_mono (n := n) hscalar)
  have he : δ • (1 : Matrix n n ℂ) + δ • 1 =
      (2 * δ) • (1 : Matrix n n ℂ) := by
    rw [← add_smul]
    congr 1
    ring
  change debit A δ η x ≤ δ • (1 : Matrix n n ℂ) + δ • 1 at hh
  rwa [he] at hh

theorem debit_le_two_delta_of_tolerance (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hparseval : (∑ i, A i) = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hN : 0 < N) (x : Fin N → ℝ) :
    debit A δ (δ / N) x ≤ (2 * δ) • (1 : Matrix n n ℂ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  apply debit_le_two_delta A hA hparseval hδ (div_nonneg hδ hn.le)
  rw [mul_div_cancel₀ _ (ne_of_gt hn)]

/-- The temporary debit used to query a live endpoint also respects the
same budget. The scalar debit is added only after acceptance. -/
theorem query_debit_le_two_delta (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hparseval : (∑ i, A i) = 1)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hηbudget : (N : ℝ) * η ≤ δ)
    {x : Fin N → ℝ} (i : Fin N) (hi : |x i| < 1) :
    debit A δ η x + δ • A i ≤ (2 * δ) • (1 : Matrix n n ℂ) := by
  have hb := debit_le_two_delta A hA hparseval hδ hη hηbudget
    (Function.update x i 1)
  rw [debit_update_endpoint A δ η i hi (Or.inl rfl)] at hb
  have hh : debit A δ η x + δ • A i ≤
      debit A δ η x + δ • A i + η • (1 : Matrix n n ℂ) :=
    le_add_of_nonneg_right (Matrix.PosSemidef.one.smul hη).nonneg
  exact hh.trans hb

theorem debit_norm_le [Nonempty n] (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hparseval : (∑ i, A i) = 1)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hηbudget : (N : ℝ) * η ≤ δ)
    (x : Fin N → ℝ) : ‖debit A δ η x‖ ≤ 2 * δ := by
  have hpos := debit_posSemidef A hA hδ hη x
  apply hermitian_norm_le_of_order hpos.isHermitian
  · exact (neg_nonpos.mpr (Matrix.PosSemidef.one.smul
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ)).nonneg).trans hpos.nonneg
  · exact debit_le_two_delta A hA hparseval hδ hη hηbudget x

/-- A movement that stays in the same open face leaves the recorded debit
exactly unchanged. -/
theorem debit_eq_of_same_frozen (A : Fin N → Matrix n n ℂ) (δ η : ℝ)
    {x y : Fin N → ℝ} (h : ksFrozen 1 x = ksFrozen 1 y) :
    debit A δ η x = debit A δ η y := by
  simp only [debit, h]

end MatrixSpencer.KSDebitBudget
