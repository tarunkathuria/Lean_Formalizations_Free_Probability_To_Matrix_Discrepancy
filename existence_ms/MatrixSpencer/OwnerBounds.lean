import MatrixSpencer.OwnerPotential
import MatrixSpencer.CovarianceBounds
import MatrixSpencer.FidelityBounds

/-!
# Elementary bounds for the actual owner potential

The free-covariance excess is at most twice the square root of the number
of retained labels. The density regularizer is never restarted here.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

local instance ownerBoundsCStarAlgebra : CStarAlgebra (Matrix n n ℂ) := {}

omit [Fintype ι] [DecidableEq ι] in
theorem realTrace_mul_density_le_norm {H S : Matrix n n ℂ}
    (hH : H.IsHermitian) (hS : S ∈ densitySet) : realTrace (H * S) ≤ ‖H‖ := by
  have h := realTrace_mul_mono hS.1 (IsSelfAdjoint.le_algebraMap_norm_self hH)
  rw [realTrace_mul_comm S H, Algebra.algebraMap_eq_smul_one,
    Matrix.mul_smul, Matrix.mul_one, realTrace_smul, hS.2, mul_one] at h
  exact h

omit [Fintype ι] [DecidableEq ι] in
theorem abs_realTrace_mul_density_le_norm {H S : Matrix n n ℂ}
    (hH : H.IsHermitian) (hS : S ∈ densitySet) : |realTrace (H * S)| ≤ ‖H‖ := by
  apply abs_le.mpr
  have hu := realTrace_mul_density_le_norm hH hS
  have hl := realTrace_mul_density_le_norm hH.neg hS
  simp only [Matrix.neg_mul, realTrace_neg, norm_neg] at hl
  exact ⟨by linarith, hu⟩

omit [Fintype ι] [DecidableEq ι] in
theorem density_trace_sqrt_le_sqrt_card {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    realTrace (CFC.sqrt S) ≤ Real.sqrt (Fintype.card n : ℝ) := by
  exact (Real.le_sqrt (realTrace_nonneg (CFC.sqrt_nonneg S).posSemidef)
    (Nat.cast_nonneg _)).mpr (density_trace_sqrt_sq_le_card hS)

theorem density_ownerFidelity_le_sqrt_card (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    fidelity S (covarianceSource A C S) ≤ Real.sqrt (Fintype.card ι : ℝ) := by
  have hf := fidelity_le_sqrt_trace_mul hS.1 (covarianceSource_posSemidef A hA hC0 hS.1)
  rw [hS.2, one_mul] at hf
  exact hf.trans (Real.sqrt_le_sqrt (density_covarianceSource_trace_le_card A hA hN hC0 hC1 hS))

/-- The zero-covariance potential, with the same center and regularizer. -/
def baseDensityPotential (H : Matrix n n ℂ) (θ : ℝ) : ℝ :=
  densityPotential H (fun _ : Empty => (0 : Matrix n n ℂ)) θ

omit [Fintype ι] [DecidableEq ι] in
theorem densityObjective_empty (H : Matrix n n ℂ) (θ : ℝ) (S : Matrix n n ℂ) :
    densityObjective H (fun _ : Empty => (0 : Matrix n n ℂ)) θ S =
      realTrace (H * S) + 2 * θ * realTrace (CFC.sqrt S) := by
  simp [densityObjective, krausChannel, fidelity, fidelityCore, realTrace_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem baseDensityObjective_le_potential [Nonempty n]
    (H : Matrix n n ℂ) (θ : ℝ) {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    realTrace (H * S) + 2 * θ * realTrace (CFC.sqrt S) ≤ baseDensityPotential H θ := by
  simpa only [densityObjective_empty] using
    densityObjective_le_potential H (fun _ : Empty => (0 : Matrix n n ℂ)) θ hS

/-- Retained covariance contributes a nonnegative excess. -/
theorem baseDensityPotential_le_owner [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ : ℝ) :
    baseDensityPotential H θ ≤ ownerPotential H A C θ := by
  obtain ⟨S, hS, hmax⟩ := exists_densityOptimizer H (fun _ : Empty => (0 : Matrix n n ℂ)) θ
  unfold baseDensityPotential
  rw [densityPotential_eq_of_maximizer H _ θ hS hmax, densityObjective_empty,
    ownerPotential_eq_densityPotential H A hA hC θ]
  apply le_trans _ (densityObjective_le_potential H (covarianceKraus A C) θ hS)
  unfold densityObjective
  linarith [fidelity_nonneg S (krausChannel (covarianceKraus A C) S)]

/-- The covariance excess has no dependence on the physical dimension. -/
theorem ownerPotential_le_base_add [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, ‖A i‖ ≤ 1) {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    (θ : ℝ) : ownerPotential H A C θ ≤
      baseDensityPotential H θ + 2 * Real.sqrt (Fintype.card ι : ℝ) := by
  obtain ⟨S, hS, hmax⟩ := exists_densityOptimizer H (covarianceKraus A C) θ
  rw [ownerPotential_eq_densityPotential H A hA hC0 θ,
    densityPotential_eq_of_maximizer H _ θ hS hmax,
    ← ownerObjective_eq_densityObjective H A hA hC0 θ S]
  have hf := density_ownerFidelity_le_sqrt_card A hA hN hC0 hC1 hS
  have hb := baseDensityObjective_le_potential H θ hS
  unfold ownerObjective
  linarith

/-- A direct bound at any Hermitian center, with the physical dimension explicit. -/
theorem ownerPotential_le_norm_add [Nonempty n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ) : ownerPotential H A C θ ≤
      ‖H‖ + 2 * Real.sqrt (Fintype.card ι : ℝ) + 2 * θ * Real.sqrt (Fintype.card n : ℝ) := by
  obtain ⟨S, hS, hmax⟩ := exists_densityOptimizer H (covarianceKraus A C) θ
  rw [ownerPotential_eq_densityPotential H A hA hC0 θ,
    densityPotential_eq_of_maximizer H _ θ hS hmax,
    ← ownerObjective_eq_densityObjective H A hA hC0 θ S]
  have hf := density_ownerFidelity_le_sqrt_card A hA hN hC0 hC1 hS
  have hh := realTrace_mul_density_le_norm hH hS
  have hr := mul_le_mul_of_nonneg_left (density_trace_sqrt_le_sqrt_card hS)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hθ)
  unfold ownerObjective
  linarith

/-- Changing the center costs at most its Euclidean operator norm. -/
theorem ownerPotential_sub_le_norm [Nonempty n]
    {H H' : Matrix n n ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ : ℝ) :
    ownerPotential H' A C θ - ownerPotential H A C θ ≤ ‖H' - H‖ := by
  obtain ⟨S, hS, hmax⟩ := exists_densityOptimizer H' (covarianceKraus A C) θ
  rw [ownerPotential_eq_densityPotential H' A hA hC θ,
    densityPotential_eq_of_maximizer H' _ θ hS hmax,
    ownerPotential_eq_densityPotential H A hA hC θ,
    densityObjective_center_difference H H' S]
  have hb := densityObjective_le_potential H (covarianceKraus A C) θ hS
  have ht := realTrace_mul_density_le_norm (hH'.sub hH) hS
  linarith

theorem abs_ownerPotential_sub_le_norm [Nonempty n]
    {H H' : Matrix n n ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ : ℝ) :
    |ownerPotential H' A C θ - ownerPotential H A C θ| ≤ ‖H' - H‖ := by
  apply abs_le.mpr
  have hu := ownerPotential_sub_le_norm hH hH' A hA hC θ
  have hl := ownerPotential_sub_le_norm hH' hH A hA hC θ
  rw [norm_sub_rev H H'] at hl
  exact ⟨by linarith, hu⟩

/-- Initial potential after the signed lift, whose physical dimension is at most twice the count. -/
theorem ownerPotential_initial_le_five [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (hd : Fintype.card n ≤ 2 * Fintype.card ι) :
    ownerPotential 0 A 1 1 ≤ 5 * Real.sqrt (Fintype.card ι : ℝ) := by
  have h := ownerPotential_le_norm_add Matrix.isHermitian_zero A hA hN
    Matrix.PosSemidef.one le_rfl (by norm_num : (0 : ℝ) ≤ 1)
  have hd' : (Fintype.card n : ℝ) ≤ 2 * (Fintype.card ι : ℝ) := by exact_mod_cast hd
  have hn0 : (0 : ℝ) ≤ Fintype.card n := Nat.cast_nonneg _
  have hi0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hnroot := Real.sq_sqrt hn0
  have hiroot := Real.sq_sqrt hi0
  have hnroot0 := Real.sqrt_nonneg (Fintype.card n : ℝ)
  have hiroot0 := Real.sqrt_nonneg (Fintype.card ι : ℝ)
  have hratio : 2 * Real.sqrt (Fintype.card n : ℝ) ≤
      3 * Real.sqrt (Fintype.card ι : ℝ) := by nlinarith
  simp only [norm_zero, zero_add, mul_one] at h
  linarith

/-- Installing a new identity-bounded owner costs only its label-count excess. -/
theorem ownerPotential_refresh_le [Nonempty n]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (A' : κ → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hA' : ∀ i, (A' i).IsHermitian)
    (hN' : ∀ i, ‖A' i‖ ≤ 1) {C : Matrix ι ι ℝ} {C' : Matrix κ κ ℝ}
    (hC : C.PosSemidef) (hC' : C'.PosSemidef) (hC'1 : C' ≤ 1) (θ : ℝ) :
    ownerPotential H A' C' θ - ownerPotential H A C θ ≤
      2 * Real.sqrt (Fintype.card κ : ℝ) := by
  have hold := baseDensityPotential_le_owner H A hA hC θ
  have hnew := ownerPotential_le_base_add H A' hA' hN' hC' hC'1 θ
  linarith

end MatrixSpencer
