import MatrixSpencer.SignedLift

/-! Dimension-free owner-potential bounds from an actual physical variance bound. -/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

local instance ksVarianceCStarAlgebra : CStarAlgebra (Matrix n n ℂ) := {}

theorem ks_density_source_trace_le_variance
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {κ : ℝ}
    (hvar : covarianceSource A C 1 ≤ κ • (1 : Matrix n n ℂ))
    {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    realTrace (covarianceSource A C S) ≤ κ := by
  have ht := realTrace_covarianceSource_selfadjoint A hA hC S 1
  rw [Matrix.mul_one] at ht
  rw [ht]
  have hm := realTrace_mul_mono hS.1 hvar
  simpa only [Matrix.mul_smul, Matrix.mul_one, realTrace_smul, hS.2, mul_one] using hm

theorem ks_density_fidelity_le_variance
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {κ : ℝ}
    (hvar : covarianceSource A C 1 ≤ κ • (1 : Matrix n n ℂ))
    {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    fidelity S (covarianceSource A C S) ≤ Real.sqrt κ := by
  have hf := fidelity_le_sqrt_trace_mul hS.1 (covarianceSource_posSemidef A hA hC hS.1)
  rw [hS.2, one_mul] at hf
  exact hf.trans (Real.sqrt_le_sqrt (ks_density_source_trace_le_variance A hA hC hvar hS))

theorem ks_ownerPotential_le_variance [Nonempty n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {κ θ : ℝ} (hθ : 0 ≤ θ)
    (hvar : covarianceSource A C 1 ≤ κ • (1 : Matrix n n ℂ)) :
    ownerPotential H A C θ ≤
      ‖H‖ + 2 * Real.sqrt κ + 2 * θ * Real.sqrt (Fintype.card n : ℝ) := by
  obtain ⟨T, hT, hmax⟩ := exists_densityOptimizer H (covarianceKraus A C) θ
  rw [ownerPotential_eq_densityPotential H A hA hC θ,
    densityPotential_eq_of_maximizer H _ θ hT hmax,
    ← ownerObjective_eq_densityObjective H A hA hC θ T]
  have hf := ks_density_fidelity_le_variance A hA hC hvar hT
  have hh := realTrace_mul_density_le_norm hH hT
  have hr := mul_le_mul_of_nonneg_left (density_trace_sqrt_le_sqrt_card hT)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hθ)
  unfold ownerObjective
  linarith

theorem ks_norm_le_signedLift_ownerPotential [Nonempty n]
    {B : Matrix n n ℂ} (hB : B.IsHermitian)
    (A : ι → Matrix (n ⊕ n) (n ⊕ n) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ : ℝ} (hθ : 0 ≤ θ) :
    ‖B‖ ≤ ownerPotential (signedLift B) A C θ := by
  rw [ownerPotential_eq_densityPotential (signedLift B) A hA hC θ]
  exact norm_le_signedLift_densityPotential hB (covarianceKraus A C) hθ

end MatrixSpencer
