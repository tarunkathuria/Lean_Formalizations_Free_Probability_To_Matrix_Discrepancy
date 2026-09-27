import HigherRankKS.MatrixPowerContinuity
import MatrixSpencer.TransportVariational
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.Analysis.Convex.Function

open Matrix Filter MeasureTheory Set
open scoped NNReal Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance matrixPowerConcavityCStar : CStarAlgebra (Matrix n n ℂ) := {}

/-- The inverse tangent remainder is a positive congruence. -/
theorem matrix_inverse_tangent_remainder {A Z : Matrix n n ℂ}
    (hA : A.PosDef) (hZ : Z.IsHermitian) :
    (A⁻¹ - 2 • Z + Z * A * Z).PosSemidef := by
  letI : Invertible A := hA.isUnit.invertible
  have h := hA.inv.posSemidef.conjTranspose_mul_mul_same (1 - A * Z)
  have heq : (1 - A * Z)ᴴ * A⁻¹ * (1 - A * Z) = A⁻¹ - 2 • Z + Z * A * Z := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, hA.isHermitian.eq, hZ.eq]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, Matrix.inv_mul_cancel_left_of_invertible]
    rw [Matrix.mul_inv_of_invertible, Matrix.mul_one]
    module
  rwa [heq] at h

/-- Operator convexity of inverse on positive definite matrices. -/
theorem matrix_inverse_convex {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • A + b • B)⁻¹ ≤ a • A⁻¹ + b • B⁻¹ := by
  let C := a • A + b • B
  have hC : C.PosDef := MatrixSpencer.posDef_convex_mixture hA hB ha hb hab
  letI : Invertible C := hC.isUnit.invertible
  have h₁ := matrix_inverse_tangent_remainder hA hC.inv.isHermitian
  have h₂ := matrix_inverse_tangent_remainder hB hC.inv.isHermitian
  have h := add_nonneg (smul_nonneg ha h₁.nonneg) (smul_nonneg hb h₂.nonneg)
  have heq : a • (A⁻¹ - 2 • C⁻¹ + C⁻¹ * A * C⁻¹) +
      b • (B⁻¹ - 2 • C⁻¹ + C⁻¹ * B * C⁻¹) =
      a • A⁻¹ + b • B⁻¹ - C⁻¹ := by
    have hc : C⁻¹ * (a • A + b • B) * C⁻¹ = C⁻¹ := by
      change C⁻¹ * C * C⁻¹ = C⁻¹
      rw [Matrix.inv_mul_of_invertible, Matrix.one_mul]
    have hs : a • C⁻¹ + b • C⁻¹ = C⁻¹ := by rw [← add_smul, hab, one_smul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul] at hc
    calc
      _ = a • A⁻¹ + b • B⁻¹ - 2 • (a • C⁻¹ + b • C⁻¹) +
          (a • (C⁻¹ * A * C⁻¹) + b • (C⁻¹ * B * C⁻¹)) := by module
      _ = _ := by rw [hs, hc]; module
  rw [heq] at h
  exact sub_nonneg.mp h

/-- The normalized scalar resolvent becomes the concrete matrix inverse. -/
theorem cfc_resolvent_one {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) A = 1 - (1 + A)⁻¹ := by
  have hn : ∀ x ∈ quasispectrum ℝ A, (1 + x : ℝ) ≠ 0 := by
    intro x hx
    have hx0 := quasispectrum_nonneg_of_nonneg A hA.nonneg x hx
    positivity
  have hc : ContinuousOn (fun x : ℝ => (1 + x)⁻¹) (quasispectrum ℝ A) :=
    (continuousOn_const.add continuousOn_id).inv₀ hn
  have hc' := hc.mono (spectrum_subset_quasispectrum ℝ A)
  have hn' : ∀ x ∈ spectrum ℝ A, (1 + x : ℝ) ≠ 0 :=
    fun x hx => hn x (spectrum_subset_quasispectrum ℝ A hx)
  rw [cfcₙ_eq_cfc (continuousOn_const.sub hc) (by norm_num),
    cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => (1 + x)⁻¹) A
      continuousOn_const hc', cfc_const_one ℝ A,
    cfc_inv (fun x : ℝ => 1 + x) A hn',
    cfc_const_add 1 (fun x : ℝ => x) A, cfc_id' ℝ A, map_one,
    ← Matrix.nonsing_inv_eq_ringInverse]

/-- Concavity of the normalized positive resolvent. -/
theorem matrix_resolvent_one_concave {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • (1 - (1 + A)⁻¹) + b • (1 - (1 + B)⁻¹) ≤
      1 - (1 + (a • A + b • B))⁻¹ := by
  have hAp : (1 + A).PosDef := Matrix.PosDef.one.add_posSemidef hA
  have hBp : (1 + B).PosDef := Matrix.PosDef.one.add_posSemidef hB
  have h := matrix_inverse_convex hAp hBp ha hb hab
  have heq : a • (1 + A) + b • (1 + B) = 1 + (a • A + b • B) := by
    rw [smul_add, smul_add]
    have hh : a • (1 : Matrix n n ℂ) + b • 1 = 1 := by rw [← add_smul, hab, one_smul]
    calc
      _ = (a • (1 : Matrix n n ℂ) + b • 1) + (a • A + b • B) := by abel
      _ = _ := by rw [hh]
  rw [heq] at h
  have hh : a • (1 : Matrix n n ℂ) + b • 1 = 1 := by rw [← add_smul, hab, one_smul]
  calc
    _ = 1 - (a • (1 + A)⁻¹ + b • (1 + B)⁻¹) := by
      simp only [smul_sub]
      calc
        _ = (a • (1 : Matrix n n ℂ) + b • 1) -
            (a • (1 + A)⁻¹ + b • (1 + B)⁻¹) := by abel
        _ = _ := by rw [hh]
    _ ≤ _ := sub_le_sub_left h 1

/-- Concavity of every integrand in the positive power representation. -/
theorem matrix_rpow_integrand_concave {p t : ℝ} (hp : p ∈ Ioo 0 1) (ht : 0 < t)
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • cfcₙ (Real.rpowIntegrand₀₁ p t) A + b • cfcₙ (Real.rpowIntegrand₀₁ p t) B ≤
      cfcₙ (Real.rpowIntegrand₀₁ p t) (a • A + b • B) := by
  have hC : (a • A + b • B).PosSemidef :=
    (add_nonneg (smul_nonneg ha hA.nonneg) (smul_nonneg hb hB.nonneg)).posSemidef
  rw [CFC.cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one hp ht A hA.nonneg,
    CFC.cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one hp ht B hB.nonneg,
    CFC.cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one hp ht _ hC.nonneg]
  have hf : Real.rpowIntegrand₀₁ p 1 = fun x : ℝ => 1 - (1 + x)⁻¹ := by
    funext x
    simp [Real.rpowIntegrand₀₁]
  rw [hf]
  have hAi : (t⁻¹ • A).PosSemidef := (smul_nonneg (inv_pos.mpr ht).le hA.nonneg).posSemidef
  have hBi : (t⁻¹ • B).PosSemidef := (smul_nonneg (inv_pos.mpr ht).le hB.nonneg).posSemidef
  have hCi : (t⁻¹ • (a • A + b • B)).PosSemidef :=
    (smul_nonneg (inv_pos.mpr ht).le hC.nonneg).posSemidef
  rw [cfc_resolvent_one hAi, cfc_resolvent_one hBi, cfc_resolvent_one hCi]
  have h := smul_le_smul_of_nonneg_left (matrix_resolvent_one_concave hAi hBi ha hb hab)
    (Real.rpow_pos_of_pos ht (p - 1)).le
  simpa only [smul_add, smul_comm t⁻¹ a A, smul_comm t⁻¹ b B,
    smul_comm (t ^ (p - 1)) a, smul_comm (t ^ (p - 1)) b] using h

/-- Operator concavity of fractional real powers on all PSD matrices,
including singular matrices and endpoint mixture weights. -/
theorem matrix_rpow_concave {p : ℝ} (hp : p ∈ Ioo 0 1)
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • CFC.rpow A p + b • CFC.rpow B p ≤ CFC.rpow (a • A + b • B) p := by
  let q : ℝ≥0 := ⟨p, hp.1.le⟩
  have hq : q ∈ Ioo 0 1 := ⟨hp.1, hp.2⟩
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁
    (Matrix n n ℂ) hq
  have hC : (a • A + b • B).PosSemidef :=
    (add_nonneg (smul_nonneg ha hA.nonneg) (smul_nonneg hb hB.nonneg)).posSemidef
  have hrep (M : Matrix n n ℂ) (hM : M.PosSemidef) :
      CFC.rpow M p = ∫ t in Ioi 0, cfcₙ (Real.rpowIntegrand₀₁ p t) M ∂μ := by
    change M ^ (q : ℝ) = _
    rw [← CFC.nnrpow_eq_rpow hq.1]
    exact (hμ M hM.nonneg).2
  have hIA : Integrable (fun t => a • cfcₙ (Real.rpowIntegrand₀₁ p t) A)
      (μ.restrict (Ioi 0)) := (hμ A hA.nonneg).1.smul a
  have hIB : Integrable (fun t => b • cfcₙ (Real.rpowIntegrand₀₁ p t) B)
      (μ.restrict (Ioi 0)) := (hμ B hB.nonneg).1.smul b
  rw [hrep A hA, hrep B hB, hrep _ hC, ← integral_smul, ← integral_smul,
    ← integral_add hIA hIB]
  apply integral_mono_ae
    (hIA.add hIB)
    (hμ _ hC.nonneg).1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact matrix_rpow_integrand_concave hp ht hA hB ha hb hab

end HigherRankKS
