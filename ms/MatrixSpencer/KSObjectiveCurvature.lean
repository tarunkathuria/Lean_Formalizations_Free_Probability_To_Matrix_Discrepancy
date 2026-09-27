import MatrixSpencer.SingularDensityCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Explicit coercivity of the actual regularized density objective

The norm geometry in the bound is the real trace (Hilbert--Schmidt) pairing.
The bound is uniform on all faithful trace-one densities and does not assume
faithfulness of the Kraus source. This file does not provide an upper Hessian
bound or a numerical value/projection oracle.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace MatrixSpencer.KSObjectiveCurvature

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

local instance : CStarAlgebra (Matrix n n ℂ) := {}

theorem one_le_inverse_of_le_one {Q : Matrix n n ℂ}
    (hQ : Q.PosDef) (hQone : Q ≤ 1) : 1 ≤ Q⁻¹ := by
  obtain ⟨u, rfl⟩ := hQ.isUnit
  rw [← Matrix.coe_units_inv]
  exact (CStarAlgebra.one_le_inv_iff_le_one hQ.posSemidef.nonneg).mpr hQone

theorem sylvester_trace_square_le (Q U : Matrix n n ℂ)
    (hQ : Q.IsHermitian) (hU : U.IsHermitian) (hQsq : Q * Q ≤ 1) :
    realTrace ((Q * U + U * Q) * (Q * U + U * Q)) ≤
      4 * realTrace (U * U) := by
  have hcross := realTrace_mul_mul_mul_le hU hQ
  have hUU : (U * U).PosSemidef := by
    simpa only [hU.eq] using Matrix.posSemidef_conjTranspose_mul_self U
  have hcap := realTrace_mul_mono hUU hQsq
  have h₁ : realTrace (Q * U * (Q * U)) = realTrace (U * Q * U * Q) := by
    simpa only [Matrix.mul_assoc] using realTrace_mul_comm Q (U * Q * U)
  have h₂ : realTrace (Q * U * (U * Q)) = realTrace (U * U * Q * Q) := by
    simpa only [Matrix.mul_assoc] using realTrace_mul_comm Q (U * U * Q)
  have h₃ : realTrace (U * Q * (Q * U)) = realTrace (U * U * Q * Q) := by
    simpa only [Matrix.mul_assoc] using realTrace_mul_comm (U * Q * Q) U
  simp only [Matrix.add_mul, Matrix.mul_add, realTrace_add]
  rw [h₁, h₂, h₃]
  simp only [Matrix.mul_one, ← Matrix.mul_assoc] at hcap ⊢
  linarith

/-- The actual negative Tsallis Hessian is at least `θ/2` in trace geometry. -/
theorem negativeTsallisHessian_ge (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hSone : (S : Matrix n n ℂ) ≤ 1) :
    θ / 2 * realTrace ((X : Matrix n n ℂ) * (X : Matrix n n ℂ)) ≤
      realTrace ((X : Matrix n n ℂ) *
        (negativeTsallisHessianEquiv θ hθ.ne' S hS X : Matrix n n ℂ)) := by
  let Q := CFC.sqrt (S : Matrix n n ℂ)
  let U := (sylvesterEquiv Q hS.posDef_sqrt).symm (X : Matrix n n ℂ)
  have hU : U.IsHermitian := sylvester_inverse_isHermitian Q hS.posDef_sqrt X.property
  have hUX : Q * U + U * Q = (X : Matrix n n ℂ) :=
    sylvester_inverse_solve Q hS.posDef_sqrt X
  have hQone : Q ≤ 1 := by
    simpa only [CFC.sqrt_one] using CFC.sqrt_le_sqrt (S : Matrix n n ℂ) 1 hSone
  have hQi := one_le_inverse_of_le_one hS.posDef_sqrt hQone
  have hUU : (U * U).PosSemidef := by
    simpa only [hU.eq] using Matrix.posSemidef_conjTranspose_mul_self U
  have hweight := realTrace_mul_mono hUU hQi
  have hcycle : realTrace (U * U * Q⁻¹) = realTrace (U * Q⁻¹ * U) := by
    simpa only [Matrix.mul_assoc] using realTrace_mul_comm U (U * Q⁻¹)
  simp only [Matrix.mul_one] at hweight
  rw [hcycle] at hweight
  have hQsq : Q * Q ≤ 1 := by
    dsimp [Q]
    rwa [CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg]
  have hsq := sylvester_trace_square_le Q U hS.posDef_sqrt.isHermitian hU hQsq
  rw [hUX] at hsq
  rw [negativeTsallisHessianEquiv_apply, fderiv_hermitianSqrt_eq S hS,
    Matrix.mul_smul, realTrace_smul]
  change θ / 2 * realTrace ((X : Matrix n n ℂ) * (X : Matrix n n ℂ)) ≤
    θ * realTrace ((X : Matrix n n ℂ) * (Q⁻¹ * U * Q⁻¹))
  conv_rhs => rw [← hUX, realTrace_sylvester_conjugate Q U hS.posDef_sqrt.isUnit]
  nlinarith [mul_le_mul_of_nonneg_left hweight hθ.le,
    mul_le_mul_of_nonneg_left hsq hθ.le]

/-- Explicit strong concavity of the original density objective. The fidelity
term is handled by the proved source-unrestricted Hessian sign theorem. -/
theorem densityNegativeHessian_ge (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S X : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hSone : (S : Matrix n n ℂ) ≤ 1) :
    θ / 2 * realTrace ((X : Matrix n n ℂ) * (X : Matrix n n ℂ)) ≤
      densityNegativeHessian H B θ S X X := by
  have hf := fderiv_fderiv_krausSourceFidelity_quadratic_nonpos_source_unrestricted B S X hS
  have ht := negativeTsallisHessian_ge θ hθ S X hS hSone
  rw [realTrace_mul_comm (X : Matrix n n ℂ)
    (negativeTsallisHessianEquiv θ hθ.ne' S hS X : Matrix n n ℂ)] at ht
  simp only [densityNegativeHessian, ContinuousLinearMap.neg_apply]
  rw [fderiv_fderiv_hermitianDensityObjective_apply_source_unrestricted H B θ S X X hS,
    fderiv_fderiv_tsallisPotential_apply θ hθ.ne' S X X hS]
  linarith

theorem densityNegativeHessian_ge_of_density (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (htr : realTrace (S : Matrix n n ℂ) = 1) :
    θ / 2 * realTrace ((X : Matrix n n ℂ) * (X : Matrix n n ℂ)) ≤
      densityNegativeHessian H B θ S X X := by
  apply densityNegativeHessian_ge H B θ hθ S X hS
  simpa only [htr, map_one] using posSemidef_le_trace_identity hS.posSemidef

end MatrixSpencer.KSObjectiveCurvature
