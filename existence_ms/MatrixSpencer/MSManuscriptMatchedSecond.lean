import MatrixSpencer.MSManuscriptMatchedInterval
import MatrixSpencer.FixedFaceOwnerTaylor

/-! Exact actual second-order coefficient for quadratic owner withdrawal. -/
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.MSManuscriptMatchedSecond
open MSManuscriptMatchedJointBounds
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance : NormedAddCommGroup (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
set_option maxHeartbeats 1000000
attribute [local irreducible] ownerPotential ownerCenterHessian

/-- The covariance derivative and actual center Hessian, with exact factors. -/
theorem second_eq (H B : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    (C Q : selfAdjoint (Matrix ι ι ℝ)) {θ : ℝ} (hθ : 0 < θ)
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    iteratedDeriv 2 (fun t => ownerPotential (center H B t) A (covariance C Q t) θ) 0 / 2 =
      (1/2 : ℝ)*ownerCenterHessian A C θ H B B -
      covarianceDerivativeFunctional A C (hermitianDensityOptimizer H (covarianceKraus A C) θ) Q := by
  have hf : ContDiffAt ℝ 2 (jointHermitianOwnerPotential A θ) (H,C) :=
    (contDiffAt_jointHermitianOwnerPotential A hA hθ H C hC).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hh := iteratedDeriv_comp_matchedCurve_two_zero (jointHermitianOwnerPotential A θ)
    (ownerTaylorEmbedding ((H,C),B,Q)) hf
  simp only [ownerTaylorEmbedding_curve] at hh
  change iteratedDeriv 2 (fun t => ownerPotential (center H B t) A (covariance C Q t) θ) 0 =
    fderiv ℝ (fderiv ℝ (jointHermitianOwnerPotential A θ)) (H,C) (B,0) (B,0)+
      2*fderiv ℝ (jointHermitianOwnerPotential A θ) (H,C) (0,-Q) at hh
  rw [jointOwner_fderiv_fderiv_center A hA hθ H B C hC,
    jointOwner_fderiv_covariance A hA hθ H C Q hC] at hh
  linarith

theorem second_le (H B : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    (C Q : selfAdjoint (Matrix ι ι ℝ)) {θ : ℝ} (hθ : 0 < θ)
    (hC : (C : Matrix ι ι ℝ).PosDef) (hQ : (Q : Matrix ι ι ℝ).PosSemidef) :
    iteratedDeriv 2 (fun t => ownerPotential (center H B t) A (covariance C Q t) θ) 0 / 2 ≤
      (1/2 : ℝ)*ownerCenterHessian A C θ H B B := by
  rw [second_eq H B A hA C Q hθ hC]
  exact sub_le_self _ (covarianceDerivativeFunctional_nonneg A hA hθ H C Q hC hQ)

end MatrixSpencer.MSManuscriptMatchedSecond
