import MatrixSpencer.MatchedOwnerTaylor
import MatrixSpencer.OwnerShavingDerivative
import MatrixSpencer.OwnerResponseGeometry

/-! The actual owner potential on a fixed coefficient face, and its uniform
matched-step expansion. The physical center and original coefficient response
remain in their ambient spaces. No nonempty assumption is imposed on the face. -/

open Set Filter Matrix
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι κ n : Type*} [Fintype ι] [Fintype κ] [Fintype n]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq n]
local instance fixedFaceOwnerCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance fixedFaceOwnerPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance fixedFaceOwnerCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix κ κ ℝ)) := inferInstance

omit [DecidableEq ι] [DecidableEq κ] in
/-- The ambient center Hessian is exactly the mixed-family center Hessian. -/
theorem ownerCenterHessian_covarianceLift (A : ι → Matrix n n ℂ)
    (U : Matrix ι κ ℝ) (K : Matrix κ κ ℝ) (θ : ℝ)
    (H : selfAdjoint (Matrix n n ℂ)) :
    ownerCenterHessian A (covarianceLift U K) θ H = ownerCenterHessian (mixFamily A U) K θ H := by
  have hf : ownerPotentialAsCenter A (covarianceLift U K) θ =
      ownerPotentialAsCenter (mixFamily A U) K θ := by
    funext H
    exact ownerPotential_covarianceLift (H : Matrix n n ℂ) A U K θ
  unfold ownerCenterHessian
  rw [hf]

omit [DecidableEq ι] in
/-- Fixed-face smoothness of the actual potential, including a zero-dimensional face. -/
theorem contDiffAt_ownerPotential_fixedFace [Nonempty n] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (U : Matrix ι κ ℝ) {θ : ℝ} (hθ : 0 < θ)
    (H : selfAdjoint (Matrix n n ℂ)) (K : selfAdjoint (Matrix κ κ ℝ))
    (hK : (K : Matrix κ κ ℝ).PosDef) :
    ContDiffAt ℝ ∞ (fun P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix κ κ ℝ) =>
      ownerPotential P.1 A (covarianceLift U P.2) θ) (H, K) := by
  have hf : (fun P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix κ κ ℝ) =>
      ownerPotential P.1 A (covarianceLift U P.2) θ) =
      jointHermitianOwnerPotential (mixFamily A U) θ := by
    funext P
    exact ownerPotential_covarianceLift (P.1 : Matrix n n ℂ) A U P.2 θ
  rw [hf]
  exact contDiffAt_jointHermitianOwnerPotential (mixFamily A U) (mixFamily_isHermitian A U hA) hθ H K hK

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem covarianceLift_sub_smul (U : Matrix ι κ ℝ) (K Q : Matrix κ κ ℝ) (t : ℝ) :
    covarianceLift U (K - t • Q) = covarianceLift U K - t • covarianceLift U Q := by
  simp only [covarianceLift, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq ι] in
/-- A common mesh for every state and bounded perturbation on a fixed face.
The second derivative appearing here is the actual ambient center Hessian. -/
theorem uniform_owner_matched_taylor_fixedFace [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (U : Matrix ι κ ℝ)
    {θ : ℝ} (hθ : 0 < θ) (R V Q : ℝ) {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ CovarianceCompactChart.parameterChart (n := n) R a V Q (1 : Matrix κ κ ℝ),
      ∀ h ∈ Icc (0 : ℝ) δ,
      |ownerPotential (p.1.1 + h • p.2.1) A
          (covarianceLift U p.1.2 - h ^ 2 • covarianceLift U p.2.2) θ -
        ownerPotential p.1.1 A (covarianceLift U p.1.2) θ -
        h * ownerMatchedLinear (mixFamily A U) θ p -
        h ^ 2 * ((1 / 2 : ℝ) * ownerCenterHessian A (covarianceLift U p.1.2) θ
          p.1.1 p.2.1 p.2.1 - covarianceDerivativeFunctional (mixFamily A U) p.1.2
          (hermitianDensityOptimizer p.1.1 (covarianceKraus (mixFamily A U) p.1.2) θ) p.2.2)|
          ≤ ε * h ^ 2 := by
  obtain ⟨δ, hδ, hb⟩ := uniform_owner_matched_taylor_on_chart (mixFamily A U)
    (mixFamily_isHermitian A U hA) hθ R V Q ha hε
  refine ⟨δ, hδ, ?_⟩
  intro p hp h hh
  have hbound := hb p hp h hh
  rw [← covarianceLift_sub_smul, ownerPotential_covarianceLift, ownerPotential_covarianceLift,
    ownerCenterHessian_covarianceLift]
  exact hbound

/-- Covariance payment is nonnegative in every PSD direction on the reduced face. -/
theorem covarianceDerivativeFunctional_nonneg [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) (H : selfAdjoint (Matrix n n ℂ))
    (C Q : selfAdjoint (Matrix ι ι ℝ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hQ : (Q : Matrix ι ι ℝ).PosSemidef) :
    0 ≤ covarianceDerivativeFunctional A C
      (hermitianDensityOptimizer H (covarianceKraus A C) θ) Q := by
  rw [covarianceDerivativeFunctional_apply A hA]
  have hS := hermitianDensityOptimizer_posDef H (covarianceKraus A C) hθ
  exact realTrace_mul_nonneg (covarianceSupportTransport_posSemidef A hA C _ hC hS)
    (covarianceSource_posSemidef A hA hQ hS.posSemidef)

end
end MatrixSpencer
