import MatrixSpencer.FixedFaceOwnerTaylor
import MatrixSpencer.DyadicMatchedOwnerTaylor
import MatrixSpencer.DyadicOwnerFunctions

/-! Actual dyadic potential calculus on every coefficient face, including an empty face. -/
open Set Filter Matrix
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι κ n : Type*} [Fintype ι] [Fintype κ] [Fintype n]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq n]
local instance dyadicFixedFaceOwnerCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicFixedFaceOwnerPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicFixedFaceOwnerCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix κ κ ℝ)) := inferInstance

omit [DecidableEq ι] [DecidableEq κ] in
/-- The ambient center Hessian is exactly the mixed-family center Hessian. -/
theorem dyadicOwnerCenterHessian_covarianceLift (A : ι → Matrix n n ℂ)
    (U : Matrix ι κ ℝ) (K : Matrix κ κ ℝ) (m : ℕ) (θ : ℝ)
    (H : selfAdjoint (Matrix n n ℂ)) :
    dyadicOwnerCenterHessian A (covarianceLift U K) m θ H = dyadicOwnerCenterHessian (mixFamily A U) K m θ H := by
  have hf : dyadicOwnerPotentialAsCenter A (covarianceLift U K) m θ =
      dyadicOwnerPotentialAsCenter (mixFamily A U) K m θ := by
    funext H
    exact dyadicOwnerPotential_covarianceLift (H : Matrix n n ℂ) A U K m θ
  unfold dyadicOwnerCenterHessian
  rw [hf]

omit [DecidableEq ι] in
/-- Fixed-face smoothness of the actual potential, including a zero-dimensional face. -/
theorem contDiffAt_dyadicOwnerPotential_fixedFace [Nonempty n] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (U : Matrix ι κ ℝ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (H : selfAdjoint (Matrix n n ℂ)) (K : selfAdjoint (Matrix κ κ ℝ))
    (hK : (K : Matrix κ κ ℝ).PosDef) :
    ContDiffAt ℝ ∞ (fun P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix κ κ ℝ) =>
      dyadicOwnerPotential P.1 A (covarianceLift U P.2) m θ) (H, K) := by
  have hf : (fun P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix κ κ ℝ) =>
      dyadicOwnerPotential P.1 A (covarianceLift U P.2) m θ) =
      jointHermitianDyadicOwnerPotential (mixFamily A U) m θ := by
    funext P
    exact dyadicOwnerPotential_covarianceLift (P.1 : Matrix n n ℂ) A U P.2 m θ
  rw [hf]
  exact contDiffAt_jointHermitianDyadicOwnerPotential (mixFamily A U) (mixFamily_isHermitian A U hA) m hm θ hθ H K hK

omit [DecidableEq ι] in
/-- A common mesh for every state and bounded perturbation on a fixed face.
The second derivative appearing here is the actual ambient center Hessian. -/
theorem uniform_dyadicOwner_matched_taylor_fixedFace [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (U : Matrix ι κ ℝ)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (R V Q : ℝ) {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ CovarianceCompactChart.parameterChart (n := n) R a V Q (1 : Matrix κ κ ℝ),
      ∀ h ∈ Icc (0 : ℝ) δ,
      |dyadicOwnerPotential (p.1.1 + h • p.2.1) A
          (covarianceLift U p.1.2 - h ^ 2 • covarianceLift U p.2.2) m θ -
        dyadicOwnerPotential p.1.1 A (covarianceLift U p.1.2) m θ -
        h * dyadicOwnerMatchedLinear (mixFamily A U) m θ p -
        h ^ 2 * ((1 / 2 : ℝ) * dyadicOwnerCenterHessian A (covarianceLift U p.1.2) m θ
          p.1.1 p.2.1 p.2.1 - covarianceDerivativeFunctional (mixFamily A U) p.1.2
          (hermitianDyadicDensityOptimizer p.1.1 (covarianceKraus (mixFamily A U) p.1.2) m θ) p.2.2)|
          ≤ ε * h ^ 2 := by
  obtain ⟨δ, hδ, hb⟩ := uniform_dyadicOwner_matched_taylor_on_chart (mixFamily A U)
    (mixFamily_isHermitian A U hA) m hm θ hθ R V Q ha hε
  refine ⟨δ, hδ, ?_⟩
  intro p hp h hh
  have hbound := hb p hp h hh
  rw [← covarianceLift_sub_smul, dyadicOwnerPotential_covarianceLift, dyadicOwnerPotential_covarianceLift,
    dyadicOwnerCenterHessian_covarianceLift]
  exact hbound

/-- Covariance payment is nonnegative in every PSD direction on the reduced face. -/
theorem covarianceDerivativeFunctional_dyadic_nonneg [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (H : selfAdjoint (Matrix n n ℂ))
    (C Q : selfAdjoint (Matrix ι ι ℝ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hQ : (Q : Matrix ι ι ℝ).PosSemidef) :
    0 ≤ covarianceDerivativeFunctional A C
      (hermitianDyadicDensityOptimizer H (covarianceKraus A C) m θ) Q := by
  rw [covarianceDerivativeFunctional_apply A hA]
  have hS := hermitianDyadicDensityOptimizer_posDef H (covarianceKraus A C) m hm θ hθ
  exact realTrace_mul_nonneg (covarianceSupportTransport_posSemidef A hA C _ hC hS)
    (covarianceSource_posSemidef A hA hQ hS.posSemidef)

end
end MatrixSpencer
