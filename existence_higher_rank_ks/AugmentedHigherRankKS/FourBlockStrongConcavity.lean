import AugmentedHigherRankKS.FourBlockPotentialHessian
import MatrixSpencer.KSObjectiveUpper

/-! Quantitative density curvature, derived from the root regularizer. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance strongConcavityCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}

theorem hermitianObjective_strongConcavity (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1) :
    θ / 2 * ‖X‖ ^ 2 ≤
      -fderiv ℝ (fderiv ℝ (hermitianObjective H A ((1 : ℝ) / 2 ^ k) c θ)) S X X := by
  have hSone : (S : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ 1 := by
    simpa only [ht, map_one] using posSemidef_le_trace_identity hS.posSemidef
  have hr := KSObjectiveCurvature.negativeTsallisHessian_ge θ hθ S X hS hSone
  have hn := KSObjectiveUpper.norm_sq_le_trace_square X.property
  have hs := nonlinearSourceFidelity_hessian_nonpos A hA k hk c hc S X hS
  rw [hermitianObjective_hessian_apply H A hA k hk c hc θ S X X hS,
    fderiv_fderiv_tsallisPotential_apply θ hθ.ne' S X X hS]
  rw [realTrace_mul_comm (X : Matrix (FourSpin n) (FourSpin n) ℂ)
    (negativeTsallisHessianEquiv θ hθ.ne' S hS X : Matrix (FourSpin n) (FourSpin n) ℂ)] at hr
  have hh := mul_le_mul_of_nonneg_left hn (show 0 ≤ θ / 2 by positivity)
  change θ / 2 * ‖(X : Matrix (FourSpin n) (FourSpin n) ℂ)‖ ^ 2 ≤ _
  linarith

/-- The density chart preserves the quantitative coercivity used in the implicit bound. -/
theorem chartObjective_strongConcavity
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 < θ)
    (H : ℝ → Matrix (FourSpin n) (FourSpin n) ℂ) (c : ℝ → ι → ℝ)
    (hc : ∀ i, 0 < c 0 i)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    (hF : ContDiffAt ℝ 2 (chartObjective H A ((1 : ℝ) / 2 ^ k) c θ S)
      ((0 : ℝ), (0 : densityTangent (n := FourSpin n))))
    (X : densityTangent (n := FourSpin n)) :
    θ / 2 * ‖X‖ ^ 2 ≤
      -fderiv ℝ (fderiv ℝ (chartObjective H A ((1 : ℝ) / 2 ^ k) c θ S))
        (0, 0) (0, X) (0, X) := by
  rw [← OptimizerHessian.vertical_hessian _ 0 0 X hF]
  change θ / 2 * ‖X‖ ^ 2 ≤
    -fderiv ℝ (fderiv ℝ (fun Y => hermitianObjective (H 0) A ((1 : ℝ) / 2 ^ k)
      (c 0) θ (densityChart S Y))) 0 X X
  rw [OptimizerResponse.densityChart_hessian_apply
    (hermitianObjective (H 0) A ((1 : ℝ) / 2 ^ k) (c 0) θ) S
    (contDiffAt_hermitianObjective (H 0) A hA k hk (c 0) hc θ S hS) X X]
  exact hermitianObjective_strongConcavity (H 0) A hA k hk (c 0) hc θ hθ S X hS ht

end AugmentedHigherRankKS
