import MatrixSpencer.RectangularRidgeCoefficientResponse

/-! The cap-to-response theorem for the actual mixed optimized potential.
This instantiates the pointwise inverse comparison at the mixed optimizer,
with its own Gram cap; no old-optimizer comparison is made. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeCalculus
open RectangularRidgePotential RectangularRidgeOwnerFrame
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance ridgeActualResponseLocal1 : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeActualResponseLocal2 : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeActualResponseLocal3 : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance ridgeActualResponseLocal4 : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
set_option maxHeartbeats 300000
attribute [local irreducible] RectangularRidgePotential.optimizer

theorem krausObservedResponse_eq_inverse (H : selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) :
    krausObservedResponse H B hB m θ κ =
      RectangularRidgeResponse.observedResponse B hB
        (tangentHessianEquiv (H : Matrix n n ℂ) B m hm θ κ hθ hκ (hermitianOptimizer (H : Matrix n n ℂ) B m θ κ)
          (hermitianOptimizer_posDef (H : Matrix n n ℂ) B m hm θ κ hθ hκ)) := by
  unfold krausObservedResponse RectangularRidgeResponse.observedResponse
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact potential_hessian_eq_inverse H (hermitianMatrixFamily B hB a) B m hm θ κ hθ hκ

/-- The same dyadic response rate holds for the actual ridge-regularized
potential at all physical and covariance ranks. -/
theorem owner_response_le_of_ownedGram_cap
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    (m : ℕ) (hm : 1 ≤ m) {θ κ L : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (hL : 0 < L) (hk : 0 < Fintype.card ι)
    (hcap : ∀ u : EuclideanSpace ℝ ι,
      u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap →
      WithLp.ofLp u ⬝ᵥ (ownedGram A C (optimizer (H : Matrix n n ℂ) (covarianceKraus A C) m θ κ) *ᵥ WithLp.ofLp u) ≤
        (L / Real.sqrt (Fintype.card ι : ℝ)) * (WithLp.ofLp u ⬝ᵥ WithLp.ofLp u)) :
    realTrace (C * ownerCoefficientResponse A hA C m θ κ H) ≤
      2 * Real.sqrt (Fintype.card ι : ℝ) +
        (6 * L ^ (1 / (2 : ℝ) ^ m) / (θ * (1 / (2 : ℝ) ^ m))) *
          (Fintype.card ι : ℝ) ^ (1 - 1 / (2 : ℝ) ^ m) := by
  rw [ownerCoefficientResponse_trace_eq A hA hC m θ κ H,
    krausObservedResponse_eq_inverse H (covarianceKraus A C) (covarianceKraus_isHermitian A hA C)
      m hm θ κ hθ hκ]
  exact RectangularRidgeResponse.owner_response_le_of_ownedGram_cap (H : Matrix n n ℂ) A hA hN hC hC1 m hm hθ hL hk
    (hermitianOptimizer (H : Matrix n n ℂ) (covarianceKraus A C) m θ κ)
    (hermitianOptimizer_posDef (H : Matrix n n ℂ) (covarianceKraus A C) m hm θ κ hθ hκ)
    (hermitianOptimizer_trace (H : Matrix n n ℂ) (covarianceKraus A C) m θ κ).le _
    (tangentHessianEquiv_ge_dyadic (H : Matrix n n ℂ) (covarianceKraus A C) m hm θ κ hθ hκ
      (hermitianOptimizer (H : Matrix n n ℂ) (covarianceKraus A C) m θ κ)
      (hermitianOptimizer_posDef (H : Matrix n n ℂ) (covarianceKraus A C) m hm θ κ hθ hκ)) hcap

end MatrixSpencer.RectangularRidgeCalculus
