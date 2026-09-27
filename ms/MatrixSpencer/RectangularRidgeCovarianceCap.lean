import MatrixSpencer.RectangularRidgeOwnerShavingDerivative
import MatrixSpencer.RectangularRidgeActualResponse

/-! The actual covariance derivative cap bounds the actual center response.
The derivative and the center Hessian refer to the same optimized mixed potential.
No independent Gram cap is assumed in this interface. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeCalculus
open RectangularRidgePotential RectangularRidgeOwnerFrame
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance ridgeCovarianceCapCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeCovarianceCapSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
attribute [local irreducible] RectangularRidgePotential.optimizer
set_option maxHeartbeats 300000

/-- A cap on the genuine supported covariance derivative implies the unchanged
rectangular response estimate, including singular physical and coefficient sources. -/
theorem owner_response_le_of_covariance_derivative_cap
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    (m : ℕ) (hm : 1 ≤ m) {θ κ L : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (hL : 0 < L) (hk : 0 < Fintype.card ι)
    (hcap : ∀ u : EuclideanSpace ℝ ι,
      u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap →
      -deriv (fun t : ℝ => regularizedOwnerPotential (H : Matrix n n ℂ) A
        (C - t • realRankOne (WithLp.ofLp u))
        (RectangularRidgeCovarianceCalculus.regularizer m θ κ)) 0 ≤
          (L / Real.sqrt (Fintype.card ι : ℝ)) * (WithLp.ofLp u ⬝ᵥ WithLp.ofLp u)) :
    realTrace (C * ownerCoefficientResponse A hA C m θ κ H) ≤
      2 * Real.sqrt (Fintype.card ι : ℝ) +
        (6 * L ^ (1 / (2 : ℝ) ^ m) / (θ * (1 / (2 : ℝ) ^ m))) *
          (Fintype.card ι : ℝ) ^ (1 - 1 / (2 : ℝ) ^ m) := by
  apply owner_response_le_of_ownedGram_cap H A hA hN hC hC1 m hm hθ hκ hL hk
  intro u hu
  have hc := hcap u hu
  rw [(hasDerivAt_ridgeOwnerPotential_supported_shave H A hA hC u hu
    m hm θ κ hθ hκ).deriv, neg_neg] at hc
  exact hc

end MatrixSpencer.RectangularRidgeCalculus
