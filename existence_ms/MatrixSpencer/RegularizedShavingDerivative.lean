import MatrixSpencer.OwnerShavingDerivative
import MatrixSpencer.RegularizedOwnerPotential

/-! Supported covariance derivatives at fixed density are independent of the regularizer. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
namespace MatrixSpencer
noncomputable section
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance regularizedShavingCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance regularizedShavingSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- No continuity or concavity assumption on R is needed: the density is fixed. -/
theorem hasDerivAt_regularizedOwnerObjective_supported_shave (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (hC : (C : Matrix ι ι ℝ).PosSemidef)
    (u : ι → ℝ) (hu : u ∈ LinearMap.range (C : Matrix ι ι ℝ).mulVecLin)
    (R : Matrix n n ℂ → ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    let B := covarianceKraus A C
    let V := krausSupportEmbedding B
    let Z := transportOptimizer (krausCompressedDensity B S) (krausCompressedSource B S)
    HasDerivAt (fun t : ℝ => regularizedOwnerObjective H A
      ((C : Matrix ι ι ℝ) - t • realRankOne u) R S)
      (-(u ⬝ᵥ (covarianceGram A S (V * Z * Vᴴ) *ᵥ u))) 0 := by
  have h := (hasDerivAt_ownerObjective_supported_shave H A hA C hC u hu 0 S hS).add_const (R S)
  simpa only [ownerObjective, regularizedOwnerObjective, mul_zero, zero_mul, add_zero] using h

end
end MatrixSpencer
