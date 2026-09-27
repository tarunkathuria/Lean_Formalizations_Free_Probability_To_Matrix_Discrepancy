import MatrixSpencer.FaithfulResponse
import MatrixSpencer.FrameTrace

/-!
# Actual observed response and the concrete force frame

The left hand side is the second derivative of the attained supremum
potential in the original physical Kraus directions.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

local instance observedResponseCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance observedResponseNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance observedResponseFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

omit [Fintype ι] [Fintype n] [DecidableEq n] in
def hermitianMatrixFamily (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian)
    (a : ι) : selfAdjoint (Matrix n n ℂ) := ⟨B a, hB a⟩

/-- Half the sum of the actual potential Hessian responses in its defining Kraus directions. -/
def krausObservedResponse (H : selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian) (θ : ℝ) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ a, fderiv ℝ (fun K => fderiv ℝ (hermitianDensityPotential B θ) K) H
    (hermitianMatrixFamily B hB a) (hermitianMatrixFamily B hB a)

/-- The actual constrained observed response is bounded by the concrete full inverse frame trace. -/
theorem faithful_observed_response_le [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) {θ : ℝ} (hθ : 0 < θ)
    (hM : (krausChannel B (densityOptimizer (H : Matrix n n ℂ) B θ)).PosDef) :
    let S := hermitianDensityOptimizer (H : Matrix n n ℂ) B θ
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    krausObservedResponse H B hB θ ≤
      realTrace (jordanForceFrame (balancedDensity S Z) (balancedKraus B Z) *
        (balancedWhitenedFull B θ S Z)⁻¹) := by
  classical
  dsimp only
  rw [krausObservedResponse, jordanForceFrame_trace_eq_half_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  apply Finset.sum_le_sum
  intro a _
  exact potential_hessian_le_whitened_inverse H (hermitianMatrixFamily B hB a) B hB hθ hM

end MatrixSpencer
