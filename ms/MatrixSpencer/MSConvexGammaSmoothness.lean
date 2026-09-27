import MatrixSpencer.MSManuscriptGammaSmoothness
import MatrixSpencer.MSConvexGammaMatrix

/-! Convex-solver substitution for the original numerical value calls.
All original geometric and scalar parameter definitions are retained. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexGammaSmoothness
open MSManuscriptGammaSmoothness MSManuscriptGammaDifference MSManuscriptGammaMatrix
variable [MSConvexOwnerValue.Oracle]
variable {N k d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1400000
attribute [local irreducible] ownerPotential observedOwnedGram

theorem report_accuracy_of_floor [Nonempty (Fin d)]
    (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix (Fin k) (Fin k) ℝ} {θ δ L η : ℝ}
    (hθ : 0 < θ) (hδ : 0 < δ) (hL : 0 ≤ L) (hη : 0 < η) (hd : 0 < d)
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C)
    (hsecond : ∀ u : EuclideanSpace ℝ (Fin k), ‖u‖ = 1 →
      ∀ a ∈ Ioo 0 (stepSize δ L η),
        |iteratedDeriv 2 (curve (H : Matrix (Fin d) (Fin d) ℂ) A C θ u) a| ≤ L) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (observedOwnedGram H A C θ-MSConvexGammaMatrix.report (H : Matrix (Fin d) (Fin d) ℂ) A C θ hd δ L η)‖ ≤
        (k : ℝ)*(2*η) :=
  MSConvexGammaMatrix.report_accuracy H A hA (posDef_of_floor hδ hfloor).posSemidef hθ hδ hL hη hd
    (querySegments_of_second_bound (H : Matrix (Fin d) (Fin d) ℂ) A hA hθ hδ hL hη hfloor hsecond)

end MatrixSpencer.MSConvexGammaSmoothness
