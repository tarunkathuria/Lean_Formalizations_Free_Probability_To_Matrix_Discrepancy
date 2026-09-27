import MatrixSpencer.MSManuscriptGammaInputBoundScaled
import MatrixSpencer.MSConvexGammaSmoothness

/-! Convex-solver substitution for the original numerical value calls.
All original geometric and scalar parameter definitions are retained. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexGammaInputBoundScaled
open MSManuscriptGammaInputBoundScaled MSManuscriptGammaDifference
variable [MSConvexOwnerValue.Oracle]
variable {N k d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1400000
attribute [local irreducible] ownerPotential observedOwnedGram

theorem report_accuracy [Nonempty (Fin d)]
    (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i, (A i).IsHermitian)
    {L : ℝ} (hL : 0 ≤ L) (hAn : ∀i, ‖A i‖ ≤ L) {C : Matrix (Fin k) (Fin k) ℝ}
    {R θ δ η : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (hR : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖ ≤ R) (hd : 0 < d)
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C) (hC1 : C ≤ 1) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (observedOwnedGram H A C θ-
      MSConvexGammaMatrix.report H A C θ hd δ (secondCap k d R θ δ L) η)‖ ≤ (k : ℝ)*(2*η) := by
  apply MSConvexGammaSmoothness.report_accuracy_of_floor H A hA hθ hδ
    (secondCap_nonneg ((norm_nonneg _).trans hR) hθ) hη hd hfloor
  intro u hu a ha
  apply query_second_le H A hA hL hAn hθ hδ hδ1 hR hfloor hC1 u hu
  exact ⟨ha.1,(ha.2.trans_le (min_le_left _ _)).trans (by linarith : δ/4 < δ/2)⟩

end MatrixSpencer.MSConvexGammaInputBoundScaled
