import MatrixSpencer.MSManuscriptGammaMatrix
import MatrixSpencer.MSConvexGammaDifference

/-! Convex-solver substitution for the original numerical value calls.
All original geometric and scalar parameter definitions are retained. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexGammaMatrix
open MSManuscriptGammaMatrix MSManuscriptGammaDifference KSRayleighAccuracy MSConvexGammaDifference
variable [MSConvexOwnerValue.Oracle]
variable {N k d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1400000
attribute [local irreducible] ownerPotential observedOwnedGram

def report (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix (Fin k) (Fin k) ℝ) (θ : ℝ) (hd : 0 < d) (δ L η : ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  reconstruct (MSConvexGammaDifference.probe H A C θ hd (stepSize δ L η) (valueTolerance δ L η))

theorem report_isSymm (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix (Fin k) (Fin k) ℝ) (θ : ℝ) (hd : 0 < d) (δ L η : ℝ) :
    (report H A C θ hd δ L η).IsSymm := reconstruct_isSymm _

/-- Quantitative segment hypotheses for the actual finite-difference queries.
These remain analytic obligations until a supported-floor curvature bound is supplied. -/

theorem report_accuracy [Nonempty (Fin d)]
    (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix (Fin k) (Fin k) ℝ} (hC : C.PosSemidef)
    {θ δ L η : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (hL : 0 ≤ L) (hη : 0 < η)
    (hd : 0 < d)
    (hsegments : QuerySegments (H : Matrix (Fin d) (Fin d) ℂ) A C θ (stepSize δ L η) L) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (observedOwnedGram H A C θ-report (H : Matrix (Fin d) (Fin d) ℂ) A C θ hd δ L η)‖ ≤
        (k : ℝ)*(2*η) := by
  have hsymm : (observedOwnedGram H A C θ).IsSymm := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (observedOwnedGram_posSemidef H A hA C hθ).isHermitian.eq
  apply reconstruct_operator_error _ hsymm _ hη.le
  intro u hu
  obtain ⟨hrange,hpsd,hcurve,hcurvature⟩ := hsegments u hu
  have h := MSConvexGammaDifference.probe_accuracy H A hA hC u hrange hθ (stepSize_pos hδ hL hη)
    (valueTolerance_pos hδ hL hη) hd hpsd hcurve hcurvature
  rw [realRayleigh_eq_quadratic]
  exact h.trans (error_budget hδ hL hη)


end MatrixSpencer.MSConvexGammaMatrix
