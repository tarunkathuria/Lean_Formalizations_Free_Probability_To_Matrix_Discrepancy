import MatrixSpencer.MSManuscriptGammaDifference
import MatrixSpencer.MSConvexOwnerValue

/-! Convex-solver substitution for the original numerical value calls.
All original geometric and scalar parameter definitions are retained. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexGammaDifference
open MSManuscriptGammaDifference 
variable [MSConvexOwnerValue.Oracle]
variable {N k d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1400000
attribute [local irreducible] ownerPotential observedOwnedGram

def valueCurve (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix (Fin k) (Fin k) ℝ) (θ : ℝ) (hd : 0 < d)
    (ν : ℝ) (u : EuclideanSpace ℝ (Fin k)) (a : ℝ) : ℝ :=
  MSConvexOwnerValue.report H A (C-a • realRankOne (WithLp.ofLp u)) θ hd ν

/-- Two calls of a certified finite value routine and ordinary scalar arithmetic. -/

def probe (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix (Fin k) (Fin k) ℝ) (θ : ℝ) (hd : 0 < d)
    (s ν : ℝ) (u : EuclideanSpace ℝ (Fin k)) : ℝ :=
  negativeSlope (valueCurve (H : Matrix (Fin d) (Fin d) ℂ) A C θ hd ν u) s

theorem probe_accuracy [Nonempty (Fin d)]
    (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix (Fin k) (Fin k) ℝ} (hC : C.PosSemidef)
    (u : EuclideanSpace ℝ (Fin k))
    (hu : u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap)
    {θ s ν L : ℝ} (hθ : 0 < θ) (hs : 0 < s) (hν : 0 < ν) (hd : 0 < d)
    (hCs : (C-s • realRankOne (WithLp.ofLp u)).PosSemidef)
    (hcurve : ContDiffOn ℝ 2 (curve (H : Matrix (Fin d) (Fin d) ℂ) A C θ u) (Icc 0 s))
    (hL : ∀ a ∈ Ioo 0 s, |iteratedDeriv 2 (curve (H : Matrix (Fin d) (Fin d) ℂ) A C θ u) a| ≤ L) :
    |probe (H : Matrix (Fin d) (Fin d) ℂ) A C θ hd s ν u -
      WithLp.ofLp u ⬝ᵥ (observedOwnedGram H A C θ *ᵥ WithLp.ofLp u)| ≤ L*s/2+2*ν/s := by
  have hH : (H : Matrix (Fin d) (Fin d) ℂ).IsHermitian := H.property
  have hder : HasDerivAt (curve (H : Matrix (Fin d) (Fin d) ℂ) A C θ u)
      (-(WithLp.ofLp u ⬝ᵥ (observedOwnedGram H A C θ *ᵥ WithLp.ofLp u))) 0 :=
    hasDerivAt_ownerPotential_supported_shave H A hA hC u hu hθ
  change |negativeSlope (valueCurve (H : Matrix (Fin d) (Fin d) ℂ) A C θ hd ν u) s -
    WithLp.ofLp u ⬝ᵥ (observedOwnedGram H A C θ *ᵥ WithLp.ofLp u)| ≤ _
  refine negativeSlope_accuracy (curve (H : Matrix (Fin d) (Fin d) ℂ) A C θ u) (valueCurve (H : Matrix (Fin d) (Fin d) ℂ) A C θ hd ν u) (q := WithLp.ofLp u ⬝ᵥ (observedOwnedGram H A C θ *ᵥ WithLp.ofLp u)) hs hcurve hder hL ?_ ?_
  · have hh := MSConvexOwnerValue.report_accuracy (H : Matrix (Fin d) (Fin d) ℂ) hH
      A hA hC hθ hν hd
    simpa only [valueCurve, curve, zero_smul, sub_zero] using hh
  · exact MSConvexOwnerValue.report_accuracy (H : Matrix (Fin d) (Fin d) ℂ) hH
      A hA hCs hθ hν hd

end MatrixSpencer.MSConvexGammaDifference
