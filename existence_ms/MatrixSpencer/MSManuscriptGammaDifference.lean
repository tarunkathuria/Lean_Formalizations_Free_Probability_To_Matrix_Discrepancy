import MatrixSpencer.KSNumericalOwnerPotential
import MatrixSpencer.OwnerShavingDerivative
import MatrixSpencer.KSFirstDifference

/-!
# Actual one-sided covariance derivative queries

The numerical slope queries the actual owner-potential evaluator at C and
C-s uuᵀ. The derivative at zero is identified with the existing observed
owned Gram matrix. The remaining quantitative premise is a second derivative
bound on this covariance segment, not an assumed value-oracle accuracy or
Taylor remainder.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000
namespace MatrixSpencer.MSManuscriptGammaDifference
attribute [local irreducible] ownerPotential observedOwnedGram KSNumericalOwnerPotential.report
variable {k d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}

def negativeSlope (r : ℝ → ℝ) (s : ℝ) : ℝ := (r 0-r s)/s

theorem negativeSlope_accuracy (f r : ℝ → ℝ) {s L ν q : ℝ} (hs : 0 < s)
    (hf : ContDiffOn ℝ 2 f (Icc 0 s)) (hd : HasDerivAt f (-q) 0)
    (hL : ∀ u ∈ Ioo 0 s, |iteratedDeriv 2 f u| ≤ L)
    (hr0 : |r 0-f 0| ≤ ν) (hrs : |r s-f s| ≤ ν) :
    |negativeSlope r s-q| ≤ L*s/2+2*ν/s := by
  have ht := KSFirstDifference.positive_remainder f hs hf hd.differentiableAt hL
  rw [hd.deriv] at ht
  rcases abs_le.mp ht with ⟨htl,htu⟩
  rcases abs_le.mp hr0 with ⟨h0l,h0u⟩
  rcases abs_le.mp hrs with ⟨hsl,hsu⟩
  have hn : |r 0-r s-s*q| ≤ L*s^2/2+2*ν := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have he : negativeSlope r s-q = (r 0-r s-s*q)/s := by
    unfold negativeSlope
    field_simp
  rw [he, abs_div, abs_of_pos hs]
  calc
    _ ≤ (L*s^2/2+2*ν)/s := div_le_div_of_nonneg_right hn hs.le
    _ = L*s/2+2*ν/s := by field_simp

def curve (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix (Fin k) (Fin k) ℝ) (θ : ℝ) (u : EuclideanSpace ℝ (Fin k)) (a : ℝ) : ℝ :=
  ownerPotential H A (C-a • realRankOne (WithLp.ofLp u)) θ

def valueCurve (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix (Fin k) (Fin k) ℝ) (θ : ℝ) (hd : 0 < d)
    (ν : ℝ) (u : EuclideanSpace ℝ (Fin k)) (a : ℝ) : ℝ :=
  KSNumericalOwnerPotential.report H A (C-a • realRankOne (WithLp.ofLp u)) θ hd ν

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
  · have hh := KSNumericalOwnerPotential.report_accuracy (H : Matrix (Fin d) (Fin d) ℂ) hH
      A hA hC hθ hν hd
    simpa only [valueCurve, curve, zero_smul, sub_zero] using hh
  · exact KSNumericalOwnerPotential.report_accuracy (H : Matrix (Fin d) (Fin d) ℂ) hH
      A hA hCs hθ hν hd

def stepSize (δ L η : ℝ) : ℝ := min (δ/4) (η/(L+1))
def valueTolerance (δ L η : ℝ) : ℝ := η * stepSize δ L η / 4

theorem stepSize_pos {δ L η : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L) (hη : 0 < η) :
    0 < stepSize δ L η := by unfold stepSize; positivity

theorem valueTolerance_pos {δ L η : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L) (hη : 0 < η) :
    0 < valueTolerance δ L η := by
  unfold valueTolerance
  exact div_pos (mul_pos hη (stepSize_pos hδ hL hη)) (by norm_num)

theorem error_budget {δ L η : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L) (hη : 0 < η) :
    L*stepSize δ L η/2 + 2*valueTolerance δ L η/stepSize δ L η ≤ η := by
  have hs := stepSize_pos hδ hL hη
  have hb : stepSize δ L η ≤ η/(L+1) := min_le_right _ _
  have hmul : L*stepSize δ L η ≤ η := by
    have hden : 0 < L+1 := by linarith
    have hh := (le_div_iff₀ hden).mp hb
    nlinarith
  have he : 2*valueTolerance δ L η/stepSize δ L η = η/2 := by
    unfold valueTolerance
    field_simp
    ring
  rw [he]
  linarith

end MatrixSpencer.MSManuscriptGammaDifference
