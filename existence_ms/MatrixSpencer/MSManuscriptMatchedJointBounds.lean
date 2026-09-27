import MatrixSpencer.MSManuscriptAffineJointBounds
import MatrixSpencer.MSManuscriptMatchedValueBound

/-!
# Actual joint second through fourth bounds on matched movement

The original real objective is evaluated at H+tB, C−t²Q in its full density
chart. Its explicit Cauchy cap is derived from the actual complex polynomial
extension, including arbitrary finite input scale L. It is not an affine
replacement, a source-gap assumption, or a supplied derivative certificate.
-/
open Matrix Set Filter Metric
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.MSManuscriptMatchedJointBounds
open KSFrobeniusTangent
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
local instance : NormedAddCommGroup (Coordinates n) := inferInstance
local instance : NormedSpace ℝ (Coordinates n) := inferInstance
local instance : NormedAddCommGroup (ℝ × Coordinates n) := inferInstance
local instance : NormedSpace ℝ (ℝ × Coordinates n) := inferInstance
set_option maxHeartbeats 1000000

abbrev RealSpace (n : Type*) [Fintype n] [DecidableEq n] := ℝ × Coordinates n

def center (H B : selfAdjoint (Matrix n n ℂ)) (t : ℝ) : selfAdjoint (Matrix n n ℂ) := H+t•B

def covariance (C Q : selfAdjoint (Matrix ι ι ℝ)) (t : ℝ) : selfAdjoint (Matrix ι ι ℝ) := C-t^2•Q

theorem contDiff_center (H B : selfAdjoint (Matrix n n ℂ)) : ContDiff ℝ ∞ (center H B) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

theorem contDiff_covariance (C Q : selfAdjoint (Matrix ι ι ℝ)) : ContDiff ℝ ∞ (covariance C Q) :=
  contDiff_const.sub ((contDiff_id.pow 2).smul contDiff_const)

theorem center_real (H B : selfAdjoint (Matrix n n ℂ)) (t : ℝ) :
    MSManuscriptMatchedComplex.center (H : Matrix n n ℂ) B (t:ℂ) = (center H B t : Matrix n n ℂ) := by
  ext i j
  simp only [MSManuscriptMatchedComplex.center,center,Matrix.add_apply,Matrix.smul_apply]
  rfl

def jointCap (ι n : Type*) [Fintype ι] [Fintype n] (R b θ γ μ L : ℝ) : ℝ :=
  MSManuscriptComplexValueBoundScaled.valueCap ι n (R+b) θ L*(10/MSManuscriptMatchedComplex.radius γ μ)^4

theorem eventuallyEq_objective (H B : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian) (θ : ℝ)
    (C Q : selfAdjoint (Matrix ι ι ℝ)) {p : RealSpace n}
    (hC : (covariance C Q p.1 : Matrix ι ι ℝ).PosDef)
    (hS : (chart n p.2 : Matrix n n ℂ).PosDef) :
    (fun z : RealSpace n => (MSManuscriptMatchedComplex.objective H B A C Q θ
      ((z.1:ℂ),(chart n z.2 : Matrix n n ℂ))).re) =ᶠ[𝓝 p]
      KSActualEnvelope.objective A θ (center H B) (covariance C Q) := by
  have hc : ContinuousAt (fun z : RealSpace n => covariance C Q z.1) p :=
    (contDiff_covariance C Q).continuous.continuousAt.comp continuousAt_fst
  have hs : ContinuousAt (fun z : RealSpace n => chart n z.2) p :=
    (contDiff_chart n).continuous.continuousAt.comp continuousAt_snd
  filter_upwards [hc.eventually (eventually_real_posDef_of_posDef (covariance C Q p.1) hC),
    hs.eventually (eventually_posDef_of_posDef (chart n p.2) hS)] with z hzC hzS
  have hH : (H : Matrix n n ℂ).IsHermitian := H.property
  have hB : (B : Matrix n n ℂ).IsHermitian := B.property
  rw [MSManuscriptMatchedComplex.objective_real (H : Matrix n n ℂ) B hH hB A hA C Q θ z.1 hzC hzS]
  rfl

/-- Primitive floors and matrix norm bounds imply the actual derivative cap. -/
theorem iterated_bounds (H B : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian) {L : ℝ}
    (hL : 0 ≤ L) (hAnorm : ∀i, ‖A i‖ ≤ L)
    (C Q : selfAdjoint (Matrix ι ι ℝ)) (hQ : ‖realMatrixEmbedding (Q : Matrix ι ι ℝ)‖ ≤ 1)
    {θ R b γ μ : ℝ} (hθ : 0 ≤ θ) (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hB : ‖(B : Matrix n n ℂ)‖ ≤ b)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1) {p : RealSpace n}
    (ht : |p.1| ≤ 1) (hH : ‖(center H B p.1 : Matrix n n ℂ)‖ ≤ R)
    (hC : γ•(1 : Matrix ι ι ℝ) ≤ (covariance C Q p.1 : Matrix ι ι ℝ))
    (hC1 : (covariance C Q p.1 : Matrix ι ι ℝ) ≤ 1)
    (hS : μ•(1 : Matrix n n ℂ) ≤ (chart n p.2 : Matrix n n ℂ))
    (hS1 : ‖(chart n p.2 : Matrix n n ℂ)‖ ≤ 1) :
    ∀ k : ℕ, 2 ≤ k → k ≤ 4 →
      ‖iteratedFDeriv ℝ k (KSActualEnvelope.objective A θ (center H B) (covariance C Q)) p‖ ≤
        jointCap ι n R b θ γ μ L := by
  have hCp : (covariance C Q p.1 : Matrix ι ι ℝ).PosDef := by
    simpa only [add_sub_cancel] using (Matrix.PosDef.one.smul hγ).add_posSemidef (Matrix.le_iff.mp hC)
  have hSp : (chart n p.2 : Matrix n n ℂ).PosDef := by
    simpa only [add_sub_cancel] using (Matrix.PosDef.one.smul hμ).add_posSemidef (Matrix.le_iff.mp hS)
  have hcont := MSManuscriptMatchedComplex.contDiffOn_objective (H : Matrix n n ℂ) B A hA C Q hQ θ
    ht hγ hγ1 hμ hμ1 hC hS
  have hH' : ‖MSManuscriptMatchedComplex.center (H : Matrix n n ℂ) B (p.1:ℂ)‖ ≤ R := by
    rwa [center_real]
  have hbound := MSManuscriptMatchedValueBound.objective_norm_le_on_ball (H : Matrix n n ℂ) B A hA
    hL hAnorm C Q hQ ht hθ hR hb hH' hB hγ hγ1 hμ hμ1 hC hC1 hS hS1
  have hh := KSComplexEnvelopeChart.chart_derivatives_le_common_cap n
    (MSManuscriptMatchedComplex.objective (H : Matrix n n ℂ) B A C Q θ) (x := p)
    (MSManuscriptMatchedComplex.radius_pos hγ hμ)
    (MSManuscriptMatchedComplex.radius_le_one hγ hγ1 hμ hμ1)
    (MSManuscriptComplexValueBoundScaled.valueCap_nonneg (ι := ι) (n := n) (L := L) (add_nonneg hR hb) hθ)
    (by simpa only [KSComplexEnvelopeChart.base_add_jointEmbedding] using hcont)
    (by simpa only [KSComplexEnvelopeChart.base_add_jointEmbedding] using hbound)
  have he := eventuallyEq_objective H B A hA θ C Q hCp hSp
  intro k hk2 hk4
  rw [← (he.iteratedFDeriv ℝ k).self_of_nhds]
  exact hh k hk2 hk4

theorem joint_bounds (H B : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian) {L : ℝ}
    (hL : 0 ≤ L) (hAnorm : ∀i, ‖A i‖ ≤ L)
    (C Q : selfAdjoint (Matrix ι ι ℝ)) (hQ : ‖realMatrixEmbedding (Q : Matrix ι ι ℝ)‖ ≤ 1)
    {θ R b γ μ : ℝ} (hθ : 0 ≤ θ) (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hB : ‖(B : Matrix n n ℂ)‖ ≤ b)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1) {p : RealSpace n}
    (ht : |p.1| ≤ 1) (hH : ‖(center H B p.1 : Matrix n n ℂ)‖ ≤ R)
    (hC : γ•(1 : Matrix ι ι ℝ) ≤ (covariance C Q p.1 : Matrix ι ι ℝ))
    (hC1 : (covariance C Q p.1 : Matrix ι ι ℝ) ≤ 1)
    (hS : μ•(1 : Matrix n n ℂ) ≤ (chart n p.2 : Matrix n n ℂ))
    (hS1 : ‖(chart n p.2 : Matrix n n ℂ)‖ ≤ 1) :
    let F := KSActualEnvelope.objective A θ (center H B) (covariance C Q)
    KSActualEnvelope.secondNorm F p ≤ jointCap ι n R b θ γ μ L ∧
    KSActualEnvelope.thirdNorm F p ≤ jointCap ι n R b θ γ μ L ∧
    KSActualEnvelope.fourthNorm F p ≤ jointCap ι n R b θ γ μ L :=
  MSManuscriptAffineJointBounds.nested_bounds
    (iterated_bounds H B A hA hL hAnorm C Q hQ hθ hR hb hB hγ hγ1 hμ hμ1 ht hH hC hC1 hS hS1)

end MatrixSpencer.MSManuscriptMatchedJointBounds
