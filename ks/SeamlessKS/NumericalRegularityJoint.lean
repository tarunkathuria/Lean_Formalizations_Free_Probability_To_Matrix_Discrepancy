import SeamlessKS.NumericalRegularityBounds
import MatrixSpencer.KSInputJointBounds

/-! Cauchy bounds for the actual new joint density objective, transferred
through the full trace-zero Frobenius chart. -/
open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace SeamlessKS
namespace NumericalRegularityJoint
open MatrixSpencer
open KSFrobeniusTangent
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
set_option maxHeartbeats 1400000

def curveC (ζ : ℝ) (x h : ι → ℝ) (t : ℝ) : selfAdjoint (Matrix (ι × Fin 4) (ι × Fin 4) ℝ) :=
  KSDebitSmoothness.coefficientCovarianceCLM (fun i => Source.weight 64 ζ (x i + t * h i))

def realObjective (ζ : ℝ) (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) (θ : ℝ) (x h : ι → ℝ) : ℝ × Coordinates (n ⊕ n) → ℝ :=
  KSActualEnvelope.objective (KSSpinSource.family (KSSpinLocalState.atoms v)) θ
    (KSActualEnvelope.curveH M hM v h) (curveC ζ x h)

def valueCap (v : ι → n → ℂ) (R θ : ℝ) : ℝ :=
  KSComplexObjectiveBound.valueCap (Fintype.card (n ⊕ n))
    (R + 2 * KSComplexPolynomialBounds.slopeBudget v) 2
    (NumericalRegularityBounds.sourceBudget v) θ

def jointCap (v : ι → n → ℂ) (μ ρ ζ R θ : ℝ) : ℝ :=
  valueCap v R θ * (10 / NumericalRegularity.radius μ ρ ζ) ^ 4

theorem valueCap_nonneg (v : ι → n → ℂ) {R θ : ℝ} (hR : 0 ≤ R) (hθ : 0 ≤ θ) :
    0 ≤ valueCap v R θ :=
  KSComplexObjectiveBound.valueCap_nonneg _ (by have := (KSComplexPolynomialBounds.slopeBudget_pos v).le; positivity)
    (by norm_num) hθ

theorem jointCap_nonneg (v : ι → n → ℂ) (μ ρ ζ : ℝ) {R θ : ℝ} (hR : 0 ≤ R) (hθ : 0 ≤ θ) :
    0 ≤ jointCap v μ ρ ζ R θ := mul_nonneg (valueCap_nonneg v hR hθ) (by positivity)

theorem contDiff_curveC {ζ : ℝ} (hζ : 0 < ζ) (x h : ι → ℝ) :
    ContDiff ℝ ∞ (curveC ζ x h) := by
  have hw : ContDiff ℝ ∞ (fun t : ℝ => fun i => Source.weight 64 ζ (x i + t * h i)) := by
    apply contDiff_pi.mpr
    intro i
    exact (Source.weight_contDiff hζ 64 ∞).comp
      (contDiff_const.add (contDiff_id.mul contDiff_const))
  exact (KSDebitSmoothness.coefficientCovarianceCLM (ι := ι)).contDiff.comp hw

theorem objective_eventuallyEq {ζ : ℝ} (hζ : 0 < ζ)
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) (θ : ℝ) (x h : ι → ℝ) (t : ℝ)
    (q : Coordinates (n ⊕ n))
    (hS : (chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (hx : ∀ i, |x i + t * h i| < 1) :
    (fun p : ℝ × Coordinates (n ⊕ n) =>
      (NumericalRegularityObjective.objective ζ M v θ x h
        ((p.1 : ℂ), (chart (n ⊕ n) p.2 : Matrix (n ⊕ n) (n ⊕ n) ℂ))).re) =ᶠ[𝓝 (t,q)]
      realObjective ζ M hM v θ x h := by
  have hchart : ContinuousAt (fun p : ℝ × Coordinates (n ⊕ n) => chart (n ⊕ n) p.2) (t,q) :=
    ((contDiff_chart (n ⊕ n)).continuous.comp continuous_snd).continuousAt
  have hd := hchart.eventually (eventually_posDef_of_posDef (chart (n ⊕ n) q) hS)
  have ho : ∀ i : ι, ∀ᶠ p : ℝ × Coordinates (n ⊕ n) in 𝓝 (t,q),
      0 < Source.weight 64 ζ (x i + p.1 * h i) := by
    intro i
    have hc : Continuous (fun p : ℝ × Coordinates (n ⊕ n) => Source.weight 64 ζ (x i + p.1 * h i)) :=
      (Source.weight_continuous 64 ζ).comp (continuous_const.add (continuous_fst.mul continuous_const))
    exact hc.continuousAt.eventually (eventually_gt_nhds (Source.weight_pos (by norm_num) (hx i)))
  filter_upwards [hd, (Filter.eventually_all).mpr ho] with p hp howners
  rw [NumericalRegularityObjective.objective_real hζ M hM v θ x h p.1 hp howners, Complex.ofReal_re]
  rfl

/-- Joint second-through-fourth derivatives are bounded by an explicit cap.
The input assumptions are state geometry and matrix norms, not derivative
or optimizer-response assumptions. -/
theorem joint_bounds {ζ μ ρ R θ : ℝ} (hζ : 0 < ζ) (hζone : ζ ≤ 1)
    (hμ : 0 < μ) (hρ : 0 < ρ) (hR : 0 ≤ R) (hθ : 0 ≤ θ)
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) (x h : ι → ℝ) (t : ℝ) (q : Coordinates (n ⊕ n))
    (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ (chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hSnorm : ‖(chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ)‖ ≤ 1)
    (hx : ∀ i, |x i + t * h i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (hcenter : ‖NumericalRegularityObjective.complexCenter M v h (t : ℂ)‖ ≤ R) :
    KSActualEnvelope.secondNorm (realObjective ζ M hM v θ x h) (t,q) ≤ jointCap v μ ρ ζ R θ ∧
    KSActualEnvelope.thirdNorm (realObjective ζ M hM v θ x h) (t,q) ≤ jointCap v μ ρ ζ R θ ∧
    KSActualEnvelope.fourthNorm (realObjective ζ M hM v θ x h) (t,q) ≤ jointCap v μ ρ ζ R θ := by
  let F := NumericalRegularityObjective.objective ζ M v θ x h
  have hbase : KSComplexEnvelopeChart.base (n ⊕ n) + KSComplexEnvelopeChart.jointEmbedding (n ⊕ n) (t,q) =
      ((t : ℂ), (chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ)) :=
    KSComplexEnvelopeChart.base_add_jointEmbedding _ _
  have hF : ContDiffOn ℂ ∞ F
      (Metric.ball (KSComplexEnvelopeChart.base (n ⊕ n) + KSComplexEnvelopeChart.jointEmbedding (n ⊕ n) (t,q))
        (NumericalRegularity.radius μ ρ ζ)) := by
    rw [hbase]
    exact NumericalRegularityObjective.contDiffOn_objective hζ M v θ x h t _ hμ hfloor hρ hx hh
  have hbound : ∀ p ∈ Metric.ball
      (KSComplexEnvelopeChart.base (n ⊕ n) + KSComplexEnvelopeChart.jointEmbedding (n ⊕ n) (t,q))
        (NumericalRegularity.radius μ ρ ζ), ‖F p‖ ≤ valueCap v R θ := by
    rw [hbase]
    exact NumericalRegularityBounds.objective_norm_le_on_ball hζ hζone M v θ x h t _
      hμ hfloor hρ hx hh hSnorm hcenter hR hθ
  have hb := KSComplexEnvelopeChart.chart_derivatives_le_common_cap (n ⊕ n) F
    (NumericalRegularity.radius_pos hμ hρ hζ)
    (show NumericalRegularity.radius μ ρ ζ ≤ 1 by have := NumericalRegularity.radius_le_one μ ρ ζ; linarith)
    (valueCap_nonneg v hR hθ) hF hbound
  exact KSInputJointBounds.nested_bounds_of_eventuallyEq
    (objective_eventuallyEq hζ M hM v θ x h t q
      (KSComplexSpinDomain.posDef_of_floor hμ hfloor) (fun i => by have hi := hx i; linarith)) hb

end NumericalRegularityJoint
end SeamlessKS
