import MatrixSpencer.KSInputJointBounds

/-! Actual KS joint derivative bounds at an arbitrary cube point with a live
margin. There is no Prepared-state type or numerical-report premise. -/
open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.KSFullManuscriptJointPoint
open KSLiveCurve KSDebitPreparedMargin KSActualEnvelope KSInputJointBounds
open KSDebitHessianQueries KSDebitNumericalDrift KSJointBoundsToTaylor
variable {N d : ℕ} [Nonempty (Fin d)]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
set_option maxHeartbeats 1200000

theorem value_bound (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hθ : 0 < θ)
    (x : Fin N → ℝ) (hx : x ∈ ksCube 1) (h : Live 1 x → ℝ)
    (hmargin : ∀i : Live 1 x, δ ≤ 1-|x i|) (hdir : ∀i, |h i| ≤ 2)
    {t : ℝ} (ht : |t| ≤ δ/16) :
    ∀p ∈ Metric.ball ((t : ℂ),curveDensity v δ η θ x h t)
      (KSJointBoundParameters.radius v δ η θ),
      ‖KSComplexOwnerObjective.objective (stateCenter v δ η x)
        (fun i : Live 1 x => v i) θ (fun i => x i) h p‖ ≤
          KSJointBoundParameters.objectiveCap v δ η θ := by
  intro p hp
  have hb := KSComplexOwnerValueBound.objective_norm_le_on_ball
    (stateCenter v δ η x) (fun i : Live 1 x => v i) θ
    (fun i => x i) h t (curveDensity v δ η θ x h t)
    (KSDebitUniformFloor.uniformFloor_pos v hδ.le hη hθ)
    (curveDensity_floor v hδ hη hθ hx h hmargin hdir ht)
    (show (0 : ℝ) < δ/2 from by positivity)
    (curve_point_margin hδ x h hmargin hdir ht) hdir
    (curveDensity_norm_le v δ η θ x h t hθ)
    (curve_complexCenter_norm_le v hδ hη hx h hmargin hdir ht)
    (KSDebitUniformFloor.centerRadius_pos v hδ.le hη).le hθ.le p hp
  exact hb.trans (live_valueCap_le_objectiveCap v δ η θ x)

theorem joint_bounds (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hθ : 0 < θ)
    (x : Fin N → ℝ) (hx : x ∈ ksCube 1) (h : Live 1 x → ℝ)
    (hmargin : ∀i : Live 1 x, δ ≤ 1-|x i|) (hdir : ∀i, |h i| ≤ 2)
    {t : ℝ} (ht : |t| ≤ δ/16) :
    let F := curveObjective (stateCenter v δ η x) (stateCenter_isHermitian v δ η x)
      (fun i : Live 1 x => v i) θ (fun i => x i) h
    let q := curveBranch (stateCenter v δ η x) (stateCenter_isHermitian v δ η x)
      (fun i : Live 1 x => v i) θ (fun i => x i) h t
    secondNorm F (t,q) ≤ KSJointBoundParameters.jointCap v δ η θ ∧
    thirdNorm F (t,q) ≤ KSJointBoundParameters.jointCap v δ η θ ∧
    fourthNorm F (t,q) ≤ KSJointBoundParameters.jointCap v δ η θ := by
  let q := curveBranch (stateCenter v δ η x) (stateCenter_isHermitian v δ η x)
    (fun i : Live 1 x => v i) θ (fun i => x i) h t
  let F := KSComplexOwnerObjective.objective (stateCenter v δ η x)
    (fun i : Live 1 x => v i) θ (fun i => x i) h
  have hbase : KSComplexEnvelopeChart.base (Fin d ⊕ Fin d) +
      KSComplexEnvelopeChart.jointEmbedding (Fin d ⊕ Fin d) (t,q) =
        ((t : ℂ),curveDensity v δ η θ x h t) := by
    rw [KSComplexEnvelopeChart.base_add_jointEmbedding]
    rfl
  have hF : ContDiffOn ℂ ∞ F
      (Metric.ball (KSComplexEnvelopeChart.base (Fin d ⊕ Fin d) +
        KSComplexEnvelopeChart.jointEmbedding (Fin d ⊕ Fin d) (t,q))
        (KSJointBoundParameters.radius v δ η θ)) := by
    rw [hbase]
    exact curve_complex_contDiff v hδ hη hθ hx h hmargin hdir ht
  have hK : ∀ p ∈ Metric.ball (KSComplexEnvelopeChart.base (Fin d ⊕ Fin d) +
        KSComplexEnvelopeChart.jointEmbedding (Fin d ⊕ Fin d) (t,q))
        (KSJointBoundParameters.radius v δ η θ),
      ‖F p‖ ≤ KSJointBoundParameters.objectiveCap v δ η θ := by
    rw [hbase]
    exact value_bound v hδ hη hθ x hx h hmargin hdir ht
  have hb := KSComplexEnvelopeChart.chart_derivatives_le_common_cap (Fin d ⊕ Fin d) F
    (KSJointBoundParameters.radius_pos v hδ hη hθ)
    (KSJointBoundParameters.radius_le_one v δ η θ)
    (KSJointBoundParameters.objectiveCap_pos v hδ.le hη hθ.le).le hF hK
  exact nested_bounds_of_eventuallyEq
    (curve_objective_eventuallyEq v hδ hθ x h hmargin hdir ht) hb

end MatrixSpencer.KSFullManuscriptJointPoint
