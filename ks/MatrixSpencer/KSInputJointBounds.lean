import MatrixSpencer.KSJointBoundsToTaylor
import MatrixSpencer.KSJointBoundParameters
import MatrixSpencer.KSComplexEnvelopeChart
import MatrixSpencer.KSComplexOwnerValueBound

/-!
# Input-derived bounds for the actual joint KS objective

The actual numerical preparation margin and canonical optimizer supply every
geometric and density hypothesis of the concrete complex extension. Its
input-entry value bound gives a Cauchy estimate, transferred exactly to the
original real joint objective. The final theorem has no derivative, Taylor,
extension, optimizer, or value-report hypothesis.
-/

open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.KSInputJointBounds
open KSLiveCurve KSDebitPreparedMargin KSActualEnvelope KSJointBoundsToTaylor
open KSDebitHessianQueries KSDebitNumericalDrift
variable {N d : ℕ} [Nonempty (Fin d)]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

/-- The canonical density at the actual live-curve point, in the full trace-zero chart. -/
def curveDensity (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (x : Fin N → ℝ)
    (h : Live 1 x → ℝ) (t : ℝ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  KSFrobeniusTangent.chart (Fin d ⊕ Fin d)
    (curveBranch (stateCenter v δ η x) (stateCenter_isHermitian v δ η x)
      (fun i : Live 1 x => v i) θ (fun i => x i) h t)

/-- A half-margin survives everywhere on the closed interval needed by the Cauchy estimate. -/
theorem curve_point_margin {δ : ℝ} (hδ : 0 < δ) (x : Fin N → ℝ)
    (h : Live 1 x → ℝ) (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|)
    (hdir : ∀ i, |h i| ≤ 2) {t : ℝ} (ht : |t| ≤ δ / 16)
    (i : Live 1 x) : |x i + t * h i| ≤ 1 - δ / 2 := by
  have hm := mul_le_mul ht (hdir i) (abs_nonneg _) (by positivity : 0 ≤ δ / 16)
  rw [← abs_mul] at hm
  have ha := abs_add_le (x i) (t * h i)
  linarith [hmargin i]

theorem curve_point_cube {δ : ℝ} (hδ : 0 < δ) {x : Fin N → ℝ}
    (hx : x ∈ ksCube 1) (h : Live 1 x → ℝ)
    (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|) (hdir : ∀ i, |h i| ≤ 2)
    {t : ℝ} (ht : |t| ≤ δ / 16) : path 1 x h t ∈ ksCube 1 :=
  path_mem_cube_on_domain hδ hx h hmargin hdir (radius_mem_curveDomain hδ ht)

/-- The whole original input supplies a positive floor for the live-curve optimizer. -/
theorem curveDensity_floor (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hθ : 0 < θ) {x : Fin N → ℝ}
    (hx : x ∈ ksCube 1) (h : Live 1 x → ℝ)
    (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|) (hdir : ∀ i, |h i| ≤ 2)
    {t : ℝ} (ht : |t| ≤ δ / 16) :
    KSDebitUniformFloor.uniformFloor v δ η θ •
      (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ) ≤ curveDensity v δ η θ x h t := by
  unfold curveDensity curveBranch
  rw [chart_branch]
  exact KSDebitUniformFloor.actual_live_curve_optimizer_floor v hδ.le hη hθ x h t
    (curve_point_cube hδ hx h hmargin hdir ht)

/-- The exact optimizer is a density matrix, hence has operator norm at most one. -/
theorem curveDensity_norm_le (v : Fin N → Fin d → ℂ) (δ η θ : ℝ)
    (x : Fin N → ℝ) (h : Live 1 x → ℝ) (t : ℝ) (hθ : 0 < θ) :
    ‖curveDensity v δ η θ x h t‖ ≤ 1 := by
  apply density_norm_le_one
  unfold curveDensity curveBranch
  rw [chart_branch]
  exact ⟨(hermitianDensityOptimizer_posDef _ _ hθ).posSemidef,
    hermitianDensityOptimizer_trace _ _ θ⟩

/-- The center at the curve point uses the original fixed debit. -/
theorem curveH_eq_path_center (v : Fin N → Fin d → ℂ) (δ η : ℝ)
    (x : Fin N → ℝ) (h : Live 1 x → ℝ) (t : ℝ) :
    (curveH (stateCenter v δ η x) (stateCenter_isHermitian v δ η x)
      (fun i : Live 1 x => v i) h t : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ) =
      KSDebitCenter.center (KSPotentialModels.center (fun i => KSRankOne.atom (v i)) (path 1 x h t))
        (KSDebitBudget.debit (fun i => KSRankOne.atom (v i)) δ η x) := by
  rw [KSDebitPreparedCurvature.center_path_fixed_debit, sum_extend_smul]
  rfl

theorem curveH_norm_le (v : Fin N → Fin d → ℂ) {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (h : Live 1 x → ℝ) (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|)
    (hdir : ∀ i, |h i| ≤ 2) {t : ℝ} (ht : |t| ≤ δ / 16) :
    ‖(curveH (stateCenter v δ η x) (stateCenter_isHermitian v δ η x)
      (fun i : Live 1 x => v i) h t : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ)‖ ≤
      KSDebitUniformFloor.centerRadius v δ η := by
  rw [curveH_eq_path_center]
  exact KSDebitUniformFloor.fixed_center_norm v hδ.le hη
    (KSDebitBudget.debit_posSemidef _ (fun i => KSRankOne.atom_posSemidef (v i)) hδ.le hη x)
    (KSDebitUniformFloor.debit_le_scalar v hδ.le hη x)
    (curve_point_cube hδ hx h hmargin hdir ht)

/-- The complex affine center at a real query point has the same input bound. -/
theorem curve_complexCenter_norm_le (v : Fin N → Fin d → ℂ) {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (h : Live 1 x → ℝ) (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|)
    (hdir : ∀ i, |h i| ≤ 2) {t : ℝ} (ht : |t| ≤ δ / 16) :
    ‖KSComplexOwnerObjective.complexCenter (stateCenter v δ η x)
      (fun i : Live 1 x => v i) h (t : ℂ)‖ ≤ KSDebitUniformFloor.centerRadius v δ η := by
  rw [KSComplexOwnerObjective.complexCenter_real]
  exact curveH_norm_le v hδ hη hx h hmargin hdir ht

/-- Strict positivity is inherited from the actual canonical optimizer. -/
theorem curveDensity_posDef (v : Fin N → Fin d → ℂ) (δ η : ℝ) {θ : ℝ}
    (hθ : 0 < θ) (x : Fin N → ℝ) (h : Live 1 x → ℝ) (t : ℝ) :
    (curveDensity v δ η θ x h t).PosDef :=
  branch_posDef _ hθ _ _ t

/-- Around every point of the closed query interval, real chart densities and
all actual live owners remain strictly positive. -/
theorem eventually_curve_chart_positive (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (hθ : 0 < θ) (x : Fin N → ℝ) (h : Live 1 x → ℝ)
    (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|) (hdir : ∀ i, |h i| ≤ 2)
    {t : ℝ} (ht : |t| ≤ δ / 16) :
    ∀ᶠ p : ℝ × KSFrobeniusTangent.Coordinates (Fin d ⊕ Fin d) in
      𝓝 (t, curveBranch (stateCenter v δ η x) (stateCenter_isHermitian v δ η x)
        (fun i : Live 1 x => v i) θ (fun i => x i) h t),
      (KSFrobeniusTangent.chart (Fin d ⊕ Fin d) p.2 :
        Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ).PosDef ∧
      ∀ i : Live 1 x, 0 < (64 : ℝ) * (1 - (x i + p.1 * h i)^2) := by
  let q := curveBranch (stateCenter v δ η x) (stateCenter_isHermitian v δ η x)
    (fun i : Live 1 x => v i) θ (fun i => x i) h t
  have hq : (KSFrobeniusTangent.chart (Fin d ⊕ Fin d) q :
      Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ).PosDef :=
    curveDensity_posDef v δ η hθ x h t
  have hchart : ContinuousAt (fun p : ℝ × KSFrobeniusTangent.Coordinates (Fin d ⊕ Fin d) =>
      KSFrobeniusTangent.chart (Fin d ⊕ Fin d) p.2) (t,q) :=
    ((KSFrobeniusTangent.contDiff_chart (Fin d ⊕ Fin d)).continuous.comp continuous_snd).continuousAt
  have hd := hchart.eventually (eventually_posDef_of_posDef
    (KSFrobeniusTangent.chart (Fin d ⊕ Fin d) q) hq)
  have ho : ∀ i : Live 1 x, ∀ᶠ p : ℝ × KSFrobeniusTangent.Coordinates (Fin d ⊕ Fin d)
      in 𝓝 (t,q), 0 < (64 : ℝ) * (1 - (x i + p.1 * h i)^2) := by
    intro i
    have hi := curve_point_margin hδ x h hmargin hdir ht i
    have habs : |x i + t * h i| < 1 := by linarith
    have hpos : 0 < (64 : ℝ) * (1 - (x i + t * h i)^2) := by
      have hs := (sq_lt_one_iff_abs_lt_one _).mpr habs
      nlinarith
    have hc : Continuous (fun p : ℝ × KSFrobeniusTangent.Coordinates (Fin d ⊕ Fin d) =>
        (64 : ℝ) * (1 - (x i + p.1 * h i)^2)) := by fun_prop
    exact hc.continuousAt.eventually (eventually_gt_nhds hpos)
  filter_upwards [hd, (Filter.eventually_all).mpr ho] with p hp howners
  exact ⟨hp,howners⟩

/-- The actual real joint objective agrees locally with the concrete complex
extension, including all density directions in the Frobenius chart. -/
theorem curve_objective_eventuallyEq (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (hθ : 0 < θ) (x : Fin N → ℝ) (h : Live 1 x → ℝ)
    (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|) (hdir : ∀ i, |h i| ≤ 2)
    {t : ℝ} (ht : |t| ≤ δ / 16) :
    (fun p : ℝ × KSFrobeniusTangent.Coordinates (Fin d ⊕ Fin d) =>
      (KSComplexOwnerObjective.objective (stateCenter v δ η x) (fun i : Live 1 x => v i)
        θ (fun i => x i) h ((p.1 : ℂ),
          (KSFrobeniusTangent.chart (Fin d ⊕ Fin d) p.2 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ))).re) =ᶠ[
      𝓝 (t,curveBranch (stateCenter v δ η x) (stateCenter_isHermitian v δ η x)
        (fun i : Live 1 x => v i) θ (fun i => x i) h t)]
      curveObjective (stateCenter v δ η x) (stateCenter_isHermitian v δ η x)
        (fun i : Live 1 x => v i) θ (fun i => x i) h := by
  filter_upwards [eventually_curve_chart_positive v (η := η) hδ hθ x h hmargin hdir ht]
    with p hp
  exact KSComplexOwnerObjective.objective_real_eq_curveObjective
    (stateCenter v δ η x) (stateCenter_isHermitian v δ η x)
    (fun i : Live 1 x => v i) θ (fun i => x i) h p.1 p.2 hp.1 hp.2

/-- The actual complex objective is smooth on the explicit input-derived ball
around every live-curve optimizer point. -/
theorem curve_complex_contDiff (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hθ : 0 < θ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (h : Live 1 x → ℝ) (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|)
    (hdir : ∀ i, |h i| ≤ 2) {t : ℝ} (ht : |t| ≤ δ / 16) :
    ContDiffOn ℂ ∞
      (KSComplexOwnerObjective.objective (stateCenter v δ η x) (fun i : Live 1 x => v i)
        θ (fun i => x i) h)
      (Metric.ball ((t : ℂ),curveDensity v δ η θ x h t) (KSJointBoundParameters.radius v δ η θ)) :=
  KSComplexOwnerObjective.contDiffOn_objective _ _ θ _ h t _
    (KSDebitUniformFloor.uniformFloor_pos v hδ.le hη hθ)
    (curveDensity_floor v hδ hη hθ hx h hmargin hdir ht) (by positivity)
    (curve_point_margin hδ x h hmargin hdir ht) hdir

section NormTransfer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAddCommGroup ((ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ ((ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := inferInstance

omit [Nonempty (Fin d)] in
/-- Exact transfer from multilinear Cauchy bounds to the nested derivative norms
used by the envelope theorem. Local agreement is enough. -/
theorem nested_bounds_of_eventuallyEq {F G : (ℝ × E) → ℝ} {p : ℝ × E} {B : ℝ}
    (he : F =ᶠ[𝓝 p] G)
    (hbound : ∀ k : ℕ, 2 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k F p‖ ≤ B) :
    secondNorm G p ≤ B ∧ thirdNorm G p ≤ B ∧ fourthNorm G p ≤ B := by
  have hb (k : ℕ) (hk2 : 2 ≤ k) (hk4 : k ≤ 4) : ‖iteratedFDeriv ℝ k G p‖ ≤ B := by
    rw [← (he.iteratedFDeriv ℝ k).self_of_nhds]
    exact hbound k hk2 hk4
  have h2 := hb 2 (by norm_num) (by norm_num)
  have h3 := hb 3 (by norm_num) (by norm_num)
  have h4 := hb 4 (by norm_num) (by norm_num)
  rw [← norm_iteratedFDeriv_fderiv (n := 1), ← norm_iteratedFDeriv_fderiv (n := 0),
    norm_iteratedFDeriv_zero] at h2
  rw [← norm_iteratedFDeriv_fderiv (n := 2), ← norm_iteratedFDeriv_fderiv (n := 1),
    ← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero] at h3
  rw [← norm_iteratedFDeriv_fderiv (n := 3), ← norm_iteratedFDeriv_fderiv (n := 2),
    ← norm_iteratedFDeriv_fderiv (n := 1), ← norm_iteratedFDeriv_fderiv (n := 0),
    norm_iteratedFDeriv_zero] at h4
  exact ⟨h2,h3,h4⟩
end NormTransfer

/-- Restricting to the live labels only decreases the explicit polynomial
budgets, so the original full input bounds every prepared face. -/
theorem live_valueCap_le_objectiveCap (v : Fin N → Fin d → ℂ)
    (δ η θ : ℝ) (x : Fin N → ℝ) :
    KSComplexObjectiveBound.valueCap (Fintype.card (Fin d ⊕ Fin d))
      (KSDebitUniformFloor.centerRadius v δ η +
        2 * KSComplexPolynomialBounds.slopeBudget (fun i : Live 1 x => v i))
      2 (KSComplexPolynomialBounds.sourceBudget (fun i : Live 1 x => v i)) θ ≤
        KSJointBoundParameters.objectiveCap v δ η θ := by
  have hs := KSComplexPolynomialBounds.slopeBudget_restrict v x
  have hm := KSComplexPolynomialBounds.sourceBudget_restrict v x
  have hb : KSComplexObjectiveBound.valueCap (Fintype.card (Fin d ⊕ Fin d))
      (KSDebitUniformFloor.centerRadius v δ η +
        2 * KSComplexPolynomialBounds.slopeBudget (fun i : Live 1 x => v i))
      2 (KSComplexPolynomialBounds.sourceBudget (fun i : Live 1 x => v i)) θ ≤
      KSComplexObjectiveBound.valueCap (Fintype.card (Fin d ⊕ Fin d))
        (KSJointBoundParameters.centerCap v δ η) 2 (KSComplexPolynomialBounds.sourceBudget v) θ := by
    unfold KSComplexObjectiveBound.valueCap KSJointBoundParameters.centerCap
    gcongr
  unfold KSJointBoundParameters.objectiveCap
  linarith

/-- Assembly helper: all geometric, optimizer, smoothness, real-agreement and
norm-transfer premises are discharged. The final theorem below supplies the
remaining actual value estimate with its concrete proof. -/
theorem jointBounds_of_actual_value_bounds (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hθ : 0 < θ) (hd : 0 < d)
    (hvalue : ∀ (s : Prepared v δ η θ hd), ¬KSDebitWalkRun.terminal s →
      ∀ (h : Live 1 s.coeff → ℝ), (∀ i, |h i| ≤ 2) →
      ∀ t : ℝ, |t| ≤ δ / 16 →
      ∀ p ∈ Metric.ball ((t : ℂ),curveDensity v δ η θ s.coeff h t)
        (KSJointBoundParameters.radius v δ η θ),
        ‖KSComplexOwnerObjective.objective (stateCenter v δ η s.coeff)
          (fun i : Live 1 s.coeff => v i) θ (fun i => s.coeff i) h p‖ ≤
            KSJointBoundParameters.objectiveCap v δ η θ) :
    JointBounds v δ η θ (KSJointBoundParameters.jointCap v δ η θ) hd := by
  constructor
  intro s hs h hdir t ht
  let q := curveBranch (stateCenter v δ η s.coeff) (stateCenter_isHermitian v δ η s.coeff)
    (fun i : Live 1 s.coeff => v i) θ (fun i => s.coeff i) h t
  let F := KSComplexOwnerObjective.objective (stateCenter v δ η s.coeff)
    (fun i : Live 1 s.coeff => v i) θ (fun i => s.coeff i) h
  have hmargin (i : Live 1 s.coeff) : δ ≤ 1 - |s.coeff i| := (s.margin i i.property).le
  have hbase : KSComplexEnvelopeChart.base (Fin d ⊕ Fin d) +
      KSComplexEnvelopeChart.jointEmbedding (Fin d ⊕ Fin d) (t,q) =
        ((t : ℂ),curveDensity v δ η θ s.coeff h t) := by
    rw [KSComplexEnvelopeChart.base_add_jointEmbedding]
    rfl
  have hF : ContDiffOn ℂ ∞ F
      (Metric.ball (KSComplexEnvelopeChart.base (Fin d ⊕ Fin d) +
        KSComplexEnvelopeChart.jointEmbedding (Fin d ⊕ Fin d) (t,q))
        (KSJointBoundParameters.radius v δ η θ)) := by
    rw [hbase]
    exact curve_complex_contDiff v hδ hη hθ s.cube h hmargin hdir ht
  have hK : ∀ p ∈ Metric.ball (KSComplexEnvelopeChart.base (Fin d ⊕ Fin d) +
        KSComplexEnvelopeChart.jointEmbedding (Fin d ⊕ Fin d) (t,q))
        (KSJointBoundParameters.radius v δ η θ),
      ‖F p‖ ≤ KSJointBoundParameters.objectiveCap v δ η θ := by
    rw [hbase]
    exact hvalue s hs h hdir t ht
  have hb := KSComplexEnvelopeChart.chart_derivatives_le_common_cap (Fin d ⊕ Fin d) F
    (KSJointBoundParameters.radius_pos v hδ hη hθ)
    (KSJointBoundParameters.radius_le_one v δ η θ)
    (KSJointBoundParameters.objectiveCap_pos v hδ.le hη hθ.le).le hF hK
  exact nested_bounds_of_eventuallyEq
    (curve_objective_eventuallyEq v hδ hθ s.coeff h hmargin hdir ht) hb

/-- The actual KS joint derivative certificate follows from the primitive
scalar input conditions. The cap is an explicit expression in input entries;
no analytic bound or numerical accuracy statement is assumed. -/
theorem jointBounds (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hθ : 0 < θ) (hd : 0 < d) :
    JointBounds v δ η θ (KSJointBoundParameters.jointCap v δ η θ) hd := by
  apply jointBounds_of_actual_value_bounds v hδ hη hθ hd
  intro s hs h hdir t ht p hp
  have hmargin (i : Live 1 s.coeff) : δ ≤ 1 - |s.coeff i| := (s.margin i i.property).le
  have hb := KSComplexOwnerValueBound.objective_norm_le_on_ball
    (stateCenter v δ η s.coeff) (fun i : Live 1 s.coeff => v i) θ
    (fun i => s.coeff i) h t (curveDensity v δ η θ s.coeff h t)
    (KSDebitUniformFloor.uniformFloor_pos v hδ.le hη hθ)
    (curveDensity_floor v hδ hη hθ s.cube h hmargin hdir ht)
    (show (0 : ℝ) < δ / 2 from by positivity)
    (curve_point_margin hδ s.coeff h hmargin hdir ht) hdir
    (curveDensity_norm_le v δ η θ s.coeff h t hθ)
    (curve_complexCenter_norm_le v hδ hη s.cube h hmargin hdir ht)
    (KSDebitUniformFloor.centerRadius_pos v hδ.le hη).le hθ.le p hp
  exact hb.trans (live_valueCap_le_objectiveCap v δ η θ s.coeff)

end MatrixSpencer.KSInputJointBounds
