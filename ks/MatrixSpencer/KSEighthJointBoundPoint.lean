import MatrixSpencer.KSEighthAnalyticCurve

/-!
# Quantitative joint derivatives at an eighth-cube query point

The scalar radii and caps are arithmetic expressions. The only budget premises
below concern norms of actual input matrices; no derivative or optimizer
estimate is assumed. A separate full-input wrapper supplies these budgets
uniformly over all retained faces.
-/

open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.KSEighthJointBoundPoint
open KSEighthTraceSource KSEighthAnalyticCurve KSActualEnvelope KSFrobeniusTangent

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def floor (R κ θ : ℝ) : ℝ := (θ / KSOptimizerFloor.inputDenominator (n := n ⊕ n) R κ θ)^2
def radius (R κ θ : ℝ) : ℝ := KSComplexPerturbationRadius.radius (floor (n := n) R κ θ) (1/2)
def valueCap (R Dcap κ θ : ℝ) : ℝ :=
  1 + KSComplexObjectiveBound.valueCap (Fintype.card (n ⊕ n)) (R+Dcap) 2 κ θ
def jointCap (R Dcap κ θ : ℝ) : ℝ :=
  valueCap (n := n) R Dcap κ θ * (10 / radius (n := n) R κ θ)^4

theorem floor_pos {R κ θ : ℝ} (hR : 0 ≤ R) (hθ : 0 < θ) : 0 < floor (n := n) R κ θ :=
  KSOptimizerFloor.inputFloor_pos hR hθ

theorem radius_pos {R κ θ : ℝ} (hR : 0 ≤ R) (hθ : 0 < θ) : 0 < radius (n := n) R κ θ :=
  KSComplexPerturbationRadius.radius_pos (floor_pos hR hθ) (by norm_num)

theorem valueCap_pos {R Dcap κ θ : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ Dcap) (hθ : 0 ≤ θ) :
    0 < valueCap (n := n) R Dcap κ θ := by
  have hv := KSComplexObjectiveBound.valueCap_nonneg (Fintype.card (n ⊕ n))
    (m := κ) (add_nonneg hR hD) (by norm_num : (0 : ℝ) ≤ 2) hθ
  unfold valueCap
  linarith

theorem jointCap_pos {R Dcap κ θ : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ Dcap) (hθ : 0 < θ) :
    0 < jointCap (n := n) R Dcap κ θ := by
  have hv := valueCap_pos (n := n) (κ := κ) hR hD hθ.le
  have hr := radius_pos (n := n) (κ := κ) hR hθ
  unfold jointCap
  positivity

theorem point_margin (x h : ι → ℝ) (hx : ∀ i, |x i| ≤ (1/8 : ℝ))
    (hh : ∀ i, |h i| ≤ 2) {t : ℝ} (ht : |t| ≤ 1/32) (i : ι) :
    |x i+t*h i| ≤ 1-(1/2 : ℝ) := by
  have hm := mul_le_mul ht (hh i) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/32)
  rw [← abs_mul] at hm
  have ha := abs_add_le (x i) (t*h i)
  linarith [hx i]

theorem query_kraus_budget (v : ι → n → ℂ) (x h : ι → ℝ)
    (hx : ∀ i, |x i| ≤ (1/8 : ℝ)) (hh : ∀ i, |h i| ≤ 2)
    {t κ : ℝ} (ht : |t| ≤ 1/32)
    (hκ : KSComplexTraceBounds.sourceBudget (KSEighthActualState.family v) ≤ κ) :
    (∑ j, (covarianceKraus (KSEighthActualState.family v) (C x h t) j)ᴴ *
      covarianceKraus (KSEighthActualState.family v) (C x h t) j) ≤
      κ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  have hp := coefficient_posDef x h t (fun i => (point_margin x h hx hh ht i).trans_lt (by norm_num))
  simp only [C, KSEighthSmoothness.coefficientCovarianceCLM_coe]
  rw [KSOwnerInputBounds.covarianceKraus_sum_eq _ (KSEighthActualState.family_isHermitian v) hp.posSemidef]
  have hn := KSComplexTraceBounds.source_norm_le_budget (KSEighthActualState.family v)
    (family_posSemidef v) (owners x) (owners h)
    (fun j => (hx j.1).trans (by norm_num)) (fun j => hh j.1) (t : ℂ)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using ht.trans (by norm_num : (1/32 : ℝ) ≤ 1))
    (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) (by simp)
  rw [source_real] at hn
  have hps := covarianceSource_posSemidef _ (KSEighthActualState.family_isHermitian v)
    hp.posSemidef Matrix.PosSemidef.one
  have hb := (CStarAlgebra.norm_le_iff_le_algebraMap _
    ((KSComplexTraceBounds.sourceBudget_pos _).le.trans hκ) hps.nonneg).mp (hn.trans hκ)
  simpa only [Algebra.algebraMap_eq_smul_one] using hb

theorem density_floor (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (v : ι → n → ℂ)
    {θ R κ : ℝ} (hθ : 0 < θ) (x h : ι → ℝ)
    (hx : ∀ i, |x i| ≤ (1/8 : ℝ)) (hh : ∀ i, |h i| ≤ 2)
    {t : ℝ} (ht : |t| ≤ 1/32)
    (hR : ‖(H Q hQ v h t : Matrix (n ⊕ n) (n ⊕ n) ℂ)‖ ≤ R)
    (hκ : KSComplexTraceBounds.sourceBudget (KSEighthActualState.family v) ≤ κ) :
    floor (n := n) R κ θ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ density Q hQ v θ x h t := by
  unfold density KSEighthAnalyticCurve.branch
  rw [chart_branch]
  exact KSOptimizerFloor.densityOptimizer_floor _ (H Q hQ v h t).property _ hθ hR
    (query_kraus_budget v x h hx hh ht hκ)

theorem joint_bounds (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (v : ι → n → ℂ)
    {θ R Dcap κ : ℝ} (hθ : 0 < θ) (x h : ι → ℝ)
    (hx : ∀ i, |x i| ≤ (1/8 : ℝ)) (hh : ∀ i, |h i| ≤ 2)
    {t : ℝ} (ht : |t| ≤ 1/32)
    (hR : ‖(H Q hQ v h t : Matrix (n ⊕ n) (n ⊕ n) ℂ)‖ ≤ R)
    (hD : ‖KSComplexOwnerObjective.slope v h‖ ≤ Dcap)
    (hκ : KSComplexTraceBounds.sourceBudget (KSEighthActualState.family v) ≤ κ) :
    secondNorm (KSEighthAnalyticCurve.objective Q hQ v θ x h)
      (t,KSEighthAnalyticCurve.branch Q hQ v θ x h t) ≤ jointCap (n := n) R Dcap κ θ ∧
    thirdNorm (KSEighthAnalyticCurve.objective Q hQ v θ x h)
      (t,KSEighthAnalyticCurve.branch Q hQ v θ x h t) ≤ jointCap (n := n) R Dcap κ θ ∧
    fourthNorm (KSEighthAnalyticCurve.objective Q hQ v θ x h)
      (t,KSEighthAnalyticCurve.branch Q hQ v θ x h t) ≤ jointCap (n := n) R Dcap κ θ := by
  let S := density Q hQ v θ x h t
  have hR0 := (norm_nonneg _).trans hR
  have hD0 := (norm_nonneg _).trans hD
  have hμ := floor_pos (n := n) (κ := κ) hR0 hθ
  have hf := density_floor Q hQ v hθ x h hx hh ht hR hκ
  have hmargin := point_margin x h hx hh ht
  have hbase : (KSComplexTraceDomain.baseSource (frame v) (KSEighthActualState.family v)
      (fun j => owners x j+t*owners h j) (owners h) S).PosDef := by
    have hb := compressedSource_posDef v (fun i => x i+t*h i) h 0
      (density_posDef Q hQ v hθ x h t)
      (fun i => by simpa using (hmargin i).trans_lt (by norm_num : 1-(1/2 : ℝ) < 1))
    exact hb
  have hc := KSComplexTraceObjective.contDiffOn_objective (frame v) (frame_isometry v)
    (signedLift Q) (KSComplexOwnerObjective.slope v h) (KSEighthActualState.family v)
    (family_posSemidef v) θ (owners x) (owners h) t S hbase hμ hf
    (by norm_num : (0 : ℝ) < 1/2) (fun j => hmargin j.1) (fun j => hh j.1)
  have hb : ∀ p ∈ Metric.ball ((t : ℂ),S) (radius (n := n) R κ θ),
      ‖extension Q v θ x h p‖ ≤ valueCap (n := n) R Dcap κ θ := by
    intro p hp
    have hv := KSComplexTraceValueBound.objective_norm_le_on_ball (frame v) (frame_isometry v)
      (support_card_le v) (signedLift Q) (KSComplexOwnerObjective.slope v h)
      (KSEighthActualState.family v) (family_posSemidef v) θ (owners x) (owners h) t S
      hbase hμ hf (by norm_num : (0 : ℝ) < 1/2) (fun j => hmargin j.1) (fun j => hh j.1)
      (density_norm_le Q hQ v hθ x h t) hR hD hR0 hθ.le p hp
    apply hv.trans
    unfold valueCap KSComplexObjectiveBound.valueCap
    have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hκ (by norm_num : (0 : ℝ) ≤ 2))
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2*(Fintype.card (n ⊕ n) : ℝ))
      (sub_nonneg.mpr hs)]
  have hchart := KSComplexEnvelopeChart.chart_derivatives_le_common_cap (n ⊕ n)
    (extension Q v θ x h) (x := (t,KSEighthAnalyticCurve.branch Q hQ v θ x h t))
    (radius_pos (n := n) (κ := κ) hR0 hθ) (KSComplexPerturbationRadius.radius_le_one _ _)
    (valueCap_pos (n := n) (κ := κ) hR0 hD0 hθ.le).le
    (by simpa only [KSComplexEnvelopeChart.base_add_jointEmbedding] using hc)
    (by simpa only [KSComplexEnvelopeChart.base_add_jointEmbedding] using hb)
  exact KSInputJointBounds.nested_bounds_of_eventuallyEq
    (extension_eventuallyEq Q hQ v θ x h t _ (density_posDef Q hQ v hθ x h t)
      (fun i => (hmargin i).trans_lt (by norm_num))) hchart

end MatrixSpencer.KSEighthJointBoundPoint
