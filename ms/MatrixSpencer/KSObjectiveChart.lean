import MatrixSpencer.KSObjectiveCurvature
import MatrixSpencer.KSProjectedContraction

/-!
# The actual density objective in real Hilbert coordinates

The coordinate map and its trace-isometry property are explicit. In particular,
no Hilbert inner product is silently attached to the matrix operator norm.
The lower Hessian bound is proved from the actual regularizer; only the upper
Hessian bound is left as a quantitative input in the contraction theorem.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

noncomputable section

namespace MatrixSpencer.KSObjectiveChart

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def objective (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ)) : E → ℝ :=
  hermitianDensityObjective H B θ ∘ e

def densityFloor (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ)) (a : ℝ) : Set E :=
  {x | a • (1 : Matrix n n ℂ) ≤ (e x : Matrix n n ℂ) ∧
    realTrace (e x : Matrix n n ℂ) = 1}

theorem densityFloor_posDef (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ))
    {a : ℝ} (ha : 0 < a) {x : E} (hx : x ∈ densityFloor e a) :
    (e x : Matrix n n ℂ).PosDef := by
  have hp := (Matrix.PosDef.one.smul ha).add_posSemidef (Matrix.le_iff.mp hx.1)
  simpa only [add_sub_cancel] using hp

theorem densityFloor_isClosed (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ)) (a : ℝ) :
    IsClosed (densityFloor e a) := by
  have he : Continuous (fun x => (e x : Matrix n n ℂ)) :=
    continuous_subtype_val.comp e.continuous
  exact (isClosed_le continuous_const he).inter
    (isClosed_eq (continuous_realTrace.comp he) continuous_const)

theorem densityFloor_convex (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ)) (a : ℝ) :
    Convex ℝ (densityFloor e a) := by
  intro x hx y hy u v hu hv huv
  have hmap : (e (u • x + v • y) : Matrix n n ℂ) =
      u • (e x : Matrix n n ℂ) + v • (e y : Matrix n n ℂ) := by
    simp only [map_add, map_smul]
    rfl
  refine ⟨?_, ?_⟩
  · change a • (1 : Matrix n n ℂ) ≤ _
    rw [hmap]
    have hl := add_le_add (smul_le_smul_of_nonneg_left hx.1 hu)
      (smul_le_smul_of_nonneg_left hy.1 hv)
    simpa only [← add_smul, huv, one_smul] using hl
  · change realTrace (e (u • x + v • y) : Matrix n n ℂ) = 1
    rw [hmap, realTrace_add, realTrace_smul, realTrace_smul, hx.2, hy.2]
    simpa using huv

theorem objective_contDiffAt (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ)) (x : E)
    (hx : (e x : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (objective H B θ e) x :=
  (contDiffAt_hermitianDensityObjective_source_unrestricted H B θ (e x) hx).comp x
    e.contDiff.contDiffAt

/-- The Hessian of the actual coordinate objective is the pullback of the
actual density Hessian, with no surrogate objective. -/
theorem objective_hessian (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ)) (x v w : E)
    (hx : (e x : Matrix n n ℂ).PosDef) :
    fderiv ℝ (fderiv ℝ (objective H B θ e)) x v w =
      fderiv ℝ (fderiv ℝ (hermitianDensityObjective H B θ)) (e x) (e v) (e w) := by
  let P := (ContinuousLinearMap.compL ℝ E (selfAdjoint (Matrix n n ℂ)) ℝ).flip e
  have hd := hasStrictFDerivAt_fderiv_hermitianDensityObjective_source_unrestricted H B θ (e x) hx
  rw [← hd.hasFDerivAt.fderiv] at hd
  have hp := P.hasFDerivAt.comp x (hd.hasFDerivAt.comp x e.hasFDerivAt)
  have heq : fderiv ℝ (objective H B θ e) =ᶠ[𝓝 x]
      fun y => P (fderiv ℝ (hermitianDensityObjective H B θ) (e y)) := by
    filter_upwards [e.continuous.continuousAt.eventually
      (eventually_posDef_of_posDef (e x) hx)] with y hy
    simpa only [ContinuousLinearMap.fderiv] using fderiv_comp y
      ((contDiffAt_hermitianDensityObjective_source_unrestricted H B θ (e y) hy).differentiableAt
        (by simp)) e.differentiableAt
  rw [(hp.congr_of_eventuallyEq heq).fderiv]
  rfl

/-- Strong concavity in the genuine Euclidean/Frobenius coordinates follows
with the explicit constant `θ/2` from the proved matrix Hessian formula. -/
theorem objective_hessian_le (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ))
    (hisometry : ∀ v, realTrace ((e v : Matrix n n ℂ) * (e v : Matrix n n ℂ)) = ‖v‖ ^ 2)
    {a : ℝ} (ha : 0 < a) {x : E} (hx : x ∈ densityFloor e a) (v : E) :
    fderiv ℝ (fderiv ℝ (objective H B θ e)) x v v ≤ -(θ / 2) * ‖v‖ ^ 2 := by
  have hb := KSObjectiveCurvature.densityNegativeHessian_ge_of_density H B θ hθ (e x) (e v)
    (densityFloor_posDef e ha hx) hx.2
  rw [hisometry v] at hb
  rw [objective_hessian H B θ e x v v (densityFloor_posDef e ha hx)]
  change θ / 2 * ‖v‖ ^ 2 ≤
    -(fderiv ℝ (fderiv ℝ (hermitianDensityObjective H B θ)) (e x) (e v) (e v)) at hb
  linarith

variable [CompleteSpace E]

open KSProjectedContraction KSInexactIteration

/-- Projected ascent for the actual density objective on the actual closed
convex density-floor domain. The lower bound is discharged by the regularizer;
the upper bound `hupper` is the remaining quantitative Hessian obligation. -/
theorem projected_contraction (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ))
    (hisometry : ∀ v, realTrace ((e v : Matrix n n ℂ) * (e v : Matrix n n ℂ)) = ‖v‖ ^ 2)
    {a : ℝ} (ha : 0 < a) (hne : (densityFloor e a).Nonempty)
    {L η q : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η) (hq : 0 ≤ q)
    (hstep : 1 - 2 * η * (θ / 2) + η ^ 2 * L ^ 2 ≤ q ^ 2)
    (hupper : ∀ x ∈ densityFloor e a,
      ‖fderiv ℝ (fderiv ℝ (objective H B θ e)) x‖ ≤ L)
    {x y : E} (hx : x ∈ densityFloor e a) (hy : y ∈ densityFloor e a) :
    dist (metricProjection (densityFloor e a) hne (densityFloor_isClosed e a).isComplete
        (densityFloor_convex e a) (x + η • gradient (objective H B θ e) x))
      (metricProjection (densityFloor e a) hne (densityFloor_isClosed e a).isComplete
        (densityFloor_convex e a) (y + η • gradient (objective H B θ e) y)) ≤ q * dist x y := by
  apply projected_contraction_of_derivative (densityFloor e a) hne
    (densityFloor_isClosed e a).isComplete (densityFloor_convex e a)
    (gradient (objective H B θ e)) (gradientDerivative (objective H B θ e)) hη hq hL
    ?_ ?_ ?_ hstep hx hy
  · intro z hz
    apply hasFDerivAt_gradient
    exact ((objective_contDiffAt H B θ e z (densityFloor_posDef e ha hz)).fderiv_right
      (m := 1) (by
        change ((1 + 1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)).differentiableAt (by norm_num)
  · intro z hz v
    rw [gradientDerivative_inner]
    exact objective_hessian_le H B θ hθ e hisometry ha hz v
  · intro z hz
    exact (gradientDerivative_norm_le (objective H B θ e) z).trans (hupper z hz)

/-- The finite approximate projected run targets an actual maximizer of the
density-floor objective. Its derivative and strong-curvature assumptions are
proved, while the upper Hessian and numerical report bounds stay explicit. -/
theorem inexact_run_distance_le (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ))
    (hisometry : ∀ v, realTrace ((e v : Matrix n n ℂ) * (e v : Matrix n n ℂ)) = ‖v‖ ^ 2)
    {a : ℝ} (ha : 0 < a) (hne : (densityFloor e a).Nonempty)
    (gradientReport projectionReport : ℕ → E → E) (x₀ xstar : E)
    {L η q eg ep : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η) (hq : 0 ≤ q) (hqone : q < 1)
    (heg : 0 ≤ eg) (hep : 0 ≤ ep)
    (hstart : x₀ ∈ densityFloor e a) (hxstar : xstar ∈ densityFloor e a)
    (hmax : IsMaxOn (objective H B θ e) (densityFloor e a) xstar)
    (hstep : 1 - 2 * η * (θ / 2) + η ^ 2 * L ^ 2 ≤ q ^ 2)
    (hupper : ∀ x ∈ densityFloor e a,
      ‖fderiv ℝ (fderiv ℝ (objective H B θ e)) x‖ ≤ L)
    (hfeasible : ∀ n z, projectionReport n z ∈ densityFloor e a)
    (hg : ∀ n x, x ∈ densityFloor e a →
      ‖gradientReport n x - gradient (objective H B θ e) x‖ ≤ eg)
    (hp : ∀ n z, dist (projectionReport n z)
      (metricProjection (densityFloor e a) hne (densityFloor_isClosed e a).isComplete
        (densityFloor_convex e a) z) ≤ ep) (N : ℕ) :
    dist (projectedGradientIteration η gradientReport projectionReport x₀ N) xstar ≤
      q ^ N * dist x₀ xstar + (ep + η * eg) / (1 - q) := by
  apply projectedGradientIteration_distance_le η hη (gradient (objective H B θ e))
    (metricProjection (densityFloor e a) hne (densityFloor_isClosed e a).isComplete
      (densityFloor_convex e a)) gradientReport projectionReport (densityFloor e a)
    x₀ xstar hq hqone heg hep hstart hfeasible
  · apply optimizer_projected_fixed (densityFloor e a) hne
      (densityFloor_isClosed e a).isComplete (densityFloor_convex e a)
      (objective H B θ e) xstar _ hxstar hmax _ hη
    exact ((objective_contDiffAt H B θ e xstar (densityFloor_posDef e ha hxstar)).differentiableAt
      (by simp)).hasGradientAt
  · intro x hx
    exact projected_contraction H B θ hθ e hisometry ha hne hL hη hq hstep hupper hx hxstar
  · exact metricProjection_nonexpansive _ _ _ _
  · exact hg
  · exact hp

end MatrixSpencer.KSObjectiveChart
