import MatrixSpencer.KSInexactIteration
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Projected ascent from the actual gradient and its derivative

The differential strong-concavity and Lipschitz bounds imply a contraction;
the optimizer fixed-point equation is proved from actual maximization.
Exact metric projection is distinct from the supplied approximate projection
reports. The report errors and feasibility remain explicit computation inputs.
-/

noncomputable section

namespace MatrixSpencer.KSProjectedContraction

open KSInexactIteration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A concrete conservative step and contraction factor. The `1/L` step can
be sharper; this choice only needs the two elementary derivative bounds. -/
theorem conservative_parameters {μ L : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) :
    0 < μ / L ^ 2 ∧ 0 ≤ Real.sqrt (1 - (μ / L) ^ 2) ∧
      Real.sqrt (1 - (μ / L) ^ 2) < 1 ∧
      1 - 2 * (μ / L ^ 2) * μ + (μ / L ^ 2) ^ 2 * L ^ 2 ≤
        (Real.sqrt (1 - (μ / L) ^ 2)) ^ 2 := by
  have hL : 0 < L := hμ.trans_le hμL
  have hr : 0 < μ / L := div_pos hμ hL
  have hrone : μ / L ≤ 1 := (div_le_one hL).mpr hμL
  have hrad : 0 ≤ 1 - (μ / L) ^ 2 := by nlinarith
  have hid : 1 - 2 * (μ / L ^ 2) * μ + (μ / L ^ 2) ^ 2 * L ^ 2 =
      1 - (μ / L) ^ 2 := by field_simp; ring
  refine ⟨div_pos hμ (sq_pos_of_pos hL), Real.sqrt_nonneg _, ?_, ?_⟩
  · have hs := Real.sq_sqrt hrad
    nlinarith [Real.sqrt_nonneg (1 - (μ / L) ^ 2)]
  · rw [Real.sq_sqrt hrad, hid]

/-- The Hilbert norm identity gives a quantitative ascent contraction from
strong negative curvature and an upper derivative bound. -/
theorem ascent_linear_norm_le (A : E →L[ℝ] E) {μ L η q : ℝ}
    (hη : 0 ≤ η) (hq : 0 ≤ q) (_hL : 0 ≤ L)
    (hstrong : ∀ v, inner ℝ (A v) v ≤ -μ * ‖v‖ ^ 2)
    (hbound : ‖A‖ ≤ L)
    (hstep : 1 - 2 * η * μ + η ^ 2 * L ^ 2 ≤ q ^ 2) :
    ‖ContinuousLinearMap.id ℝ E + η • A‖ ≤ q := by
  apply ContinuousLinearMap.opNorm_le_bound _ hq
  intro v
  have ha : ‖A v‖ ≤ L * ‖v‖ :=
    (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg v))
  have ha2 : ‖A v‖ ^ 2 ≤ L ^ 2 * ‖v‖ ^ 2 := by
    nlinarith [norm_nonneg (A v), mul_nonneg _hL (norm_nonneg v)]
  have hs := mul_le_mul_of_nonneg_left (hstrong v) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hη)
  have hb := mul_le_mul_of_nonneg_left ha2 (sq_nonneg η)
  have hc := mul_le_mul_of_nonneg_right hstep (sq_nonneg ‖v‖)
  have he : ‖v + η • A v‖ ^ 2 =
      ‖v‖ ^ 2 + 2 * η * inner ℝ (A v) v + η ^ 2 * ‖A v‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, real_inner_comm v (A v),
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
    ring
  change ‖v + η • A v‖ ≤ q * ‖v‖
  nlinarith [norm_nonneg (v + η • A v), mul_nonneg hq (norm_nonneg v)]

/-- Integration along feasible line segments converts the Hessian bounds
into a contraction of the actual (unprojected) gradient-ascent map. -/
theorem ascent_contraction_of_derivative (K : Set E) (hK : Convex ℝ K)
    (g : E → E) (Dg : E → E →L[ℝ] E) {μ L η q : ℝ}
    (hη : 0 ≤ η) (hq : 0 ≤ q) (hL : 0 ≤ L)
    (hderiv : ∀ x ∈ K, HasFDerivAt g (Dg x) x)
    (hstrong : ∀ x ∈ K, ∀ v, inner ℝ (Dg x v) v ≤ -μ * ‖v‖ ^ 2)
    (hbound : ∀ x ∈ K, ‖Dg x‖ ≤ L)
    (hstep : 1 - 2 * η * μ + η ^ 2 * L ^ 2 ≤ q ^ 2)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) :
    dist (x + η • g x) (y + η • g y) ≤ q * dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  apply hK.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun x => ContinuousLinearMap.id ℝ E + η • Dg x)
    (fun x hx => ((hasFDerivAt_id x).add ((hderiv x hx).const_smul η)).hasFDerivWithinAt)
    (fun x hx => ascent_linear_norm_le (Dg x) hη hq hL (hstrong x hx) (hbound x hx) hstep)
    hy hx

/-- Exact projection does not enlarge the proved ascent contraction. -/
theorem projected_contraction_of_derivative (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hK : Convex ℝ K)
    (g : E → E) (Dg : E → E →L[ℝ] E) {μ L η q : ℝ}
    (hη : 0 ≤ η) (hq : 0 ≤ q) (hL : 0 ≤ L)
    (hderiv : ∀ x ∈ K, HasFDerivAt g (Dg x) x)
    (hstrong : ∀ x ∈ K, ∀ v, inner ℝ (Dg x v) v ≤ -μ * ‖v‖ ^ 2)
    (hbound : ∀ x ∈ K, ‖Dg x‖ ≤ L)
    (hstep : 1 - 2 * η * μ + η ^ 2 * L ^ 2 ≤ q ^ 2)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) :
    dist (metricProjection K hne hcomplete hK (x + η • g x))
      (metricProjection K hne hcomplete hK (y + η • g y)) ≤ q * dist x y :=
  (metricProjection_nonexpansive K hne hcomplete hK _ _).trans
    (ascent_contraction_of_derivative K hK g Dg hη hq hL hderiv hstrong hbound hstep hx hy)

theorem metricProjection_eq_of_variational (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hK : Convex ℝ K) (z x : E) (hx : x ∈ K)
    (hvar : ∀ y ∈ K, inner ℝ (z - x) (y - x) ≤ 0) :
    metricProjection K hne hcomplete hK z = x := by
  let p := metricProjection K hne hcomplete hK z
  have hp := metricProjection_mem K hne hcomplete hK z
  have h₁ := metricProjection_variational K hne hcomplete hK z x hx
  have h₂ := hvar p hp
  have he : ‖p - x‖ ^ 2 =
      inner ℝ (z - p) (x - p) + inner ℝ (z - x) (p - x) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hz : ‖p - x‖ = 0 := by nlinarith [norm_nonneg (p - x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

variable [CompleteSpace E]

/-- The derivative of the actual Riesz gradient, expressed by the actual
second Frechet derivative of the objective. -/
def gradientDerivative (f : E → ℝ) (x : E) : E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fderiv ℝ (fderiv ℝ f) x)

theorem hasFDerivAt_gradient (f : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    HasFDerivAt (gradient f) (gradientDerivative f x) x :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.hasFDerivAt.comp x
    hf.hasFDerivAt

theorem gradientDerivative_inner (f : E → ℝ) (x v w : E) :
    inner ℝ (gradientDerivative f x v) w = fderiv ℝ (fderiv ℝ f) x v w :=
  InnerProductSpace.toDual_symm_apply

theorem gradientDerivative_norm_le (f : E → ℝ) (x : E) :
    ‖gradientDerivative f x‖ ≤ ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (gradientDerivative f x) (norm_nonneg (fderiv ℝ (fderiv ℝ f) x))
  intro v
  change ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fderiv ℝ f) x v)‖ ≤ _
  rw [(InnerProductSpace.toDual ℝ E).symm.norm_map]
  exact (fderiv ℝ (fderiv ℝ f) x).le_opNorm v

/-- Maximization of the objective itself proves the projection fixed-point
equation, including a constrained maximizer on the feasible boundary. -/
theorem optimizer_projected_fixed (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hK : Convex ℝ K) (f : E → ℝ) (xstar gstar : E)
    (hxstar : xstar ∈ K) (hmax : IsMaxOn f K xstar)
    (hg : HasGradientAt f gstar xstar) {η : ℝ} (hη : 0 ≤ η) :
    metricProjection K hne hcomplete hK (xstar + η • gstar) = xstar := by
  apply metricProjection_eq_of_variational K hne hcomplete hK _ xstar hxstar
  intro y hy
  have hd := hmax.localize.hasFDerivWithinAt_nonpos hg.hasFDerivAt.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hK.segment_subset hxstar hy))
  change inner ℝ gstar (y - xstar) ≤ 0 at hd
  simpa only [add_sub_cancel_left, real_inner_smul_left] using
    mul_nonpos_of_nonneg_of_nonpos hη hd

/-- The explicitly defined approximate projected iteration converges toward
an actual maximizer. Contraction and fixed-point conclusions are discharged
by the analytic hypotheses, rather than assumed as iteration inputs. -/
theorem inexact_iteration_distance_le (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hK : Convex ℝ K)
    (f : E → ℝ) (g : E → E) (Dg : E → E →L[ℝ] E)
    (gradientReport projectionReport : ℕ → E → E) (x₀ xstar : E)
    {μ L η q eg ep : ℝ} (hη : 0 ≤ η) (hq : 0 ≤ q) (hqone : q < 1)
    (hL : 0 ≤ L) (heg : 0 ≤ eg) (hep : 0 ≤ ep)
    (hstart : x₀ ∈ K) (hxstar : xstar ∈ K) (hmax : IsMaxOn f K xstar)
    (hgstar : HasGradientAt f (g xstar) xstar)
    (hderiv : ∀ x ∈ K, HasFDerivAt g (Dg x) x)
    (hstrong : ∀ x ∈ K, ∀ v, inner ℝ (Dg x v) v ≤ -μ * ‖v‖ ^ 2)
    (hbound : ∀ x ∈ K, ‖Dg x‖ ≤ L)
    (hstep : 1 - 2 * η * μ + η ^ 2 * L ^ 2 ≤ q ^ 2)
    (hfeasible : ∀ n z, projectionReport n z ∈ K)
    (hg : ∀ n x, x ∈ K → ‖gradientReport n x - g x‖ ≤ eg)
    (hp : ∀ n z,
      dist (projectionReport n z) (metricProjection K hne hcomplete hK z) ≤ ep)
    (N : ℕ) :
    dist (projectedGradientIteration η gradientReport projectionReport x₀ N) xstar ≤
      q ^ N * dist x₀ xstar + (ep + η * eg) / (1 - q) := by
  apply projectedGradientIteration_distance_le η hη g (metricProjection K hne hcomplete hK)
    gradientReport projectionReport K x₀ xstar hq hqone heg hep hstart hfeasible
  · exact optimizer_projected_fixed K hne hcomplete hK f xstar (g xstar) hxstar hmax hgstar hη
  · intro x hx
    exact projected_contraction_of_derivative K hne hcomplete hK g Dg hη hq hL
      hderiv hstrong hbound hstep hx hxstar
  · exact metricProjection_nonexpansive K hne hcomplete hK
  · exact hg
  · exact hp

end MatrixSpencer.KSProjectedContraction
