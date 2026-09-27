import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Finite inexact projected iterations

The sequence is defined by the supplied update map, not supplied independently
with an assumed scalar recurrence.  A contraction and uniform update error
give a geometric distance bound and an explicit finite accuracy threshold.

The final section identifies the actual approximate projected-gradient update
and its gradient/projection error budget.  This does not assert that the KS
objective already has the required contraction estimate or a computed matrix
projection/value oracle.  Exact convex projection and its nonexpansiveness are
proved using mathlib's Hilbert projection theorem.
-/

noncomputable section

namespace MatrixSpencer
namespace KSInexactIteration

variable {X : Type*}

/-- The actual finite iteration of a possibly time-dependent approximate map. -/
def iterate (update : ℕ → X → X) (x₀ : X) : ℕ → X
  | 0 => x₀
  | n + 1 => update n (iterate update x₀ n)

theorem iterate_mem (update : ℕ → X → X) (x₀ : X) (S : Set X)
    (hstart : x₀ ∈ S) (hupdate : ∀ n x, x ∈ S → update n x ∈ S) (n : ℕ) :
    iterate update x₀ n ∈ S := by
  induction n with
  | zero => exact hstart
  | succ n ih => exact hupdate n _ ih

section Metric

variable [PseudoMetricSpace X]

theorem step_distance_le (update : ℕ → X → X) (T : X → X) (x₀ xstar : X)
    (S : Set X) (q e : ℝ) (hstart : x₀ ∈ S)
    (hupdate : ∀ n x, x ∈ S → update n x ∈ S)
    (hfixed : T xstar = xstar)
    (hcontract : ∀ x ∈ S, dist (T x) (T xstar) ≤ q * dist x xstar)
    (herror : ∀ n x, x ∈ S → dist (update n x) (T x) ≤ e) (n : ℕ) :
    dist (iterate update x₀ (n + 1)) xstar ≤
      q * dist (iterate update x₀ n) xstar + e := by
  have hx := iterate_mem update x₀ S hstart hupdate n
  have hc := hcontract _ hx
  rw [hfixed] at hc
  exact (dist_triangle (update n (iterate update x₀ n)) (T (iterate update x₀ n)) xstar).trans
    (by linarith [herror n _ hx])

/-- The perturbation floor is `e / (1-q)`; the initial error decays as `q^n`. -/
theorem distance_le (update : ℕ → X → X) (T : X → X) (x₀ xstar : X)
    (S : Set X) {q e : ℝ} (hq : 0 ≤ q) (hqone : q < 1) (he : 0 ≤ e)
    (hstart : x₀ ∈ S) (hupdate : ∀ n x, x ∈ S → update n x ∈ S)
    (hfixed : T xstar = xstar)
    (hcontract : ∀ x ∈ S, dist (T x) (T xstar) ≤ q * dist x xstar)
    (herror : ∀ n x, x ∈ S → dist (update n x) (T x) ≤ e) (n : ℕ) :
    dist (iterate update x₀ n) xstar ≤ q ^ n * dist x₀ xstar + e / (1 - q) := by
  have hd : 0 < 1 - q := sub_pos.mpr hqone
  have hf : 0 ≤ e / (1 - q) := div_nonneg he hd.le
  have hid : q * (e / (1 - q)) + e = e / (1 - q) := by
    have h := div_mul_cancel₀ e (ne_of_gt hd)
    nlinarith
  induction n with
  | zero => simpa [iterate] using le_add_of_nonneg_right (a := dist x₀ xstar) hf
  | succ n ih =>
    have hs := step_distance_le update T x₀ xstar S q e hstart hupdate hfixed
      hcontract herror n
    calc
      _ ≤ q * (q ^ n * dist x₀ xstar + e / (1 - q)) + e :=
        hs.trans (add_le_add_right (mul_le_mul_of_nonneg_left ih hq) e)
      _ = _ := by rw [pow_succ]; nlinarith [hid]

end Metric

/-- A coarse explicit bound sufficient for a finite iteration count. -/
theorem pow_mul_linear_le_one {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    q ^ n * (1 + (n : ℝ) * (1 - q)) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hf : q * (1 + ((n : ℝ) + 1) * (1 - q)) ≤ 1 + (n : ℝ) * (1 - q) := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ (n : ℝ) + 1) (sq_nonneg (1 - q))]
    calc
      _ = q ^ n * (q * (1 + ((n : ℝ) + 1) * (1 - q))) := by
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ q ^ n * (1 + (n : ℝ) * (1 - q)) :=
        mul_le_mul_of_nonneg_left hf (pow_nonneg hq n)
      _ ≤ 1 := ih

/-- A conservative finite count; no logarithm computation is required. -/
def iterationCount (q D τ : ℝ) : ℕ := ⌈2 * D / ((1 - q) * τ)⌉₊

theorem iterationCount_spec {q τ : ℝ} (hqone : q < 1) (hτ : 0 < τ) (D : ℝ) :
    2 * D ≤ (iterationCount q D τ : ℝ) * ((1 - q) * τ) := by
  have hd : 0 < (1 - q) * τ := mul_pos (sub_pos.mpr hqone) hτ
  exact (div_le_iff₀ hd).mp (Nat.le_ceil (2 * D / ((1 - q) * τ)))

theorem geometric_error_at_count {q τ : ℝ} (hq : 0 ≤ q) (hqone : q < 1)
    (hτ : 0 < τ) (D : ℝ) : q ^ iterationCount q D τ * D ≤ τ / 2 := by
  have hp := pow_mul_linear_le_one hq (iterationCount q D τ)
  have hc := mul_le_mul_of_nonneg_left (iterationCount_spec hqone hτ D)
    (pow_nonneg hq (iterationCount q D τ))
  have hb := mul_le_mul_of_nonneg_left hp hτ.le
  nlinarith [mul_nonneg (pow_nonneg hq (iterationCount q D τ)) hτ.le]

section Metric

variable [PseudoMetricSpace X]

/-- The explicit finite iterate attains the requested accuracy when the
per-step error leaves at least half the error budget for geometric decay. -/
theorem distance_at_count_le (update : ℕ → X → X) (T : X → X) (x₀ xstar : X)
    (S : Set X) {q e τ : ℝ} (hq : 0 ≤ q) (hqone : q < 1) (he : 0 ≤ e)
    (hτ : 0 < τ) (hsmall : e ≤ (1 - q) * τ / 2)
    (hstart : x₀ ∈ S) (hupdate : ∀ n x, x ∈ S → update n x ∈ S)
    (hfixed : T xstar = xstar)
    (hcontract : ∀ x ∈ S, dist (T x) (T xstar) ≤ q * dist x xstar)
    (herror : ∀ n x, x ∈ S → dist (update n x) (T x) ≤ e) :
    dist (iterate update x₀ (iterationCount q (dist x₀ xstar) τ)) xstar ≤ τ := by
  have hr := distance_le update T x₀ xstar S hq hqone he hstart hupdate hfixed
    hcontract herror (iterationCount q (dist x₀ xstar) τ)
  have hg := geometric_error_at_count hq hqone hτ (dist x₀ xstar)
  have he' : e / (1 - q) ≤ τ / 2 := by
    apply (div_le_iff₀ (sub_pos.mpr hqone)).mpr
    nlinarith [hsmall]
  linarith

end Metric

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The variational inequalities alone imply nonexpansiveness of projection
onto a convex feasible set. -/
theorem projection_nonexpansive_of_variational (K : Set E) (p : E → E)
    (hmem : ∀ x, p x ∈ K)
    (hvar : ∀ x y, y ∈ K → inner ℝ (x - p x) (y - p x) ≤ 0) (x y : E) :
    dist (p x) (p y) ≤ dist x y := by
  have hx := hvar x (p y) (hmem y)
  have hy := hvar y (p x) (hmem x)
  have hid : inner ℝ (x - y) (p x - p y) - ‖p x - p y‖ ^ 2 =
      -inner ℝ (x - p x) (p y - p x) - inner ℝ (y - p y) (p x - p y) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hs : ‖p x - p y‖ ^ 2 ≤ inner ℝ (x - y) (p x - p y) := by linarith
  have hc := real_inner_le_norm (x - y) (p x - p y)
  rw [dist_eq_norm, dist_eq_norm]
  by_cases hp : ‖p x - p y‖ = 0
  · rw [hp]
    exact norm_nonneg _
  · have hpos : 0 < ‖p x - p y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hp)
    apply (mul_le_mul_iff_left₀ hpos).mp
    nlinarith

/-- The exact closest point supplied by the Hilbert projection theorem. -/
def metricProjection (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (x : E) : E :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x).choose

theorem metricProjection_mem (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (x : E) : metricProjection K hne hcomplete hconvex x ∈ K :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x).choose_spec.1

theorem metricProjection_variational (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x y : E) (hy : y ∈ K) :
    inner ℝ (x - metricProjection K hne hcomplete hconvex x)
      (y - metricProjection K hne hcomplete hconvex x) ≤ 0 := by
  apply (norm_eq_iInf_iff_real_inner_le_zero hconvex
    (metricProjection_mem K hne hcomplete hconvex x)).mp
      (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x).choose_spec.2 y hy

/-- In a complete ambient space, a nonempty closed convex set supplies these
hypotheses through `IsClosed.isComplete`. -/
theorem metricProjection_nonexpansive (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x y : E) :
    dist (metricProjection K hne hcomplete hconvex x)
      (metricProjection K hne hcomplete hconvex y) ≤ dist x y :=
  projection_nonexpansive_of_variational K (metricProjection K hne hcomplete hconvex)
    (metricProjection_mem K hne hcomplete hconvex)
    (metricProjection_variational K hne hcomplete hconvex) x y

/-- The actual inexact projected-gradient map used to define the finite run. -/
def projectedUpdate (η : ℝ) (gradientReport projectionReport : ℕ → E → E)
    (n : ℕ) (x : E) : E := projectionReport n (x + η • gradientReport n x)

def projectedGradientIteration (η : ℝ) (gradientReport projectionReport : ℕ → E → E)
    (x₀ : E) : ℕ → E := iterate (projectedUpdate η gradientReport projectionReport) x₀

/-- The computed gradient contributes `η*eg`, and the approximate projection
contributes `ep`, to the actual update error. -/
theorem projectedUpdate_error (η : ℝ) (hη : 0 ≤ η) (gradient projection : E → E)
    (gradientReport projectionReport : ℕ → E → E) (eg ep : ℝ)
    (hproj : ∀ x y, dist (projection x) (projection y) ≤ dist x y)
    (n : ℕ) (x : E)
    (hg : ‖gradientReport n x - gradient x‖ ≤ eg)
    (hp : ∀ z, dist (projectionReport n z) (projection z) ≤ ep) :
    dist (projectedUpdate η gradientReport projectionReport n x)
      (projection (x + η • gradient x)) ≤ ep + η * eg := by
  unfold projectedUpdate
  calc
    _ ≤ dist (projectionReport n (x + η • gradientReport n x))
          (projection (x + η • gradientReport n x)) +
        dist (projection (x + η • gradientReport n x)) (projection (x + η • gradient x)) :=
      dist_triangle _ _ _
    _ ≤ ep + dist (x + η • gradientReport n x) (x + η • gradient x) :=
      add_le_add (hp _) (hproj _ _)
    _ = ep + η * ‖gradientReport n x - gradient x‖ := by
      rw [dist_eq_norm]
      have h : (x + η • gradientReport n x) - (x + η • gradient x) =
          η • (gradientReport n x - gradient x) := by module
      rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left hg hη) ep

/-- A rate for the explicitly defined inexact projected-gradient run. -/
theorem projectedGradientIteration_distance_le (η : ℝ) (hη : 0 ≤ η)
    (gradient projection : E → E) (gradientReport projectionReport : ℕ → E → E)
    (K : Set E) (x₀ xstar : E) {q eg ep : ℝ}
    (hq : 0 ≤ q) (hqone : q < 1) (heg : 0 ≤ eg) (hep : 0 ≤ ep)
    (hstart : x₀ ∈ K) (hfeasible : ∀ n z, projectionReport n z ∈ K)
    (hfixed : projection (xstar + η • gradient xstar) = xstar)
    (hcontract : ∀ x ∈ K,
      dist (projection (x + η • gradient x)) (projection (xstar + η • gradient xstar)) ≤
        q * dist x xstar)
    (hproj : ∀ x y, dist (projection x) (projection y) ≤ dist x y)
    (hg : ∀ n x, x ∈ K → ‖gradientReport n x - gradient x‖ ≤ eg)
    (hp : ∀ n z, dist (projectionReport n z) (projection z) ≤ ep) (N : ℕ) :
    dist (projectedGradientIteration η gradientReport projectionReport x₀ N) xstar ≤
      q ^ N * dist x₀ xstar + (ep + η * eg) / (1 - q) := by
  apply distance_le (projectedUpdate η gradientReport projectionReport)
    (fun x => projection (x + η • gradient x)) x₀ xstar K hq hqone
      (add_nonneg hep (mul_nonneg hη heg)) hstart
  · intro n x _
    exact hfeasible n _
  · exact hfixed
  · exact hcontract
  · intro n x hx
    exact projectedUpdate_error η hη gradient projection gradientReport projectionReport
      eg ep hproj n x (hg n x hx) (hp n)

end Projection

end KSInexactIteration
end MatrixSpencer
