import MatrixSpencer.KSFullManuscriptLevelBall
import MatrixSpencer.KSFullManuscriptEllipsoidCutoff
import MatrixSpencer.KSFullManuscriptBisection

/-!
# Actual ellipsoid feasibility and tolerant bisection for affine SDPs

Every feasibility answer is computed by the finite central-cut recursion
using the symmetric-elimination and objective separator. The explicit input
inner/outer radii prove its weak-feasibility specification; that specification
is not an oracle hypothesis. The remaining KS-specific obligation is to
construct the concrete affine density SDP and its explicit geometry bounds.
-/

open Matrix
open scoped BigOperators InnerProductSpace
noncomputable section
namespace MatrixSpencer.KSFullManuscriptWeakOptimization

open KSFullManuscriptAffinePSD KSFullManuscriptSuperlevel KSFullManuscriptLevelBall
open KSFullManuscriptEllipsoidRun KSFullManuscriptEllipsoidCutoff
variable {ℓ n : ℕ}

theorem base_convex (D : Data ℓ n) : Convex ℝ (KSFullManuscriptAffinePSD.target D) := by
  intro x hx y hy a b ha hb hab
  change (matrixAt D (a • x + b • y)).PosSemidef
  have he : matrixAt D (a • x + b • y) = a • matrixAt D x + b • matrixAt D y := by
    simp only [matrixAt, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      add_smul, MulAction.mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, smul_add]
    have hc : D.constant = a • D.constant + b • D.constant := by
      rw [← add_smul, hab, one_smul]
    conv_lhs => rw [hc]
    abel
  refine ⟨?_, fun v => ?_⟩
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using matrixAt_isSymm D (a • x + b • y)
  · rw [he]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, star_trivial, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.2 v)) (mul_nonneg hb (hy.2 v))

/-- The computed finite feasibility result. It does not depend on a feasible
point, an optimizer, or any chosen separating direction. -/
def feasible (D : Data ℓ n) (c fallback : Space ℓ) (b R r L τ t : ℝ) : Bool :=
  (output (ℓ : ℝ) (KSFullManuscriptSuperlevel.query D c fallback b t)
    (KSFullManuscriptEllipsoidCutoff.budget ℓ R (fraction τ L R * r))
    (initial 0 R)).isSome

theorem feasible_sound (D : Data ℓ n) (c fallback z : Space ℓ) (b R r L τ t : ℝ)
    (hz : z ∈ KSFullManuscriptAffinePSD.target D) (hf : fallback ≠ 0)
    (hyes : feasible D c fallback b R r L τ t = true) :
    ∃ y, y ∈ KSFullManuscriptAffinePSD.target D ∧ t ≤ objective c b y := by
  let sep := KSFullManuscriptSuperlevel.procedure D c fallback b t z hz hf
  unfold feasible at hyes
  cases ho : output (ℓ : ℝ) (KSFullManuscriptSuperlevel.query D c fallback b t)
      (KSFullManuscriptEllipsoidCutoff.budget ℓ R (fraction τ L R * r)) (initial 0 R) with
  | none => simp [ho] at hyes
  | some y =>
    exact ⟨y, output_sound (ℓ : ℝ) sep _ _ ho⟩

theorem feasible_of_gap (D : Data ℓ n) (c fallback z x : Space ℓ) {b R r L τ t : ℝ}
    (hℓ : 1 < ℓ) (hf : fallback ≠ 0)
    (hR : 0 < R) (hr : 0 < r) (hL : 0 < L) (hτ : 0 < τ) (hτcap : τ ≤ L * R)
    (hrR : r ≤ R) (hc : ‖c‖ ≤ L)
    (houter : KSFullManuscriptAffinePSD.target D ⊆ Metric.closedBall 0 R)
    (hinner : Metric.closedBall z r ⊆ KSFullManuscriptAffinePSD.target D)
    (hx : x ∈ KSFullManuscriptAffinePSD.target D)
    (hgap : t + τ ≤ objective c b x) :
    feasible D c fallback b R r L τ t = true := by
  have hz : z ∈ KSFullManuscriptAffinePSD.target D := hinner (Metric.mem_closedBall_self hr.le)
  have hxR : ‖x‖ ≤ R := by simpa using houter hx
  have hzR : ‖z‖ ≤ R := by simpa using houter hz
  have hball := explicit_ball_subset_level (base_convex D) hx hinner hτ hτcap hL hR
    hxR hzR hrR hc hgap
  let sep := KSFullManuscriptSuperlevel.procedure D c fallback b t z hz hf
  have hout : KSFullManuscriptSuperlevel.target D c b t ⊆ Metric.closedBall 0 R :=
    fun y hy => houter hy.1
  obtain ⟨y, hy, _⟩ := output_by_budget hℓ sep 0 (mixture (fraction τ L R) x z)
    hR (mul_pos (fraction_pos hτ hL hR) hr) hout hball
  unfold feasible
  change (output (ℓ : ℝ) sep.query _ _).isSome = true
  rw [hy]
  rfl

/-- A false answer bounds every feasible objective value. -/
theorem false_bounds_all (D : Data ℓ n) (c fallback z : Space ℓ) {b R r L τ t : ℝ}
    (hℓ : 1 < ℓ) (hf : fallback ≠ 0)
    (hR : 0 < R) (hr : 0 < r) (hL : 0 < L) (hτ : 0 < τ) (hτcap : τ ≤ L * R)
    (hrR : r ≤ R) (hc : ‖c‖ ≤ L)
    (houter : KSFullManuscriptAffinePSD.target D ⊆ Metric.closedBall 0 R)
    (hinner : Metric.closedBall z r ⊆ KSFullManuscriptAffinePSD.target D)
    (hno : feasible D c fallback b R r L τ t = false) :
    ∀ x ∈ KSFullManuscriptAffinePSD.target D, objective c b x ≤ t + τ := by
  intro x hx
  by_contra hh
  have hyes := feasible_of_gap D c fallback z x hℓ hf hR hr hL hτ hτcap hrR hc
    houter hinner hx (le_of_lt (lt_of_not_ge hh))
  rw [hno] at hyes
  contradiction

/-- The actual finite PSD/ellipsoid routine discharges tolerant bisection's
feasibility contract. An optimizer occurs only in this proof specification. -/
theorem correctFeasibility (D : Data ℓ n) (c fallback z x : Space ℓ) {b R r L τ : ℝ}
    (hℓ : 1 < ℓ) (hf : fallback ≠ 0)
    (hR : 0 < R) (hr : 0 < r) (hL : 0 < L) (hτ : 0 < τ) (hτcap : τ ≤ L * R)
    (hrR : r ≤ R) (hc : ‖c‖ ≤ L)
    (houter : KSFullManuscriptAffinePSD.target D ⊆ Metric.closedBall 0 R)
    (hinner : Metric.closedBall z r ⊆ KSFullManuscriptAffinePSD.target D)
    (hx : x ∈ KSFullManuscriptAffinePSD.target D)
    (hmax : ∀ y ∈ KSFullManuscriptAffinePSD.target D, objective c b y ≤ objective c b x) :
    KSFullManuscriptBisection.CorrectFeasibility (feasible D c fallback b R r L τ)
      (objective c b x) τ := by
  have hz := hinner (Metric.mem_closedBall_self hr.le)
  intro t
  constructor
  · intro hyes
    obtain ⟨y, hy, ht⟩ := feasible_sound D c fallback z b R r L τ t hz hf hyes
    exact ht.trans (hmax y hy)
  · intro hno
    exact false_bounds_all D c fallback z hℓ hf hR hr hL hτ hτcap hrR hc houter hinner hno x hx

/-- Numerical value: finite tolerant bisection of the actual ellipsoid test. -/
def report (D : Data ℓ n) (c fallback : Space ℓ) (b R r L τ ω : ℝ)
    (interval : KSFullManuscriptBisection.Interval) : ℝ :=
  KSFullManuscriptBisection.report (feasible D c fallback b R r L τ) ω τ interval

theorem report_accuracy (D : Data ℓ n) (c fallback z x : Space ℓ) {b R r L τ ω : ℝ}
    (hℓ : 1 < ℓ) (hf : fallback ≠ 0)
    (hR : 0 < R) (hr : 0 < r) (hL : 0 < L) (hτ : 0 < τ) (hτcap : τ ≤ L * R)
    (hrR : r ≤ R) (hc : ‖c‖ ≤ L)
    (houter : KSFullManuscriptAffinePSD.target D ⊆ Metric.closedBall 0 R)
    (hinner : Metric.closedBall z r ⊆ KSFullManuscriptAffinePSD.target D)
    (hx : x ∈ KSFullManuscriptAffinePSD.target D)
    (hmax : ∀ y ∈ KSFullManuscriptAffinePSD.target D, objective c b y ≤ objective c b x)
    (hω : 0 < ω) (hτω : τ ≤ ω / 4) {interval : KSFullManuscriptBisection.Interval}
    (hinterval : KSFullManuscriptBisection.Contains interval (objective c b x)) :
    |report D c fallback b R r L τ ω interval - objective c b x| ≤ ω := by
  exact KSFullManuscriptBisection.report_accuracy _ hω hτ.le hτω
    (correctFeasibility D c fallback z x hℓ hf hR hr hL hτ hτcap hrR hc
      houter hinner hx hmax) hinterval

end MatrixSpencer.KSFullManuscriptWeakOptimization
