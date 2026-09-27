import MatrixSpencer.KSObjectiveUpper

/-!
# Explicit finite projected-optimizer parameters

All scalar choices use the supplied curvature constants and requested
distance accuracy. The count uses the proved density diameter bound `2`,
not the unknown distance to an optimizer. The actual objective's upper
Hessian input is discharged by its explicit source-budget and floor bound.

The accuracy and feasibility of the gradient and projection reports remain
explicit inputs to the finite iteration theorem. This module chooses their
positive tolerances and does not replace those reports by exact oracles.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSOptimizerParameters

def step (μ L : ℝ) : ℝ := μ / L ^ 2
def factor (μ L : ℝ) : ℝ := Real.sqrt (1 - (μ / L) ^ 2)
def projectionError (μ L τ : ℝ) : ℝ := (1 - factor μ L) * τ / 4
def gradientError (μ L τ : ℝ) : ℝ := (1 - factor μ L) * τ / (4 * step μ L)
def count (μ L τ : ℝ) : ℕ := KSInexactIteration.iterationCount (factor μ L) 2 τ

theorem parameters {μ L : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) :
    0 < step μ L ∧ 0 ≤ factor μ L ∧ factor μ L < 1 ∧
      1 - 2 * step μ L * μ + step μ L ^ 2 * L ^ 2 ≤ factor μ L ^ 2 :=
  KSProjectedContraction.conservative_parameters hμ hμL

theorem projectionError_pos {μ L τ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) (hτ : 0 < τ) :
    0 < projectionError μ L τ :=
  div_pos (mul_pos (sub_pos.mpr (parameters hμ hμL).2.2.1) hτ) (by norm_num)

theorem gradientError_pos {μ L τ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) (hτ : 0 < τ) :
    0 < gradientError μ L τ :=
  div_pos (mul_pos (sub_pos.mpr (parameters hμ hμL).2.2.1) hτ)
    (mul_pos (by norm_num) (parameters hμ hμL).1)

theorem update_error_eq {μ L τ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) :
    projectionError μ L τ + step μ L * gradientError μ L τ =
      (1 - factor μ L) * τ / 2 := by
  have hs := (parameters hμ hμL).1.ne'
  unfold projectionError gradientError
  field_simp
  ring

theorem noise_floor_eq {μ L τ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) :
    (projectionError μ L τ + step μ L * gradientError μ L τ) / (1 - factor μ L) = τ / 2 := by
  rw [update_error_eq hμ hμL]
  have hq := (sub_pos.mpr (parameters hμ hμL).2.2.1).ne'
  field_simp

theorem rate_at_count_le {μ L τ D : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hτ : 0 < τ) (hD : D ≤ 2) :
    factor μ L ^ count μ L τ * D +
      (projectionError μ L τ + step μ L * gradientError μ L τ) / (1 - factor μ L) ≤ τ := by
  have hp := parameters hμ hμL
  have hg := KSInexactIteration.geometric_error_at_count hp.2.1 hp.2.2.1 hτ (2 : ℝ)
  have hd := mul_le_mul_of_nonneg_left hD (pow_nonneg hp.2.1 (count μ L τ))
  rw [noise_floor_eq hμ hμL]
  change factor μ L ^ count μ L τ * 2 ≤ τ / 2 at hg
  linarith

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open KSObjectiveChart KSInexactIteration

/-- Enlarging the explicit upper bound by the known strong-concavity
constant makes every scalar parameter valid without another spectral test. -/
def densityL (a κ θ : ℝ) : ℝ :=
  max (θ / 2) (KSObjectiveUpper.upperCoefficient (n := n) a κ θ 1)

omit [DecidableEq n] in
theorem densityL_pos {a κ θ : ℝ} (hθ : 0 < θ) : 0 < densityL (n := n) a κ θ :=
  lt_of_lt_of_le (div_pos hθ (by norm_num)) (le_max_left _ _)

theorem densityFloor_norm_le_one (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ))
    (hisometry : ∀ v, realTrace ((e v : Matrix n n ℂ) * (e v : Matrix n n ℂ)) = ‖v‖ ^ 2)
    {a : ℝ} (ha : 0 < a) {x : E} (hx : x ∈ densityFloor e a) : ‖x‖ ≤ 1 := by
  have hd : (e x : Matrix n n ℂ) ∈ densitySet := ⟨(densityFloor_posDef e ha hx).posSemidef, hx.2⟩
  have hsq := (realTrace_mul_density_le_norm (e x).property hd).trans (density_norm_le_one hd)
  rw [hisometry x] at hsq
  nlinarith [norm_nonneg x]

/-- The Frobenius-coordinate diameter bound is independent of the unknown
optimizer and therefore can be used in the actual iteration count. -/
theorem densityFloor_distance_le_two (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ))
    (hisometry : ∀ v, realTrace ((e v : Matrix n n ℂ) * (e v : Matrix n n ℂ)) = ‖v‖ ^ 2)
    {a : ℝ} (ha : 0 < a) {x y : E} (hx : x ∈ densityFloor e a) (hy : y ∈ densityFloor e a) :
    dist x y ≤ 2 :=
  (dist_le_norm_add_norm x y).trans (by
    have hx' := densityFloor_norm_le_one e hisometry ha hx
    have hy' := densityFloor_norm_le_one e hisometry ha hy
    linarith)

variable [CompleteSpace E]

/-- The actual finite approximate projected-gradient run reaches any
prescribed Frobenius distance accuracy with explicit parameters and count.
The two numerical report error guarantees remain visible hypotheses. -/
theorem inexact_density_run_accuracy (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ))
    (hisometry : ∀ v, realTrace ((e v : Matrix n n ℂ) * (e v : Matrix n n ℂ)) = ‖v‖ ^ 2)
    {a κ τ : ℝ} (ha : 0 < a) (hκ : 0 ≤ κ) (hτ : 0 < τ)
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ κ • (1 : Matrix n n ℂ))
    (hne : (densityFloor e a).Nonempty)
    (gradientReport projectionReport : ℕ → E → E) (x₀ xstar : E)
    (hstart : x₀ ∈ densityFloor e a) (hxstar : xstar ∈ densityFloor e a)
    (hmax : IsMaxOn (objective H B θ e) (densityFloor e a) xstar)
    (hfeasible : ∀ k z, projectionReport k z ∈ densityFloor e a)
    (hg : ∀ k x, x ∈ densityFloor e a →
      ‖gradientReport k x - gradient (objective H B θ e) x‖ ≤
        gradientError (θ / 2) (densityL (n := n) a κ θ) τ)
    (hp : ∀ k z, dist (projectionReport k z)
      (metricProjection (densityFloor e a) hne (densityFloor_isClosed e a).isComplete
        (densityFloor_convex e a) z) ≤ projectionError (θ / 2) (densityL (n := n) a κ θ) τ) :
    dist (projectedGradientIteration (step (θ / 2) (densityL (n := n) a κ θ))
      gradientReport projectionReport x₀ (count (θ / 2) (densityL (n := n) a κ θ) τ)) xstar ≤ τ := by
  have hμ : 0 < θ / 2 := div_pos hθ (by norm_num)
  have hμL : θ / 2 ≤ densityL (n := n) a κ θ := le_max_left _ _
  have hpar := parameters hμ hμL
  have hr := inexact_run_distance_le H B θ hθ e hisometry ha hne
    gradientReport projectionReport x₀ xstar (densityL_pos hθ).le hpar.1.le
    hpar.2.1 hpar.2.2.1 (gradientError_pos hμ hμL hτ).le
    (projectionError_pos hμ hμL hτ).le hstart hxstar hmax hpar.2.2.2
    (fun x hx => (KSObjectiveUpper.objective_floor_hessian_norm_le_explicit H B θ hθ e
      hisometry ha hκ hbudget x hx).trans (le_max_right _ _)) hfeasible hg hp
    (count (θ / 2) (densityL (n := n) a κ θ) τ)
  exact hr.trans (rate_at_count_le hμ hμL hτ (densityFloor_distance_le_two e hisometry ha hstart hxstar))

end MatrixSpencer.KSOptimizerParameters
