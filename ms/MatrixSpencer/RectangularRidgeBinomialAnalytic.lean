import MatrixSpencer.RectangularRidgeTracePowerAnalytic
import MatrixSpencer.KSComplexObjectiveBound
import MatrixSpencer.KSCompactResolvent
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Constructed uniform analytic binomial series

For every real exponent in `[0,1]`, all binomial coefficients have modulus
at most one. The actual matrix power series consequently has radius at
least one and a geometric norm bound independent of the exponent. Its
trace is holomorphic on `‖S-1‖ < 1`.

This file constructs the series; agreement with the actual dyadic matrix
power on positive definite densities is a separate remaining identity.
-/

open Matrix Set Metric
open scoped BigOperators Matrix.Norms.L2Operator Topology ENNReal NNReal ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeBinomialAnalytic

/-- The scalar coefficient recursion, over the reals. -/
theorem choose_recurrence (α : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * Ring.choose α (k + 1) = Ring.choose α k * (α - k) := by
  have h := Ring.choose_smul_choose α (n := k + 1) (k := k) (Nat.le_succ k)
  simpa only [Nat.choose_succ_self_right, Nat.add_sub_cancel_left,
    Ring.choose_one_right, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using h

/-- Uniform coefficient bound, with no inverse exponent. -/
theorem abs_choose_le_one {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (k : ℕ) :
    |Ring.choose α k| ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he := congrArg abs (choose_recurrence α k)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hp : 0 < (k : ℝ) + 1 := by positivity
    rw [abs_mul, abs_of_pos hp, abs_mul] at he
    have hc : |α - (k : ℝ)| ≤ (k : ℝ) + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hm := mul_le_mul ih hc (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    rw [one_mul] at hm
    rw [← he] at hm
    nlinarith

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

def series (α : ℝ) : FormalMultilinearSeries ℂ (Matrix n n ℂ) (Matrix n n ℂ) :=
  .ofScalars _ (fun k => ((Ring.choose α k : ℝ) : ℂ))

def matrixSeries (α : ℝ) (X : Matrix n n ℂ) : Matrix n n ℂ := (series α).sum X

def tracePowerSeries (α : ℝ) (S : Matrix n n ℂ) : ℂ :=
  Matrix.trace (matrixSeries α (S - 1))

theorem coefficient_norm_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (k : ℕ) :
    ‖((Ring.choose α k : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_choose_le_one hα0 hα1 k

section Nonempty
variable [Nonempty n]

/-- The actual matrix series converges on the unit ball for every exponent in `[0,1]`. -/
theorem one_le_radius {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (1 : ℝ≥0∞) ≤ (series (n := n) α).radius := by
  apply (series (n := n) α).le_radius_of_bound (C := 1) (r := 1)
  intro k
  simp only [series, FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one,
    one_pow, mul_one]
  exact coefficient_norm_le hα0 hα1 k

/-- Constructed analyticity, not a supplied hypothesis about matrix powers. -/
theorem analyticAt_matrixSeries {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {X : Matrix n n ℂ} (hX : ‖X‖ < 1) : AnalyticAt ℂ (matrixSeries α) X := by
  have hr := one_le_radius (n := n) hα0 hα1
  have hp := (series (n := n) α).hasFPowerSeriesOnBall (lt_of_lt_of_le (by norm_num) hr)
  apply hp.analyticOnNhd
  rw [mem_emetric_ball_zero_iff]
  apply lt_of_lt_of_le _ hr
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr hX

omit [Nonempty n] in
theorem matrixSeries_eq_tsum (α : ℝ) (X : Matrix n n ℂ) :
    matrixSeries α X = ∑' k, ((Ring.choose α k : ℝ) : ℂ) • X ^ k := by
  exact FormalMultilinearSeries.ofScalars_sum_eq _ _

theorem term_norm_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (X : Matrix n n ℂ) (k : ℕ) :
    ‖((Ring.choose α k : ℝ) : ℂ) • X ^ k‖ ≤ ‖X‖ ^ k := by
  rw [norm_smul]
  exact (mul_le_mul (coefficient_norm_le hα0 hα1 k) (norm_pow_le X k)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)

/-- Direct geometric norm cap for the constructed series. -/
theorem matrixSeries_norm_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {X : Matrix n n ℂ} (hX : ‖X‖ < 1) :
    ‖matrixSeries α X‖ ≤ (1 - ‖X‖)⁻¹ := by
  have hg := summable_geometric_of_lt_one (norm_nonneg X) hX
  have ht : Summable (fun k => ‖((Ring.choose α k : ℝ) : ℂ) • X ^ k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (term_norm_le hα0 hα1 X) hg
  rw [matrixSeries_eq_tsum]
  exact (norm_tsum_le_tsum_norm ht).trans
    ((ht.tsum_le_tsum (term_norm_le hα0 hα1 X) hg).trans_eq
      (tsum_geometric_of_lt_one (norm_nonneg X) hX))

/-- The trace extension is holomorphic on a concrete, order-independent domain. -/
theorem analyticAt_tracePowerSeries {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {S : Matrix n n ℂ} (hS : ‖S - 1‖ < 1) :
    AnalyticAt ℂ (tracePowerSeries α) S := by
  have hm := (analyticAt_matrixSeries hα0 hα1 hS).comp
    (f := fun T : Matrix n n ℂ => T - 1) (analyticAt_id.sub analyticAt_const)
  exact (KSCompactResolvent.traceCLM (n := n)).analyticAt _ |>.comp hm

/-- Trace value cap for that actual analytic extension. -/
theorem tracePowerSeries_norm_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {S : Matrix n n ℂ} (hS : ‖S - 1‖ < 1) :
    ‖tracePowerSeries α S‖ ≤ (Fintype.card n : ℝ) * (1 - ‖S - 1‖)⁻¹ := by
  exact (KSComplexObjectiveBound.norm_trace_le_card_mul_norm _).trans
    (mul_le_mul_of_nonneg_left (matrixSeries_norm_le hα0 hα1 hS) (Nat.cast_nonneg _))


omit [Nonempty n] in
/-- A norm gap at the real center gives an explicit common complex neighborhood. -/
theorem norm_sub_one_lt_of_mem_ball {S T : Matrix n n ℂ} {μ : ℝ}
    (_hμ : 0 < μ) (hS : ‖S - 1‖ ≤ 1 - μ) (hT : T ∈ ball S (μ / 2)) :
    ‖T - 1‖ < 1 - μ / 2 := by
  have ht : ‖T - S‖ < μ / 2 := by simpa only [mem_ball, dist_eq_norm] using hT
  have he : T - 1 = (T - S) + (S - 1) := by abel
  have hh : ‖T - 1‖ ≤ ‖T - S‖ + ‖S - 1‖ := by rw [he]; exact norm_add_le _ _
  linarith

/-- Explicit value cap on that neighborhood, independent of the exponent. -/
theorem tracePowerSeries_ball_bound {α μ : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hμ : 0 < μ) {S T : Matrix n n ℂ} (hS : ‖S - 1‖ ≤ 1 - μ)
    (hT : T ∈ ball S (μ / 2)) :
    ‖tracePowerSeries α T‖ ≤ (Fintype.card n : ℝ) * (2 / μ) := by
  have hn := norm_sub_one_lt_of_mem_ball hμ hS hT
  have ht : ‖T - 1‖ < 1 := by linarith
  apply (tracePowerSeries_norm_le hα0 hα1 ht).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hi := one_div_le_one_div_of_le (by positivity : 0 < μ / 2)
    (by linarith : μ / 2 ≤ 1 - ‖T - 1‖)
  convert hi using 1 <;> ring

/-- Actual second through fourth derivatives of the constructed trace series.
The exponent enters only the harmless hypothesis `α ∈ [0,1]`. -/
theorem tracePowerSeries_iterated_derivative_bound {α μ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    {S : Matrix n n ℂ} (hS : ‖S - 1‖ ≤ 1 - μ) (k : ℕ)
    (hk2 : 2 ≤ k) (hk4 : k ≤ 4) :
    ‖iteratedFDeriv ℂ k (tracePowerSeries α) S‖ ≤
      ((Fintype.card n : ℝ) * (2 / μ)) * (20 / μ) ^ 4 := by
  have ha : AnalyticOnNhd ℂ (tracePowerSeries α) (ball S (μ / 2)) := by
    intro T hT
    apply analyticAt_tracePowerSeries hα0 hα1
    have ht := norm_sub_one_lt_of_mem_ball hμ hS hT
    linarith
  have hc : ContDiffOn ℂ ∞ (tracePowerSeries α) (ball S (μ / 2)) :=
    ha.contDiffOn isOpen_ball.uniqueDiffOn
  have hd := KSCauchyDerivatives.iterated_derivatives_le_common_cap
    (f := tracePowerSeries α) (x := S) (R := μ / 2)
    (K := (Fintype.card n : ℝ) * (2 / μ)) (by positivity) (by linarith)
    (by positivity) hc (fun T hT => tracePowerSeries_ball_bound hα0 hα1 hμ hS hT)
    k hk2 hk4
  convert hd using 1; ring

end Nonempty
end MatrixSpencer.RectangularRidgeBinomialAnalytic
