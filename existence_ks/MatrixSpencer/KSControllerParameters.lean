import MatrixSpencer.KSDebitWalkQuality
import MatrixSpencer.KSNumericalHessian

/-!
# Explicit scalar parameters for the finite debit walk

The formulas cover zero original labels without division by zero. They
provide a positive movement step, the Taylor-error allowance, the entropy
drift budget and a positive finite cutoff. The meaning of `M` as an actual
uniform fourth-derivative bound remains a separate analytic obligation.
-/

noncomputable section
namespace MatrixSpencer.KSControllerParameters

def curvatureTolerance (N : ℕ) (δ : ℝ) : ℝ := δ / (100 * ((N : ℝ) + 1))
def hessianRadius (δ : ℝ) : ℝ := δ / 16
def movementStep (N : ℕ) (δ M : ℝ) : ℝ :=
  min (δ / 4) (Real.sqrt (curvatureTolerance N δ / (M + 1)))
def driftCoefficient (N : ℕ) (δ : ℝ) : ℝ := 4 * curvatureTolerance N δ
def cutoff (N : ℕ) (δ M : ℝ) : ℕ :=
  max 1 ⌈16 * (N : ℝ) / movementStep N δ M ^ 2⌉₊

theorem curvatureTolerance_pos (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 < curvatureTolerance N δ := by unfold curvatureTolerance; positivity

theorem hessianRadius_pos {δ : ℝ} (hδ : 0 < δ) : 0 < hessianRadius δ := by
  unfold hessianRadius
  positivity

theorem movementStep_pos (N : ℕ) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) :
    0 < movementStep N δ M := by
  have hκ := curvatureTolerance_pos N hδ
  unfold movementStep
  positivity

theorem movementStep_le_quarter (N : ℕ) (δ M : ℝ) : movementStep N δ M ≤ δ / 4 :=
  min_le_left _ _

theorem movementStep_square_bound (N : ℕ) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) :
    M * movementStep N δ M ^ 2 ≤ curvatureTolerance N δ := by
  have ht := movementStep_pos N hδ hM
  have hκ := curvatureTolerance_pos N hδ
  have hden : 0 < M + 1 := by linarith
  have hs := min_le_right (δ / 4) (Real.sqrt (curvatureTolerance N δ / (M + 1)))
  change movementStep N δ M ≤ Real.sqrt (curvatureTolerance N δ / (M + 1)) at hs
  have hsq : movementStep N δ M ^ 2 ≤ curvatureTolerance N δ / (M + 1) := by
    have hr := Real.sq_sqrt (div_nonneg hκ.le hden.le)
    nlinarith [Real.sqrt_nonneg (curvatureTolerance N δ / (M + 1))]
  have hp := (le_div_iff₀ hden).mp hsq
  nlinarith [sq_nonneg (movementStep N δ M)]

/-- The actual `3κ` Rayleigh allowance and fourth-order remainder fit in
the chosen per-movement drift coefficient. -/
theorem movement_drift_budget (N : ℕ) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) :
    3 * curvatureTolerance N δ / 2 + M * movementStep N δ M ^ 2 / 24 ≤
      driftCoefficient N δ := by
  have h := movementStep_square_bound N hδ hM
  have hκ := curvatureTolerance_pos N hδ
  unfold driftCoefficient
  linarith

theorem driftCoefficient_nonneg (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ driftCoefficient N δ := by
  have hκ := curvatureTolerance_pos N hδ
  unfold driftCoefficient
  positivity

/-- The entropy-telescoped potential cost fits the additional `δ` allowance. -/
theorem entropy_drift_budget (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    driftCoefficient N δ * (2 * (N : ℝ) * Real.log 2) ≤ δ := by
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hden : 0 < 100 * ((N : ℝ) + 1) := by positivity
  unfold driftCoefficient curvatureTolerance
  have hidentity : 4 * (δ / (100 * ((N : ℝ) + 1))) * (2 * (N : ℝ) * Real.log 2) =
      8 * δ * (N : ℝ) * Real.log 2 / (100 * ((N : ℝ) + 1)) := by ring
  rw [hidentity, div_le_iff₀ hden]
  have hl := mul_le_mul_of_nonneg_left hlog
    (by positivity : 0 ≤ 8 * δ * (N : ℝ))
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

theorem cutoff_pos (N : ℕ) (δ M : ℝ) : 0 < cutoff N δ M :=
  lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) (le_max_left _ _)

theorem cutoff_bound (N : ℕ) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) :
    16 * (N : ℝ) ≤ movementStep N δ M ^ 2 * (cutoff N δ M : ℝ) := by
  have ht := movementStep_pos N hδ hM
  have hceil := Nat.le_ceil (16 * (N : ℝ) / movementStep N δ M ^ 2)
  have hmax : (⌈16 * (N : ℝ) / movementStep N δ M ^ 2⌉₊ : ℝ) ≤ (cutoff N δ M : ℝ) :=
    Nat.cast_le.mpr (le_max_right _ _)
  have h := (div_le_iff₀ (sq_pos_of_pos ht)).mp (hceil.trans hmax)
  nlinarith

/-- The finite timeout probability's scalar upper bound is at most one eighth. -/
theorem entropy_cutoff_budget (N : ℕ) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) :
    2 * (N : ℝ) * Real.log 2 /
      (movementStep N δ M ^ 2 * (cutoff N δ M : ℝ)) ≤ 1 / 8 := by
  have ht := movementStep_pos N hδ hM
  have hT : 0 < (cutoff N δ M : ℝ) := Nat.cast_pos.mpr (cutoff_pos N δ M)
  have hden : 0 < movementStep N δ M ^ 2 * (cutoff N δ M : ℝ) := by positivity
  have hb := cutoff_bound N hδ hM
  have hlog : Real.log 2 ≤ 1 := by
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hl
    exact hl
  have hn := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 * (N : ℝ))
  rw [div_le_iff₀ hden]
  nlinarith

end MatrixSpencer.KSControllerParameters
