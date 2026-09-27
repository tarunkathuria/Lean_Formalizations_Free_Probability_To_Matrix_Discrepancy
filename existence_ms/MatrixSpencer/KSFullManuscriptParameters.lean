import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic



noncomputable section
namespace MatrixSpencer.KSFullManuscriptParameters

def signingScale : ℝ := 16 * Real.sqrt 2 + 5
def debitTolerance (N : ℕ) (δ : ℝ) : ℝ := δ / N
def curvatureTolerance (N : ℕ) (δ : ℝ) : ℝ := δ / (100 * N)
def queryStep (N : ℕ) (δ M : ℝ) : ℝ :=
  min (δ / (4 * Real.sqrt 2)) (Real.sqrt (curvatureTolerance N δ / (8 * N * M)))
def valueTolerance (N : ℕ) (δ M : ℝ) : ℝ :=
  curvatureTolerance N δ * queryStep N δ M ^ 2 / (16 * N)
def movementStep (N : ℕ) (δ M : ℝ) : ℝ :=
  min (δ / 4) (Real.sqrt (24 * curvatureTolerance N δ / M))
def driftCoefficient (N : ℕ) (δ : ℝ) : ℝ := δ / (25 * N)
def cutoff (N : ℕ) (δ M : ℝ) : ℕ :=
  ⌈16 * (N : ℝ) / movementStep N δ M ^ 2⌉₊

theorem signingScale_ge_one : 1 ≤ signingScale := by
  unfold signingScale
  nlinarith [Real.sqrt_nonneg 2]

theorem debitTolerance_pos {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) :
    0 < debitTolerance N δ := div_pos hδ (Nat.cast_pos.mpr hN)

theorem debitTolerance_budget {N : ℕ} (hN : 0 < N) (δ : ℝ) :
    (N : ℝ) * debitTolerance N δ = δ := by
  unfold debitTolerance
  field_simp [ne_of_gt (Nat.cast_pos.mpr hN : (0 : ℝ) < N)]

theorem curvatureTolerance_pos {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) :
    0 < curvatureTolerance N δ := by
  unfold curvatureTolerance
  exact div_pos hδ (mul_pos (by norm_num) (Nat.cast_pos.mpr hN))

theorem queryStep_pos {N : ℕ} (hN : 0 < N) {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 < M) : 0 < queryStep N δ M := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hκ := curvatureTolerance_pos hN hδ
  unfold queryStep
  positivity

theorem queryStep_margin (N : ℕ) (δ M : ℝ) :
    queryStep N δ M * Real.sqrt 2 ≤ δ / 4 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h := mul_le_mul_of_nonneg_right
    (min_le_left (δ / (4 * Real.sqrt 2)) (Real.sqrt (curvatureTolerance N δ / (8 * N * M)))) hs.le
  change queryStep N δ M * Real.sqrt 2 ≤ _ at h
  convert h using 1
  field_simp

theorem queryStep_square_bound {N : ℕ} (hN : 0 < N) {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 < M) :
    queryStep N δ M ^ 2 ≤ curvatureTolerance N δ / (8 * N * M) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hκ := curvatureTolerance_pos hN hδ
  have hden : 0 < 8 * (N : ℝ) * M := by positivity
  calc
    _ ≤ Real.sqrt (curvatureTolerance N δ / (8 * N * M)) ^ 2 :=
      pow_le_pow_left₀ (queryStep_pos hN hδ hM).le (min_le_right _ _) 2
    _ = _ := Real.sq_sqrt (div_nonneg hκ.le hden.le)

theorem valueTolerance_pos {N : ℕ} (hN : 0 < N) {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 < M) : 0 < valueTolerance N δ M := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hκ := curvatureTolerance_pos hN hδ
  have ht := queryStep_pos hN hδ hM
  unfold valueTolerance
  positivity


theorem hessian_entry_budget {N : ℕ} (hN : 0 < N) {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 < M) :
    2 * M * queryStep N δ M ^ 2 +
      4 * valueTolerance N δ M / queryStep N δ M ^ 2 ≤ curvatureTolerance N δ / (2 * N) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have ht := queryStep_pos hN hδ hM
  have hden : 0 < 8 * (N : ℝ) * M := by positivity
  have hs := (le_div_iff₀ hden).mp (queryStep_square_bound hN hδ hM)
  have hv : 4 * valueTolerance N δ M / queryStep N δ M ^ 2 =
      curvatureTolerance N δ / (4 * N) := by
    unfold valueTolerance
    field_simp
    ring
  rw [hv]
  apply (le_div_iff₀ (by positivity : 0 < 2 * (N : ℝ))).mpr
  have hid : curvatureTolerance N δ / (4 * N) * (2 * N) = curvatureTolerance N δ / 2 := by
    field_simp
    ring
  rw [add_mul, hid]
  nlinarith

theorem movementStep_pos {N : ℕ} (hN : 0 < N) {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 < M) : 0 < movementStep N δ M := by
  have hκ := curvatureTolerance_pos hN hδ
  unfold movementStep
  positivity

theorem movementStep_le_quarter (N : ℕ) (δ M : ℝ) : movementStep N δ M ≤ δ / 4 :=
  min_le_left _ _

theorem movement_remainder_budget {N : ℕ} (hN : 0 < N) {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 < M) :
    movementStep N δ M ^ 2 * M / 24 ≤ curvatureTolerance N δ := by
  have hκ := curvatureTolerance_pos hN hδ
  have hs : movementStep N δ M ^ 2 ≤ 24 * curvatureTolerance N δ / M := by
    calc
      _ ≤ Real.sqrt (24 * curvatureTolerance N δ / M) ^ 2 :=
        pow_le_pow_left₀ (movementStep_pos hN hδ hM).le (min_le_right _ _) 2
      _ = _ := Real.sq_sqrt (by positivity)
  have hb := (le_div_iff₀ hM).mp hs
  linarith

theorem movement_drift_budget {N : ℕ} (hN : 0 < N) {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 < M) :
    3 * curvatureTolerance N δ + movementStep N δ M ^ 2 * M / 24 ≤ driftCoefficient N δ := by
  have hb := movement_remainder_budget hN hδ hM
  have he : driftCoefficient N δ = 4 * curvatureTolerance N δ := by
    unfold driftCoefficient curvatureTolerance
    ring
  rw [he]
  linarith

theorem cutoff_bound {N : ℕ} (hN : 0 < N) {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 < M) :
    16 * (N : ℝ) ≤ movementStep N δ M ^ 2 * (cutoff N δ M : ℝ) := by
  have ht := movementStep_pos hN hδ hM
  have h := Nat.le_ceil (16 * (N : ℝ) / movementStep N δ M ^ 2)
  have hb := (div_le_iff₀ (sq_pos_of_pos ht)).mp h
  simpa only [cutoff, mul_comm] using hb

theorem cutoff_pos {N : ℕ} (hN : 0 < N) {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 < M) : 0 < cutoff N δ M := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hb := cutoff_bound hN hδ hM
  by_contra hc
  have hz : cutoff N δ M = 0 := by omega
  rw [hz, Nat.cast_zero, mul_zero] at hb
  linarith

end MatrixSpencer.KSFullManuscriptParameters
