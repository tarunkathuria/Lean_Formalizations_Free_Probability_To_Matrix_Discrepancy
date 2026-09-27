import MatrixSpencer.MSManuscriptAffineJointBoundsScaled
import MatrixSpencer.RectangularRidgeNumericalParameters

/-! Polynomial scalar bounds for the source-fidelity derivative cap and its
optimizer-response correction. These lemmas evaluate the existing explicit cap;
they do not postulate a bound on an unspecified derivative. -/

noncomputable section
namespace MatrixSpencer.RectangularRidgeCovarianceBudget
open RectangularRidgeNumericalParameters
set_option exponentiation.threshold 2048
set_option maxRecDepth 4096

variable {ι n : Type*} [Fintype ι] [Fintype n]

theorem valueCap_le {N R L : ℝ} (hN : 1 ≤ N)
    (hi : (Fintype.card ι : ℝ) ≤ N) (hn : (Fintype.card n : ℝ) ≤ N)
    (hR : 0 ≤ R) (hRN : R ≤ N) (hL : 0 ≤ L) (hLN : L ≤ N) :
    MSManuscriptComplexValueBoundScaled.valueCap ι n R 0 L ≤ big N 3 3 := by
  have hN0 : 0 ≤ N := by linarith
  have hprod : (Fintype.card ι : ℝ) * L ≤ N^2 := by
    simpa [pow_two] using mul_le_mul hi hLN hL hN0
  have hs : Real.sqrt (2 * (4 * (Fintype.card ι : ℝ)^2 * L^2)) ≤
      3 * (Fintype.card ι : ℝ) * L := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [sq_nonneg ((Fintype.card ι : ℝ)*L)]
  have hs' : Real.sqrt (2 * (4 * (Fintype.card ι : ℝ)^2 * L^2)) ≤ 3*N^2 :=
    hs.trans (by nlinarith)
  have hh : (Fintype.card n : ℝ)*R ≤ N^2 := by
    simpa [pow_two] using mul_le_mul hn hRN hR hN0
  have hf := mul_le_mul hn hs' (Real.sqrt_nonneg _) hN0
  have hpow : N^2 ≤ N^3 := pow_le_pow_right₀ hN (by omega)
  unfold MSManuscriptComplexValueBoundScaled.valueCap KSComplexObjectiveBound.valueCap big
  norm_num only [zero_mul, add_zero, Nat.reducePow]
  nlinarith

theorem radius_inverse_le {N γ μ : ℝ} (hN : 1 ≤ N)
    (hγ : ((2:ℝ)^15)⁻¹ ≤ γ) (hμ : densityFloor N ≤ μ) :
    10 / MSManuscriptComplexSourceDomain.radius γ μ ≤ big N 36 6 := by
  have hN0 : 0 < N := by linarith
  have hμ0 : 0 < μ := lt_of_lt_of_le (small_pos hN0 10 6) hμ
  have hm := mul_le_mul hγ hμ (small_pos hN0 10 6).le (by positivity : 0 ≤ γ)
  have hr : small N 32 6 ≤ MSManuscriptComplexSourceDomain.radius γ μ := by
    calc
      small N 32 6 = (((2:ℝ)^15)⁻¹ * densityFloor N) / 128 := by
        simp [small, big, densityFloor, mul_inv_rev]
        ring
      _ ≤ γ*μ/128 := div_le_div_of_nonneg_right hm (by norm_num)
      _ = _ := rfl
  calc
    10 / MSManuscriptComplexSourceDomain.radius γ μ ≤ 10 / small N 32 6 :=
      div_le_div_of_nonneg_left (by norm_num) (small_pos hN0 32 6) hr
    _ = 10 * big N 32 6 := by simp [small, div_eq_mul_inv]
    _ ≤ 16 * big N 32 6 := by nlinarith [big_pos hN0 32 6]
    _ = big N 36 6 := by norm_num [big]; ring

theorem jointCap_le {N R γ μ L : ℝ} (hN : 1 ≤ N)
    (hi : (Fintype.card ι : ℝ) ≤ N) (hn : (Fintype.card n : ℝ) ≤ N)
    (hR : 0 ≤ R) (hRN : R ≤ N) (hL : 0 ≤ L) (hLN : L ≤ N)
    (hγ : ((2:ℝ)^15)⁻¹ ≤ γ) (hμ : densityFloor N ≤ μ) :
    MSManuscriptAffineJointBoundsScaled.jointCap ι n R 0 γ μ L ≤ big N 147 27 := by
  have hN0 : 0 < N := by linarith
  have hγ0 : 0 < γ := lt_of_lt_of_le (by positivity) hγ
  have hμ0 : 0 < μ := lt_of_lt_of_le (small_pos hN0 10 6) hμ
  have hp : 0 ≤ 10 / MSManuscriptComplexSourceDomain.radius γ μ := by
    unfold MSManuscriptComplexSourceDomain.radius
    positivity
  have hb := radius_inverse_le hN hγ hμ
  have hp4 : (10 / MSManuscriptComplexSourceDomain.radius γ μ)^4 ≤ big N 144 24 := by
    calc
      _ ≤ (big N 36 6)^4 := pow_le_pow_left₀ hp hb 4
      _ = _ := by simp only [big, mul_pow, ← pow_mul]
  unfold MSManuscriptAffineJointBoundsScaled.jointCap
  calc
    _ ≤ big N 3 3 * big N 144 24 :=
      mul_le_mul (valueCap_le hN hi hn hR hRN hL hLN) hp4 (by positivity)
        (big_pos hN0 3 3).le
    _ = _ := big_mul N 3 3 144 24

theorem optimized_covariance_cap_le {N R γ μ L κ : ℝ} (hN : 1 ≤ N)
    (hi : (Fintype.card ι : ℝ) ≤ N) (hn : (Fintype.card n : ℝ) ≤ N)
    (hR : 0 ≤ R) (hRN : R ≤ N) (hL : 0 ≤ L) (hLN : L ≤ N)
    (hγ : ((2:ℝ)^15)⁻¹ ≤ γ) (hμ : densityFloor N ≤ μ) (hκ : N⁻¹ ≤ κ) :
    let B := MSManuscriptAffineJointBoundsScaled.jointCap ι n R 0 γ μ L
    B * (1 + B / (κ/2)) ≤ covarianceCap N := by
  classical
  let B := MSManuscriptAffineJointBoundsScaled.jointCap ι n R 0 γ μ L
  have hN0 : 0 < N := by linarith
  have hκ0 : 0 < κ := lt_of_lt_of_le (inv_pos.mpr hN0) hκ
  have hB0 : 0 ≤ B := mul_nonneg
    (MSManuscriptComplexValueBoundScaled.valueCap_nonneg hR (by norm_num)) (by positivity)
  have hB : B ≤ big N 147 27 := jointCap_le hN hi hn hR hRN hL hLN hγ hμ
  have hNk : 1 ≤ N*κ := by
    have hh := mul_le_mul_of_nonneg_left hκ hN0.le
    simpa [ne_of_gt hN0] using hh
  have hik : (κ/2)⁻¹ ≤ 2*N := (inv_le_iff_one_le_mul₀ (by positivity)).2 (by nlinarith)
  have hdiv : B / (κ/2) ≤ big N 148 28 := by
    calc
      _ ≤ big N 147 27 * (2*N) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul hB hik (by positivity) (big_pos hN0 147 27).le
      _ = big N 147 27 * big N 1 1 := by simp [big]
      _ = _ := big_mul N 147 27 1 1
  have hsum : 1 + B / (κ/2) ≤ big N 149 28 := by
    calc
      _ ≤ 2 * big N 148 28 := by linarith [big_one_le hN 148 28]
      _ = big N 1 0 * big N 148 28 := by simp [big]
      _ = _ := big_mul N 1 0 148 28
  change B * (1 + B / (κ/2)) ≤ covarianceCap N
  calc
    _ ≤ big N 147 27 * big N 149 28 :=
      mul_le_mul hB hsum (by positivity) (big_pos hN0 147 27).le
    _ = big N 296 55 := big_mul N 147 27 149 28
    _ ≤ covarianceCap N := big_mono hN (by omega) (by omega)

end MatrixSpencer.RectangularRidgeCovarianceBudget
