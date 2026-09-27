import MatrixSpencer.RectangularRidgePrimitiveParameters
import MatrixSpencer.RectangularRidgeNumericalOptimizerFloor

/-! Coarse polynomial magnitude bounds for the actual integer-tuned exponent
and regularizer weight. These avoid substituting the old logarithmic tuning. -/
noncomputable section
namespace MatrixSpencer.RectangularRidgePrimitiveMagnitude
open RectangularRidgePrimitiveParameters RectangularRidgeTuning
open RectangularRidgeNumericalOptimizerFloor (size)

theorem order_le_eight_size {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    (2 : ℝ) ^ depth N D hN ≤ 8 * size D N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hnp : (0 : ℝ) < N := by linarith
  have hdr : (D : ℝ)/N ≤ D := by
    apply (div_le_iff₀ hnp).mpr
    nlinarith
  have hlog : Real.log ((D : ℝ)/N) ≤ D :=
    (Real.log_le_self (by positivity)).trans hdr
  have hb := (logarithmic_bounds hN hND).2
  have he : (order N D hN : ℝ) = (2 : ℝ)^depth N D hN := by simp [order]
  rw [he] at hb
  dsimp [size]
  linarith

theorem weight_add_ridge_le {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    weight N D hN + 1/(D : ℝ) ≤ 128 * size D N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hq := exponent_positive N D hN
  have hq1 := exponent_le_half N D hN
  have ht := weight_positive hN hND
  have hp : 1 ≤ (D : ℝ)^exponent N D hN := Real.one_le_rpow hd hq.le
  have hmul : weight N D hN ≤ weight N D hN * (D : ℝ)^exponent N D hN := by
    simpa using mul_le_mul_of_nonneg_left hp ht.le
  have hlow : weight N D hN ≤ weight N D hN * (D : ℝ)^exponent N D hN /
      (1-exponent N D hN) := by
    apply (le_div_iff₀ (by linarith : 0 < 1-exponent N D hN)).mpr
    nlinarith [mul_nonneg ht.le hq.le]
  have hb := hlow.trans (regularizer_budget_le hN hND)
  have hk : 1/(D : ℝ) ≤ 1 := (one_div_le_one_div_of_le (by norm_num) hd).trans_eq (by norm_num)
  dsimp [RectangularRidgeParameters.size] at hb
  dsimp [size]
  linarith

end MatrixSpencer.RectangularRidgePrimitiveMagnitude
