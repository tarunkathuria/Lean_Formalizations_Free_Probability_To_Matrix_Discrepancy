import MatrixSpencer.RectangularRidgeUniformResponse

/-! Scalar normalization of the fixed-parameter initial potential and all
geometrically decreasing live-set phase costs. This module supplies bounds
on these actual accounting expressions; it does not assume a successful run. -/
noncomputable section
namespace MatrixSpencer.RectangularRidgeSigningBudget
open RectangularRidgePrimitiveParameters RectangularRidgeUniformResponse

def scale (N D : ℕ) : ℝ := Real.sqrt ((N : ℝ) * (1 + Real.log ((D : ℝ) / N)))

def initialBudget (N D : ℕ) (hN : 1 ≤ N) : ℝ :=
  2 * Real.sqrt (N : ℝ) +
    (weight N D hN * (D : ℝ) ^ exponent N D hN / (1 - exponent N D hN) +
      2 * (1 / (D : ℝ)) * Real.sqrt (D : ℝ))

theorem sqrt_count_le_scale {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    Real.sqrt (N : ℝ) ≤ scale N D := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hr : (1 : ℝ) ≤ (D : ℝ) / N := by
    apply (le_div_iff₀ hn).mpr
    simpa using (Nat.cast_le.mpr hND : (N : ℝ) ≤ D)
  have hl := Real.log_nonneg hr
  apply Real.sqrt_le_sqrt
  nlinarith

theorem one_le_scale {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) : 1 ≤ scale N D :=
  (Real.le_sqrt_of_sq_le (by exact_mod_cast hN)).trans (sqrt_count_le_scale hN hND)

theorem ridge_cost_le {D : ℕ} (hD : 1 ≤ D) :
    2 * (1 / (D : ℝ)) * Real.sqrt (D : ℝ) ≤ 2 := by
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hs : Real.sqrt (D : ℝ) ≤ D := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * (1 / (D : ℝ)) by positivity)
  have he : 2 * (1 / (D : ℝ)) * (D : ℝ) = 2 := by field_simp
  exact hh.trans_eq he

theorem initialBudget_le {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    initialBudget N D hN ≤ 84 * scale N D := by
  have hb := RectangularRidgeTuning.optimized_budget_le hN hND
  change Real.sqrt (N : ℝ) + weight N D hN * (D : ℝ) ^ exponent N D hN /
    (1 - exponent N D hN) + (4096 : ℝ) ^ exponent N D hN *
      (N : ℝ) ^ (1 - exponent N D hN) / (weight N D hN * exponent N D hN) ≤
        81 * scale N D at hb
  have ht : 0 ≤ (4096 : ℝ) ^ exponent N D hN * (N : ℝ) ^ (1 - exponent N D hN) /
      (weight N D hN * exponent N D hN) := by
    have := weight_positive hN hND
    have := exponent_positive N D hN
    positivity
  have hr := ridge_cost_le (hN.trans hND)
  have hs := sqrt_count_le_scale hN hND
  have h1 := one_le_scale hN hND
  unfold initialBudget
  linarith

/-- Each phase has at most `152(B+1)` epochs at successful elapsed threshold half the operational duration, pays `K sqrt(live)` per
accepted epoch, and incurs at most `64 sqrt(live)` for final small-set rounding.
The geometric outer ledger multiplies this coefficient by four. -/
theorem totalBudget_le {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D)
    {K : ℝ} (hK : 0 ≤ K) :
    initialBudget N D hN +
      4 * (152 * K * (coefficient N D hN + 1) + 64) * Real.sqrt (N : ℝ) ≤
        (84 + 1944 * (152 * K + 64)) * scale N D := by
  have hi := initialBudget_le hN hND
  have hc := scaled_coefficient_le hN hND
  change (coefficient N D hN + 1) * Real.sqrt (N : ℝ) ≤ 486 * scale N D at hc
  have hB := coefficient_two_le hN hND
  have habsorb : 152 * K * (coefficient N D hN + 1) + 64 ≤
      (152 * K + 64) * (coefficient N D hN + 1) := by nlinarith
  have hfirst := mul_le_mul_of_nonneg_right habsorb (Real.sqrt_nonneg (N : ℝ))
  have hsecond := mul_le_mul_of_nonneg_left hc (show 0 ≤ 152 * K + 64 by positivity)
  nlinarith

end MatrixSpencer.RectangularRidgeSigningBudget
