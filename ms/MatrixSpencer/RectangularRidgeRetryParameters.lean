import MatrixSpencer.RectangularRidgePhaseProgress

/-! Explicit polynomial amplification. The retry count is deliberately
conservative: an integer dimension polynomial plus the desired number of
binary confidence digits. No logarithm, ceiling oracle, or bit model is used. -/
noncomputable section
namespace MatrixSpencer.RectangularRidgeRetryParameters

def selected (N D : ℕ) : ℕ := 2 ^ 22 * (D + N + 2) ^ 4

def retries (N D k : ℕ) : ℕ := selected N D + k + 1

theorem count_succ_le_selected (N D : ℕ) : N + 1 ≤ selected N D := by
  have hp : 1 ≤ D + N + 2 := by omega
  calc
    N + 1 ≤ D + N + 2 := by omega
    _ ≤ (D + N + 2) ^ 4 := le_self_pow hp (by norm_num)
    _ ≤ 2 ^ 22 * (D + N + 2) ^ 4 := Nat.le_mul_of_pos_left _ (by positivity)

theorem selected_cast (N D : ℕ) : (selected N D : ℝ) =
    RectangularRidgeNumericalParameters.selectedEpochs (RectangularRidgeNumericalOptimizerFloor.size D N) := by
  simp only [selected, RectangularRidgeNumericalParameters.selectedEpochs,
    RectangularRidgeNumericalParameters.big, RectangularRidgeNumericalOptimizerFloor.size,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]

theorem total_calls_le {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    (N + 1) * RectangularRidgePhaseProgress.epochCalls N D hN ≤ selected N D := by
  have hh := RectangularRidgePhaseProgress.total_epochCalls_le hN hND
  rw [← selected_cast] at hh
  exact_mod_cast hh

/-- Even linear rather than logarithmic dependence on the number of epoch
calls gives a polynomial retry count and exponential confidence. -/
theorem failure_amplification (M k : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    (M : ℝ) * q ^ (M + k + 1) ≤ (1 / 2 : ℝ) ^ k := by
  have hM : (M : ℝ) ≤ (2 : ℝ) ^ M := by
    have hnat : M ≤ 2 ^ M := by
      induction M with
      | zero => norm_num
      | succ M ih =>
        rw [pow_succ]
        have hp : 0 < 2 ^ M := by positivity
        omega
    exact_mod_cast hnat
  have hbase : (M : ℝ) * (1 / 2 : ℝ) ^ M ≤ 1 := by
    calc
      _ ≤ (2 : ℝ) ^ M * (1 / 2 : ℝ) ^ M :=
        mul_le_mul_of_nonneg_right hM (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  have hpow := pow_le_pow_left₀ hq0 hq (M + k + 1)
  have hh := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg M)
  have he : (M : ℝ) * (1 / 2 : ℝ) ^ (M + k + 1) =
      ((M : ℝ) * (1 / 2 : ℝ) ^ M) * (1 / 2 : ℝ) ^ k * (1 / 2) := by
    rw [pow_add, pow_add]
    ring
  rw [he] at hh
  have hb := mul_le_mul_of_nonneg_right hbase (show 0 ≤ (1 / 2 : ℝ) ^ k by positivity)
  nlinarith [show 0 ≤ (1 / 2 : ℝ) ^ k by positivity]

theorem total_failure_le {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) (k : ℕ) :
    (((N + 1) * RectangularRidgePhaseProgress.epochCalls N D hN : ℕ) : ℝ) *
      (19 / 50 : ℝ) ^ retries N D k ≤ (1 / 2 : ℝ) ^ k := by
  have hc : ((((N + 1) * RectangularRidgePhaseProgress.epochCalls N D hN) : ℕ) : ℝ) ≤
      selected N D := by exact_mod_cast total_calls_le hN hND
  exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans
    (failure_amplification (selected N D) k (by norm_num) (by norm_num))

theorem retries_polynomial (N D k : ℕ) :
    retries N D k = 2 ^ 22 * (D + N + 2) ^ 4 + k + 1 := rfl

end MatrixSpencer.RectangularRidgeRetryParameters
