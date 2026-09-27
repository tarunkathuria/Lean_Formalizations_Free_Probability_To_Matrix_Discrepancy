import MatrixSpencer.RectangularRidgeNumericalParameters

/-! Arithmetic validation of the selected-prefix rounding ledger. The number
of events in a trial and the number of selected epochs are given their concrete
polynomial caps. The separate walk proof must establish that its executions
obey these caps. Matrix arithmetic and repeated rejected trials are not omitted
from a claimed total work bound: this file makes no such work claim. -/

noncomputable section
namespace MatrixSpencer.RectangularRidgePrefixBudget
open RectangularRidgeNumericalParameters
set_option exponentiation.threshold 2048

def trialEvents (N : ℝ) : ℝ := big N 1080 208 + big N 320 63 + N + 1

lemma big_double (N : ℝ) (a b : ℕ) : 2*big N a b = big N (a+1) b := by
  unfold big
  rw [pow_succ]
  ring

theorem paid_count_scale (N : ℝ) : N/paidStep N = big N 320 63 := by
  simp only [paidStep, small, div_inv_eq_mul]
  change N*big N 320 62 = _
  unfold big
  rw [show (63:ℕ)=62+1 by omega, pow_succ]
  ring

theorem movements_scale (N : ℝ) : (mesh N^2)⁻¹ = big N 1080 208 := by
  rw [mesh_squared]
  simp [small]

theorem trialEvents_le {N : ℝ} (hN : 1≤N) : trialEvents N ≤ big N 1081 208 := by
  have hn : N ≤ big N 320 63 := by
    simpa [big] using big_mono hN (show 0≤320 by omega) (show 1≤63 by omega)
  have h1 := big_one_le hN 320 63
  have h0 := (big_pos (by linarith : 0<N) 320 63).le
  have hrest : big N 320 63+N+1 ≤ big N 1080 208 := by
    calc
      _ ≤ 4*big N 320 63 := by linarith
      _ = big N 322 63 := by rw [show (4:ℝ)=2*2 by norm_num, mul_assoc,
        big_double, big_double]
      _ ≤ big N 1080 208 := big_mono hN (by omega) (by omega)
  calc
    trialEvents N = big N 1080 208+(big N 320 63+N+1) := by unfold trialEvents; ring
    _ ≤ 2*big N 1080 208 := by linarith
    _ = big N 1081 208 := big_double N 1080 208

theorem selectedEpochs_add_one_le {N : ℝ} (hN : 1≤N) :
    selectedEpochs N+1 ≤ big N 23 4 := by
  have h1 := big_one_le hN 22 4
  calc
    selectedEpochs N+1 ≤ 2*big N 22 4 := by unfold selectedEpochs; linarith
    _ = big N 23 4 := big_double N 22 4

/-- The rounding budget covers ten scalar state/certificate actions per
input coordinate at each structural event, over all selected epochs and one
extra trial. This is stronger than simply counting the structural events. -/
theorem prefix_rounding_budget {N : ℝ} (hN : 1≤N) :
    10*N*(selectedEpochs N+1)*trialEvents N ≤ prefixUpdates N := by
  have hN0 : 0<N := by linarith
  have hfac : 10*N ≤ big N 4 1 := by norm_num [big]; linarith
  have hep := selectedEpochs_add_one_le hN
  have hev := trialEvents_le hN
  have hev0 : 0≤trialEvents N := by
    exact add_nonneg (add_nonneg (add_nonneg (big_pos hN0 1080 208).le
      (big_pos hN0 320 63).le) hN0.le) zero_le_one
  have hep0 : 0≤selectedEpochs N+1 := by
    exact add_nonneg (big_pos hN0 22 4).le zero_le_one
  calc
    _ ≤ big N 4 1*big N 23 4*big N 1081 208 :=
      mul_le_mul (mul_le_mul hfac hep hep0 (big_pos hN0 4 1).le)
        hev hev0 (mul_nonneg (big_pos hN0 4 1).le (big_pos hN0 23 4).le)
    _ = big N 1108 213 := by rw [big_mul, big_mul]
    _ ≤ prefixUpdates N := big_mono hN (by omega) (by omega)

end MatrixSpencer.RectangularRidgePrefixBudget
