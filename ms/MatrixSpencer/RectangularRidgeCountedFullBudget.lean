import MatrixSpencer.RectangularRidgeCountedFull
import MatrixSpencer.RectangularRidgeRetryParameters

/-! Polynomial outer execution accounting for the actual chosen epoch cap.
The accepted-epoch operation bound remains a scalar argument here, to be
replaced by the concrete compiled trial/retry/acceptance polynomial. -/
namespace MatrixSpencer.RectangularRidgeCountedFullBudget
open RectangularRidgeRetryParameters RectangularRidgePhaseProgress

theorem operations_le {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) (B : ℕ) :
    RectangularRidgeCountedFull.operations N (epochCalls N D hN) B ≤
      selected N D * (B + 83 * N + 79) := by
  have hc := total_calls_le hN hND
  have hn := count_succ_le_selected N D
  have hM : 1 ≤ selected N D := by omega
  have hfirst := Nat.mul_le_mul_right (B + 44 * N + 39) hc
  have hsecond := Nat.mul_le_mul_right (39 * N + 36) hn
  have hthird := Nat.mul_le_mul_left 4 hM
  unfold RectangularRidgeCountedFull.operations
  nlinarith

theorem draws_le {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) (R : ℕ) :
    (N + 1) * (epochCalls N D hN * R) ≤ selected N D * R := by
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right R (total_calls_le hN hND)

end MatrixSpencer.RectangularRidgeCountedFullBudget
