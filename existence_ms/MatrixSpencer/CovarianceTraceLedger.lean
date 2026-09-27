import MatrixSpencer.CovarianceMovement
import MatrixSpencer.FiniteProcessMoments

/-!
# Exact finite trace ledger for movements and cleaning

The operational time is the sum of squared mesh sizes. No exponential
lower bound or infinite process is needed for this accounting.
-/

open scoped BigOperators MatrixOrder
open Matrix
namespace MatrixSpencer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem realTrace_le_card_of_le_one {Q : Matrix ι ι ℝ} (hQ : Q ≤ 1) :
    realTrace Q ≤ Fintype.card ι := by
  have hh := realTrace_mul_mono (Matrix.PosSemidef.one : (1 : Matrix ι ι ℝ).PosSemidef) hQ
  simpa [realTrace] using hh

/-- Exact pathwise ledger for an arbitrary finite sequence of actual matrix updates. -/
theorem covariance_trace_ledger (C Q R : ℕ → Matrix ι ι ℝ) (h : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ j < N, C (j + 1) = C j - h j ^ 2 • Q j - R j) :
    realTrace (C N) = realTrace (C 0) -
      (∑ j ∈ Finset.range N, h j ^ 2 * realTrace (Q j)) -
      ∑ j ∈ Finset.range N, realTrace (R j) := by
  have hh := FiniteProcessMoments.telescope_eq (fun j => realTrace (C j))
    (fun j => -(h j ^ 2 * realTrace (Q j)) - realTrace (R j)) N
    (fun j hj => by dsimp only; rw [hstep j hj]; simp; ring)
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hh
  linarith

theorem covariance_trace_ledger_lower (C Q R : ℕ → Matrix ι ι ℝ)
    (h : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ j < N, C (j + 1) = C j - h j ^ 2 • Q j - R j)
    (hQ : ∀ j < N, Q j ≤ 1) :
    realTrace (C 0) - (Fintype.card ι : ℝ) * (∑ j ∈ Finset.range N, h j ^ 2) -
      (∑ j ∈ Finset.range N, realTrace (R j)) ≤ realTrace (C N) := by
  have hb : (∑ j ∈ Finset.range N, h j ^ 2 * realTrace (Q j)) ≤
      (Fintype.card ι : ℝ) * ∑ j ∈ Finset.range N, h j ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (realTrace_le_card_of_le_one (hQ j (Finset.mem_range.mp hj))) (sq_nonneg (h j))
  rw [covariance_trace_ledger C Q R h N hstep]
  linarith

theorem covariance_trace_before_time_limit (C Q R : ℕ → Matrix ι ι ℝ)
    (h : ℕ → ℝ) (N : ℕ) (hC0 : C 0 = 1)
    (hstep : ∀ j < N, C (j + 1) = C j - h j ^ 2 • Q j - R j)
    (hQ : ∀ j < N, Q j ≤ 1)
    (htime : (∑ j ∈ Finset.range N, h j ^ 2) ≤ (1 / 2 : ℝ)) :
    (Fintype.card ι : ℝ) / 8 - (∑ j ∈ Finset.range N, realTrace (R j)) ≤
      realTrace (C N) := by
  have hh := covariance_trace_ledger_lower C Q R h N hstep hQ
  have hinit : realTrace (C 0) = (Fintype.card ι : ℝ) := by simp [hC0, realTrace]
  rw [hinit] at hh
  have hmul := mul_le_mul_of_nonneg_left htime (Nat.cast_nonneg (Fintype.card ι) :
    (0 : ℝ) ≤ (Fintype.card ι : ℝ))
  have hc : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- The epoch stopping thresholds leave positive movement variance. -/
theorem movement_trace_positive_of_ledger {ell dc f q : ℝ}
    (hell : 32 ≤ ell) (hdc : dc ≤ ell / 64) (hf : f ≤ ell / 64)
    (hq : ell / 8 - dc - f - 1 ≤ q) : ell / 16 ≤ q ∧ 0 < q := by
  constructor <;> linarith

end MatrixSpencer
