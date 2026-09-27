import MatrixSpencer.MSManuscriptProbability

/-! A conservative arithmetic retry count giving constant success for the
entire finite adaptive run. No logarithm or unknown success probability is
needed to choose the count. This is not a running-time theorem. -/
namespace MatrixSpencer.MSManuscriptRetryBudget

def retries (N K : ℕ) : ℕ := (N+1)*K+1

theorem count_pow_bound (t : ℕ) : ((t:ℝ)+1)*((1:ℝ)/2)^t ≤ 1 := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    rw [pow_succ]
    push_cast
    have hp : 0 ≤ ((1:ℝ)/2)^t := by positivity
    have ht : 0 ≤ (t:ℝ) := Nat.cast_nonneg t
    nlinarith

theorem failure_budget (N K : ℕ) :
    ((N+1:ℕ):ℝ)*(K:ℝ)*((1:ℝ)/2)^(retries N K) ≤ 1/2 := by
  let t := (N+1)*K
  have ht := count_pow_bound t
  have hp : 0 ≤ ((1:ℝ)/2)^t := by positivity
  change ((N+1:ℕ):ℝ)*(K:ℝ)*((1:ℝ)/2)^(t+1) ≤ _
  rw [pow_succ]
  have hc : (t:ℝ) = ((N+1:ℕ):ℝ)*(K:ℝ) := by simp [t]
  rw [← hc]
  nlinarith

end MatrixSpencer.MSManuscriptRetryBudget
