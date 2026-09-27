import MatrixSpencer.RealRAMProgram
import Mathlib.Algebra.Order.Floor.Semiring

/-! Natural ceiling computed by counted scalar comparisons and additions.
The supplied natural cap is an upper bound, not the unknown ceiling. Once a
polynomial cap is available this computes the actual original integer budget
with polynomial work. No ceiling instruction is added to the real-RAM. -/

namespace MatrixSpencer.RealRAM.Ceiling

inductive Register where
  | argument
  | counter
  deriving DecidableEq, Fintype

def step : Program Register :=
  .branchLE (.input .argument) (.input .counter) .skip
    (.assign .counter (.add (.input .counter) (.constant 1)))

def program (cap : ℕ) : Program Register :=
  .seq (.assign .counter (.constant 0)) (.repeat cap step)

theorem step_argument (v : Register → ℝ) :
    step.run v .argument = v .argument := by
  simp only [step, Program.run, Expr.eval]
  split_ifs <;> simp

theorem step_counter (v : Register → ℝ) :
    step.run v .counter =
      if v .argument ≤ v .counter then v .counter else v .counter + 1 := by
  simp only [step, Program.run, Expr.eval]
  split_ifs <;> simp

theorem iterate_argument (n : ℕ) (v : Register → ℝ) :
    (step.run)^[n] v .argument = v .argument := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', step_argument, ih]

theorem iterate_counter (n : ℕ) (v : Register → ℝ) (hv : v .counter = 0) :
    (step.run)^[n] v .counter = (min n ⌈v .argument⌉₊ : ℕ) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [Function.iterate_succ_apply', step_counter, iterate_argument, ih]
    by_cases hn : ⌈v .argument⌉₊ ≤ n
    · rw [min_eq_right hn, min_eq_right (by omega : ⌈v .argument⌉₊ ≤ n+1)]
      exact if_pos (Nat.le_ceil _)
    · have hn' : n ≤ ⌈v .argument⌉₊ := by omega
      have hs : n+1 ≤ ⌈v .argument⌉₊ := by omega
      rw [min_eq_left hn', min_eq_left hs, if_neg (by
        intro h
        exact hn (Nat.ceil_le.mpr h))]
      simp

theorem output (cap : ℕ) (v : Register → ℝ) (hcap : v .argument ≤ cap) :
    (program cap).run v .counter = ⌈v .argument⌉₊ := by
  let w := Function.update v .counter (0 : ℝ)
  have hzero : w .counter = 0 := by simp [w]
  have hx : w .argument = v .argument := by simp [w]
  change (step.run)^[cap] (Function.update v .counter ((0 : ℚ) : ℝ)) .counter = _
  norm_num only [Rat.cast_zero]
  change (step.run)^[cap] w .counter = _
  rw [iterate_counter cap w hzero, hx, min_eq_right (Nat.ceil_le.mpr hcap)]

theorem preserves_argument (cap : ℕ) (v : Register → ℝ) :
    (program cap).run v .argument = v .argument := by
  change (step.run)^[cap] (Function.update v .counter ((0 : ℚ) : ℝ)) .argument = _
  norm_num only [Rat.cast_zero]
  rw [iterate_argument]
  simp

theorem step_safe (v : Register → ℝ) : step.Safe v := by
  simp [step, Program.Safe, Expr.Valid]

theorem safe (cap : ℕ) (v : Register → ℝ) : (program cap).Safe v := by
  refine ⟨trivial, ?_⟩
  intro k hk
  exact step_safe _

theorem bound (cap : ℕ) : (program cap).bound = 8*cap+3 := by
  simp [program, step, Program.bound, Expr.cost]
  omega

/-- The ceiling result has an actual safe primitive execution with counted
comparisons, additions, initialization, stores and loop control. -/
theorem execution (cap : ℕ) (v : Register → ℝ) (hcap : v .argument ≤ cap) :
    ∃ w k, Program.Executes (program cap) v w k ∧
      w .counter = ⌈v .argument⌉₊ ∧ w .argument = v .argument ∧ k ≤ 8*cap+3 := by
  refine ⟨(program cap).run v, (program cap).cost v,
    Program.executes_of_safe _ _ (safe cap v), output cap v hcap,
    preserves_argument cap v, ?_⟩
  rw [← bound]
  exact Program.cost_le_bound _ _

end MatrixSpencer.RealRAM.Ceiling
