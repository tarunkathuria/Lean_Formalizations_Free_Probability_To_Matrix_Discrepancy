import MatrixSpencer.RealRAMCeiling

/-! Compute the first natural strictly larger than a nonnegative real,
including the exact integer boundary: the result is floor(x)+1. This is the
actual square-MS movement count convention. No floor primitive is assumed. -/

namespace MatrixSpencer.RealRAM.StrictCeiling
abbrev Register := Ceiling.Register

def step : Program Register :=
  .branchLE (.input .counter) (.input .argument)
    (.assign .counter (.add (.input .counter) (.constant 1))) .skip

def program (cap : ℕ) : Program Register :=
  .seq (.assign .counter (.constant 0)) (.repeat cap step)

theorem step_argument (v : Register → ℝ) : step.run v .argument=v .argument := by
  simp only [step,Program.run,Expr.eval]
  split_ifs <;> simp

theorem step_counter (v : Register → ℝ) : step.run v .counter=
    if v .counter ≤ v .argument then v .counter+1 else v .counter := by
  simp only [step,Program.run,Expr.eval]
  split_ifs <;> simp

theorem iterate_argument (n : ℕ) (v : Register → ℝ) :
    (step.run)^[n] v .argument=v .argument := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',step_argument,ih]

theorem iterate_counter (n : ℕ) (v : Register → ℝ)
    (hv : v .counter=0) (hx : 0≤v .argument) :
    (step.run)^[n] v .counter=(min n (⌊v .argument⌋₊+1) : ℕ) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [Function.iterate_succ_apply',step_counter,iterate_argument,ih]
    by_cases hn : ⌊v .argument⌋₊+1≤n
    · rw [min_eq_right hn,min_eq_right (by omega : ⌊v .argument⌋₊+1≤n+1)]
      have hlt := Nat.lt_floor_add_one (v .argument)
      rw [if_neg (by push_cast; linarith)]
    · have hn' : n≤⌊v .argument⌋₊+1 := by omega
      have hs : n+1≤⌊v .argument⌋₊+1 := by omega
      rw [min_eq_left hn',min_eq_left hs,
        if_pos ((Nat.le_floor_iff hx).mp (by omega : n≤⌊v .argument⌋₊))]
      simp

theorem output (cap : ℕ) (v : Register → ℝ)
    (hx : 0≤v .argument) (hcap : v .argument < cap) :
    (program cap).run v .counter=(⌊v .argument⌋₊+1 : ℕ) := by
  let w := Function.update v .counter (0:ℝ)
  have hzero : w .counter=0 := by simp [w]
  have he : w .argument=v .argument := by simp [w]
  change (step.run)^[cap] (Function.update v .counter ((0:ℚ):ℝ)) .counter=_
  norm_num only [Rat.cast_zero]
  change (step.run)^[cap] w .counter=_
  rw [iterate_counter cap w hzero (he.symm ▸ hx),he,
    min_eq_right (by have h := (Nat.floor_lt hx).mpr hcap; omega)]

theorem preserves_argument (cap : ℕ) (v : Register → ℝ) :
    (program cap).run v .argument=v .argument := by
  change (step.run)^[cap] (Function.update v .counter ((0:ℚ):ℝ)) .argument=_
  rw [iterate_argument]
  simp

theorem step_safe (v : Register → ℝ) : step.Safe v := by
  simp [step,Program.Safe,Expr.Valid]

theorem safe (cap : ℕ) (v : Register → ℝ) : (program cap).Safe v := by
  refine ⟨trivial,?_⟩
  intro k hk
  exact step_safe _

theorem bound (cap : ℕ) : (program cap).bound=8*cap+3 := by
  simp [program,step,Program.bound,Expr.cost]
  omega

theorem execution (cap : ℕ) (v : Register → ℝ)
    (hx : 0≤v .argument) (hcap : v .argument < cap) :
    ∃ w k, Program.Executes (program cap) v w k ∧
      w .counter=(⌊v .argument⌋₊+1 : ℕ) ∧ w .argument=v .argument ∧ k≤8*cap+3 := by
  refine ⟨(program cap).run v,(program cap).cost v,
    Program.executes_of_safe _ _ (safe cap v),output cap v hx hcap,
    preserves_argument cap v,?_⟩
  rw [←bound]
  exact Program.cost_le_bound _ _

end MatrixSpencer.RealRAM.StrictCeiling
