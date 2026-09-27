import MatrixSpencer.RealRAMProgram

/-! Sequential evaluation of actual register programs with a read-only input
bank and individual output addresses. Costs sum the primitive program bounds;
there is no opaque function-call instruction in the batch. -/
open scoped BigOperators
namespace MatrixSpencer.RealRAM.ReadOnlyBatch
variable {I O : Type*} [DecidableEq I] [DecidableEq O]
abbrev Registers (I O : Type*) := I ⊕ O

def program (job : O → Program (Registers I O)) : List O → Program (Registers I O)
  | [] => .skip
  | o::os => .seq (job o) (program job os)

theorem preserves_input (job : O → Program (Registers I O))
    (hread : ∀o v i,(job o).run v (.inl i)=v (.inl i)) (os : List O)
    (v : Registers I O → ℝ) (i : I) : (program job os).run v (.inl i)=v (.inl i) := by
  induction os generalizing v with
  | nil => rfl
  | cons o os ih =>
    change (program job os).run ((job o).run v) (.inl i)=v (.inl i)
    rw [ih,hread]

theorem safe (job : O → Program (Registers I O)) (hsafe : ∀o v,(job o).Safe v)
    (os : List O) (v : Registers I O → ℝ) : (program job os).Safe v := by
  induction os generalizing v with
  | nil => trivial
  | cons o os ih => exact ⟨hsafe o v,ih _⟩

theorem output (job : O → Program (Registers I O)) (f : (I → ℝ) → O → ℝ)
    (hread : ∀o v i,(job o).run v (.inl i)=v (.inl i))
    (hwrite : ∀o v,(job o).run v (.inr o)=f (fun i => v (.inl i)) o)
    (hother : ∀o v a,a≠o→(job o).run v (.inr a)=v (.inr a))
    (os : List O) (v : Registers I O → ℝ) (a : O) :
    (program job os).run v (.inr a)=if a∈os then f (fun i => v (.inl i)) a else v (.inr a) := by
  induction os generalizing v with
  | nil => simp [program,Program.run]
  | cons o os ih =>
    change (program job os).run ((job o).run v) (.inr a)=_
    rw [ih]
    have he : (fun i => (job o).run v (.inl i))=(fun i => v (.inl i)) := funext (hread o v)
    rw [he]
    by_cases ha : a∈os
    · simp [ha]
    · by_cases hao : a=o
      · subst a
        simp [ha,hwrite]
      · simp [ha,hao,hother o v a hao]

omit [DecidableEq I] [DecidableEq O] in
theorem bound (job : O → Program (Registers I O)) (os : List O) :
    (program job os).bound=(os.map (fun o => (job o).bound)).sum := by
  induction os with
  | nil => rfl
  | cons o os ih => simp only [program,Program.bound,List.map_cons,List.sum_cons,ih]

omit [DecidableEq I] [DecidableEq O] in
theorem bound_le (job : O → Program (Registers I O)) (os : List O) (b : ℕ)
    (hb : ∀o,(job o).bound≤b) : (program job os).bound≤os.length*b := by
  induction os with
  | nil => simp [program,Program.bound]
  | cons o os ih =>
    simp only [program,Program.bound,List.length_cons]
    have h := hb o
    nlinarith

end MatrixSpencer.RealRAM.ReadOnlyBatch
