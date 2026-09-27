import SeamlessKS.Input
import MatrixSpencer.RealRAMKSInputSetup
import MatrixSpencer.RealRAMProgram

/-! Original squared norms and their maximum are evaluated from scalar input
entries. The maximum uses explicit comparison and assignment instructions;
zero atoms remain among the original labels. -/
open scoped BigOperators
noncomputable section
namespace SeamlessKS.RuntimeInput
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {N d : ℕ}

abbrev MaxRegister (N : ℕ) := Fin N ⊕ Unit

def maxInput (q : Fin N → ℝ) : MaxRegister N → ℝ := Sum.elim q (fun _ => 0)

def maxProgram : List (Fin N) → Program (MaxRegister N)
  | [] => .assign (.inr ()) (.constant 0)
  | i :: is => .seq (maxProgram is)
      (.branchLE (.input (.inl i)) (.input (.inr ())) .skip
        (.assign (.inr ()) (.input (.inl i))))

theorem maxProgram_preserves (is : List (Fin N)) (q : MaxRegister N → ℝ) (j : Fin N) :
    (maxProgram is).run q (.inl j)=q (.inl j) := by
  induction is with
  | nil => simp [maxProgram,Program.run]
  | cons i is ih =>
    simp only [maxProgram,Program.run,Expr.eval]
    split_ifs <;> simpa using ih

theorem maxProgram_output (is : List (Fin N)) (q : MaxRegister N → ℝ) :
    (maxProgram is).run q (.inr ())=Input.maximum (is.map (fun i => q (.inl i))) := by
  induction is with
  | nil => simp [maxProgram,Program.run,Expr.eval,Input.maximum]
  | cons i is ih =>
    simp only [maxProgram,Program.run,Expr.eval,List.map_cons]
    rw [maxProgram_preserves,ih]
    simp only [Input.maximum,List.foldr_cons,max_def]
    split_ifs <;> simp_all [Input.maximum]

theorem maxProgram_safe (is : List (Fin N)) (q : MaxRegister N → ℝ) :
    (maxProgram is).Safe q := by
  induction is with
  | nil => trivial
  | cons i is ih =>
    refine ⟨ih,trivial,trivial,?_⟩
    split_ifs <;> trivial

theorem maxProgram_bound (is : List (Fin N)) : (maxProgram is).bound=5*is.length+2 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [maxProgram,Program.bound,Expr.cost,ih]; omega

/-- The size expressions reused here are literal sums of squares of real and
imaginary input entries. -/
theorem sizes_value (v : Fin N → Fin d → ℂ) : (KSInputSetup.sizes v).value=Input.size v :=
  KSInputSetup.sizes_value v

theorem sizes_execution (v : Fin N → Fin d → ℂ) (i : Fin N) :
    Expr.Executes (KSInputSetup.input v) (KSInputSetup.sizeExpr i)
      (Input.size v i) (8*d+1) := by
  simpa only [sizes_value] using KSInputSetup.sizes_entry_execution v i

def compute (v : Fin N → Fin d → ℂ) : Counted ℝ :=
  let q := KSInputSetup.sizes v
  let p := maxProgram (List.finRange N)
  let x := maxInput q.value
  ⟨p.run x (.inr ()),q.cost+p.cost x+2*N+4⟩

@[simp] theorem compute_value (v : Fin N → Fin d → ℂ) :
    (compute v).value=Input.epsilon v := by
  simp [compute,maxProgram_output,maxInput,sizes_value,Input.epsilon]

theorem maximum_execution (v : Fin N → Fin d → ℂ) :
    ∃ q k, Program.Executes (maxProgram (List.finRange N))
      (maxInput (KSInputSetup.sizes v).value) q k ∧
      q (.inr ())=Input.epsilon v ∧ k≤5*N+2 := by
  let p := maxProgram (List.finRange N)
  let x := maxInput (KSInputSetup.sizes v).value
  refine ⟨p.run x,p.cost x,Program.executes_of_safe _ _ (maxProgram_safe _ _),?_,?_⟩
  · exact compute_value v
  · simpa [p,maxProgram_bound] using Program.cost_le_bound p x

theorem compute_cost (v : Fin N → Fin d → ℂ) : (compute v).cost≤20*(N+1)*(d+1) := by
  have h := Program.cost_le_bound (maxProgram (List.finRange N))
    (maxInput (KSInputSetup.sizes v).value)
  rw [maxProgram_bound,List.length_finRange] at h
  dsimp only [KSInputSetup.sizes] at h
  dsimp only [compute,KSInputSetup.sizes]
  nlinarith

end SeamlessKS.RuntimeInput
