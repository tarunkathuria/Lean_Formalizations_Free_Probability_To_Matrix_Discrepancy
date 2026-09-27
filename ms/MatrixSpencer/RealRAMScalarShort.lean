import MatrixSpencer.RealRAMReadOnlyBatch
import MatrixSpencer.RealRAMLinearAlgebra
import MatrixSpencer.MSManuscriptNumericalShort

/-!
# Primitive execution of one guarded scalar covariance short

Every matrix-vector product and quadratic form is expanded into scalar loads,
multiplies and sums. Every output entry has two zero tests and an explicit
nonzero division branch. The conservative implementation recomputes these
quantities per entry; its full dense cost is polynomial, not unit-cost shorting.
-/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.ScalarShort
abbrev Entries (d : ℕ) := Fin d × Fin d
abbrev Inputs (d : ℕ) := Entries d ⊕ Fin d
abbrev Registers (d : ℕ) := Inputs d ⊕ Entries d

def matrixOf {d : ℕ} (v : Inputs d → ℝ) : Matrix (Fin d) (Fin d) ℝ := fun i j => v (.inl (i,j))
def vectorOf {d : ℕ} (v : Inputs d → ℝ) : Fin d → ℝ := fun i => v (.inr i)
def input {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) (u : Fin d → ℝ) : Inputs d → ℝ :=
  Sum.elim (fun ij => C ij.1 ij.2) u

def read {d : ℕ} (v : Registers d → ℝ) : Inputs d → ℝ := fun i => v (.inl i)
def value {d : ℕ} (v : Inputs d → ℝ) (ij : Entries d) :=
  MSManuscriptNumericalShort.short (matrixOf v) (vectorOf v) ij.1 ij.2

def matrixExpr (d : ℕ) (ij : Entries d) : Expr (Registers d) := .input (.inl (.inl ij))
def vectorExpr (d : ℕ) (i : Fin d) : Expr (Registers d) := .input (.inl (.inr i))
def productExpr (d : ℕ) (i : Fin d) : Expr (Registers d) :=
  dotExpr d (fun j => .inl (.inl (i,j))) (fun j => .inl (.inr j))
def quadraticExpr (d : ℕ) : Expr (Registers d) :=
  Expr.sumList (List.ofFn (fun i => Expr.mul (vectorExpr d i) (productExpr d i)))
def updatedExpr (d : ℕ) (ij : Entries d) : Expr (Registers d) :=
  .sub (matrixExpr d ij) (.div (.mul (productExpr d ij.1) (productExpr d ij.2)) (quadraticExpr d))

theorem productExpr_eval {d : ℕ} (v : Registers d → ℝ) (i : Fin d) :
    (productExpr d i).eval v=(matrixOf (read v)*ᵥvectorOf (read v)) i := by
  simp only [productExpr,dotExpr_eval,Matrix.mulVec,dotProduct,matrixOf,vectorOf,read]

theorem quadraticExpr_eval {d : ℕ} (v : Registers d → ℝ) :
    (quadraticExpr d).eval v=InverseComparison.quadratic (matrixOf (read v)) (vectorOf (read v)) := by
  simp only [quadraticExpr,Expr.eval_sumList,List.map_ofFn,List.sum_ofFn,Function.comp_apply,Expr.eval,
    vectorExpr,productExpr_eval,InverseComparison.quadratic,dotProduct,vectorOf,read]

theorem quadraticExpr_valid {d : ℕ} (v : Registers d → ℝ) : (quadraticExpr d).Valid v := by
  apply Expr.valid_sumList
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  exact ⟨trivial,dotExpr_valid d _ _ v⟩

theorem updatedExpr_valid {d : ℕ} (v : Registers d → ℝ) (ij : Entries d)
    (hq : (quadraticExpr d).eval v≠0) : (updatedExpr d ij).Valid v :=
  ⟨trivial,⟨dotExpr_valid d _ _ v,dotExpr_valid d _ _ v⟩,quadraticExpr_valid v,hq⟩

theorem updatedExpr_eval {d : ℕ} (v : Registers d → ℝ) (ij : Entries d)
    (hq : (quadraticExpr d).eval v≠0) : (updatedExpr d ij).eval v=value (read v) ij := by
  have hq' := hq
  rw [quadraticExpr_eval] at hq'
  simp only [updatedExpr,Expr.eval,productExpr_eval,quadraticExpr_eval,matrixExpr,
    value,MSManuscriptNumericalShort.short,if_neg hq',Matrix.sub_apply,Matrix.smul_apply,
    realRankOne,Matrix.vecMulVec_apply,smul_eq_mul]
  change (matrixOf (read v)) ij.1 ij.2 - _ = _
  ring

def entryProgram (d : ℕ) (ij : Entries d) : Program (Registers d) :=
  .branchLE (quadraticExpr d) (.constant 0)
    (.branchLE (.constant 0) (quadraticExpr d)
      (.assign (.inr ij) (matrixExpr d ij)) (.assign (.inr ij) (updatedExpr d ij)))
    (.assign (.inr ij) (updatedExpr d ij))

theorem entryProgram_safe {d : ℕ} (v : Registers d → ℝ) (ij : Entries d) :
    (entryProgram d ij).Safe v := by
  simp only [entryProgram,Program.Safe,Expr.Valid,Expr.eval,Rat.cast_zero]
  refine ⟨quadraticExpr_valid v,trivial,?_⟩
  by_cases hle : (quadraticExpr d).eval v≤0
  · rw [if_pos hle]
    refine ⟨trivial,quadraticExpr_valid v,?_⟩
    split_ifs with hge
    · trivial
    · exact updatedExpr_valid v ij (by intro he; rw [he] at hge; exact hge le_rfl)
  · rw [if_neg hle]
    exact updatedExpr_valid v ij (by intro he; rw [he] at hle; exact hle le_rfl)

theorem entryProgram_run {d : ℕ} (v : Registers d → ℝ) (ij : Entries d) :
    (entryProgram d ij).run v=Function.update v (.inr ij) (value (read v) ij) := by
  by_cases hz : (quadraticExpr d).eval v=0
  · have hq := hz
    rw [quadraticExpr_eval] at hq
    simp only [entryProgram,Program.run,Expr.eval,Rat.cast_zero,hz,le_refl,if_true]
    congr 1
    simp only [value,MSManuscriptNumericalShort.short,hq,if_true,matrixExpr,Expr.eval,matrixOf,read]
  · by_cases hle : (quadraticExpr d).eval v≤0
    · have hge : ¬0≤(quadraticExpr d).eval v := by intro h; exact hz (le_antisymm hle h)
      simp only [entryProgram,Program.run,Expr.eval,Rat.cast_zero,if_pos hle,if_neg hge,updatedExpr_eval v ij hz]
    · simp only [entryProgram,Program.run,Expr.eval,Rat.cast_zero,if_neg hle,updatedExpr_eval v ij hz]

theorem quadraticExpr_cost (d : ℕ) : (quadraticExpr d).cost=4*d^2+4*d+1 := by
  simp only [quadraticExpr,Expr.cost_sumList,List.length_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    Expr.cost,vectorExpr,productExpr,dotExpr_cost]
  simp
  ring

theorem entryProgram_bound (d : ℕ) (ij : Entries d) :
    (entryProgram d ij).bound≤46*(d+1)^2 := by
  simp only [entryProgram,Program.bound,quadraticExpr_cost,Expr.cost,matrixExpr,updatedExpr,
    productExpr,dotExpr_cost]
  have hexpand : (d+1)^2=d^2+2*d+1 := by ring
  rw [hexpand]
  omega

def entries (d : ℕ) : List (Entries d) :=
  (List.finRange d).flatMap (fun i => (List.finRange d).map (fun j => (i,j)))
def program (d : ℕ) : Program (Registers d) := ReadOnlyBatch.program (entryProgram d) (entries d)

theorem entries_length (d : ℕ) : (entries d).length=d*d := by
  simp [entries,List.length_flatMap]

theorem mem_entries {d : ℕ} (ij : Entries d) : ij∈entries d := by simp [entries]

theorem program_safe {d : ℕ} (v : Registers d → ℝ) : (program d).Safe v :=
  ReadOnlyBatch.safe (entryProgram d) (fun ij v => entryProgram_safe v ij) _ v

theorem program_output {d : ℕ} (v : Registers d → ℝ) (ij : Entries d) :
    (program d).run v (.inr ij)=value (read v) ij := by
  have h := ReadOnlyBatch.output (entryProgram d) value
    (fun o v i => by rw [entryProgram_run]; simp)
    (fun o v => by rw [entryProgram_run]; simp; rfl)
    (fun o v a ha => by rw [entryProgram_run]; simp [ha]) (entries d) v ij
  simpa only [if_pos (mem_entries ij)] using h

theorem program_preserves_input {d : ℕ} (v : Registers d → ℝ) (i : Inputs d) :
    (program d).run v (.inl i)=v (.inl i) :=
  ReadOnlyBatch.preserves_input (entryProgram d) (fun o v i => by rw [entryProgram_run]; simp) _ v i

theorem program_bound (d : ℕ) : (program d).bound≤46*(d+1)^4 := by
  have h := ReadOnlyBatch.bound_le (entryProgram d) (entries d) (46*(d+1)^2) (entryProgram_bound d)
  rw [entries_length] at h
  refine h.trans ?_
  have hd : d*d≤(d+1)^2 := by nlinarith
  calc
    d*d*(46*(d+1)^2) ≤ (d+1)^2*(46*(d+1)^2) := Nat.mul_le_mul_right _ hd
    _ = 46*(d+1)^4 := by ring

/-- An actual safe primitive program computes every entry of the guarded short,
including its zero-denominator branch, within the displayed polynomial bound. -/
theorem program_executes {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) (u : Fin d → ℝ) :
    ∃w : Registers d → ℝ, ∃k≤46*(d+1)^4,
      Program.Executes (program d) (Sum.elim (input C u) (fun _ => 0)) w k ∧
      ∀ij,w (.inr ij)=MSManuscriptNumericalShort.short C u ij.1 ij.2 := by
  let v : Registers d → ℝ := Sum.elim (input C u) (fun _ => 0)
  refine ⟨(program d).run v,(program d).cost v,
    ((program d).cost_le_bound v).trans (program_bound d),
    Program.executes_of_safe _ v (program_safe v),?_⟩
  intro ij
  simpa only [value,read,input,matrixOf,vectorOf,v,Sum.elim_inl,Sum.elim_inr] using program_output v ij

end MatrixSpencer.RealRAM.ScalarShort
