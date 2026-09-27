import MatrixSpencer.RealRAMConstraintScan
import MatrixSpencer.MSManuscriptNumericalLDL

/-!
# Guarded LDL residuals by actual primitive execution

The coordinate constraints are written as rational constants, with their stores
charged, and the complete scalar constraint scan is then executed. Every
residual matrix is retained in its own bank. Zero pivots execute the guarded
identity branch, so no division by zero is performed, even for singular inputs.
-/
open Matrix
noncomputable section
namespace MatrixSpencer.RealRAM.LDLResiduals
abbrev Registers (d : ℕ) := ConstraintScan.Registers d d

def initializeEntry (d : ℕ) (ji : ScalarShort.Entries d) : Program (Registers d) :=
  .assign (.inr ji) (.constant (if ji.1=ji.2 then 1 else 0))
def initializeProgram (d : ℕ) : Program (Registers d) :=
  ReadOnlyBatch.program (initializeEntry d) (ScalarShort.entries d)

theorem initialize_safe {d : ℕ} (v : Registers d → ℝ) : (initializeProgram d).Safe v :=
  ReadOnlyBatch.safe (initializeEntry d) (fun _ _ => trivial) _ v

theorem initialize_matrix {d : ℕ} (v : Registers d → ℝ) (b : Fin (d+1)) :
    ConstraintScan.matrix ((initializeProgram d).run v) b=ConstraintScan.matrix v b := by
  ext i j
  exact ReadOnlyBatch.preserves_input (initializeEntry d)
    (fun _ _ _ => by simp [initializeEntry,Program.run]) _ v (b,(i,j))

theorem initialize_constraint {d : ℕ} (v : Registers d → ℝ) (j : Fin d) :
    ConstraintScan.constraint ((initializeProgram d).run v) j=Pi.single j 1 := by
  funext i
  have h := ReadOnlyBatch.output (initializeEntry d)
    (fun _ ji => if ji.1=ji.2 then (1:ℝ) else 0)
    (fun _ _ _ => by simp [initializeEntry,Program.run])
    (fun ji v => by simp [initializeEntry,Program.run,Expr.eval]; split_ifs <;> norm_num)
    (fun ji v a ha => by simp [initializeEntry,Program.run,ha])
    (ScalarShort.entries d) v (j,i)
  simpa only [ScalarShort.mem_entries,if_true,Pi.single_apply,eq_comm] using h

theorem initialize_bound (d : ℕ) : (initializeProgram d).bound≤2*d*d := by
  have h := ReadOnlyBatch.bound_le (initializeEntry d) (ScalarShort.entries d) 2
    (fun ji => by simp [initializeEntry,Program.bound,Expr.cost])
  rw [ScalarShort.entries_length] at h
  change (ReadOnlyBatch.program (initializeEntry d) (ScalarShort.entries d)).bound≤_
  nlinarith

theorem short_single {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    MSManuscriptNumericalShort.short C (Pi.single j 1)=MSManuscriptNumericalLDL.schur C j := by
  simp only [MSManuscriptNumericalShort.short,InverseComparison.quadratic,
    Matrix.mulVec_single_one,single_dotProduct,one_mul,MSManuscriptNumericalLDL.schur,
    realRankOne,Matrix.col,Matrix.transpose_apply]
  rfl

theorem matrices_units {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) :
    ConstraintScan.matrices C (fun j : Fin d => Pi.single j 1) n=
      MSManuscriptNumericalLDL.residual C n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ConstraintScan.matrices,MSManuscriptNumericalLDL.residual,ih,short_single]

def program (d : ℕ) : Program (Registers d) := .seq (initializeProgram d) (ConstraintScan.scan d d d)

theorem program_safe {d : ℕ} (v : Registers d → ℝ) : (program d).Safe v :=
  ⟨initialize_safe v,ConstraintScan.scan_safe _ _ _ _⟩

theorem program_residual {d : ℕ} (v : Registers d → ℝ) (j : ℕ) (hj : j≤d) :
    ConstraintScan.matrix ((program d).run v) ⟨j,by omega⟩=
      MSManuscriptNumericalLDL.residual (ConstraintScan.matrix v 0) j := by
  have h := ConstraintScan.scan_stored d le_rfl ((initializeProgram d).run v) j hj
  have hc : ConstraintScan.constraint ((initializeProgram d).run v)=fun i => Pi.single i 1 :=
    funext (initialize_constraint v)
  rw [initialize_matrix,hc,matrices_units] at h
  exact h

theorem program_bound (d : ℕ) : (program d).bound≤48*(d+1)^5 := by
  have hi := initialize_bound d
  have hs := ConstraintScan.scan_bound d d d
  change (initializeProgram d).bound+(ConstraintScan.scan d d d).bound≤_
  nlinarith

/-- A concrete safe primitive run computes every guarded LDL residual. The
original matrix alone is supplied; the unit constraints are initialized by
charged scalar stores inside the program. Scratch banks are arbitrary. -/
theorem program_executes {d : ℕ} (v : Registers d → ℝ) :
    ∃w : Registers d → ℝ, ∃cost≤48*(d+1)^5,
      Program.Executes (program d) v w cost ∧
      ∀j (hj : j≤d), ConstraintScan.matrix w ⟨j,by omega⟩=
        MSManuscriptNumericalLDL.residual (ConstraintScan.matrix v 0) j := by
  refine ⟨(program d).run v,(program d).cost v,
    ((program d).cost_le_bound v).trans (program_bound d),
    Program.executes_of_safe _ v (program_safe v),?_⟩
  exact program_residual v

end MatrixSpencer.RealRAM.LDLResiduals
