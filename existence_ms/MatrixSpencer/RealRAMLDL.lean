import MatrixSpencer.RealRAMLDLResiduals

/-!
# Guarded LDL factor data with primitive real-RAM execution and cost

The program initializes coordinate constraints, executes their scalar shorts,
then copies every pivot and computes every column entry with an explicit
zero-pivot branch. All arithmetic, comparisons, loads and stores are charged.
No eigenvector, inverse matrix, or opaque factorization instruction is used.
The conservative bound is polynomial; it is not an optimized cubic LDL claim.
-/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.LDL
abbrev Outputs (d : ℕ) := Fin d ⊕ ScalarShort.Entries d
abbrev Registers (d : ℕ) := LDLResiduals.Registers d ⊕ Outputs d

def pivotValue {d : ℕ} (v : LDLResiduals.Registers d → ℝ) (j : Fin d) : ℝ :=
  v (.inl (j.castSucc,(j,j)))
def columnValue {d : ℕ} (v : LDLResiduals.Registers d → ℝ) (ja : ScalarShort.Entries d) : ℝ :=
  if pivotValue v ja.1=0 then 0 else v (.inl (ja.1.castSucc,(ja.2,ja.1)))/pivotValue v ja.1
def value {d : ℕ} (v : LDLResiduals.Registers d → ℝ) : Outputs d → ℝ :=
  Sum.elim (pivotValue v) (columnValue v)

def pivotExpr (d : ℕ) (j : Fin d) : Expr (Registers d) :=
  .input (.inl (.inl (j.castSucc,(j,j))))
def columnExpr (d : ℕ) (ja : ScalarShort.Entries d) : Expr (Registers d) :=
  .div (.input (.inl (.inl (ja.1.castSucc,(ja.2,ja.1))))) (pivotExpr d ja.1)

def entryProgram (d : ℕ) : Outputs d → Program (Registers d)
  | .inl j => .assign (.inr (.inl j)) (pivotExpr d j)
  | .inr ja =>
    .branchLE (pivotExpr d ja.1) (.constant 0)
      (.branchLE (.constant 0) (pivotExpr d ja.1)
        (.assign (.inr (.inr ja)) (.constant 0))
        (.assign (.inr (.inr ja)) (columnExpr d ja)))
      (.assign (.inr (.inr ja)) (columnExpr d ja))

theorem entryProgram_safe {d : ℕ} (o : Outputs d) (v : Registers d → ℝ) :
    (entryProgram d o).Safe v := by
  rcases o with j|ja
  · trivial
  · simp only [entryProgram,Program.Safe,Expr.Valid,Expr.eval,pivotExpr,columnExpr,Rat.cast_zero]
    split_ifs <;> simp_all
    all_goals linarith

theorem entryProgram_run {d : ℕ} (o : Outputs d) (v : Registers d → ℝ) :
    (entryProgram d o).run v=Function.update v (.inr o) (value (v ∘ Sum.inl) o) := by
  rcases o with j|ja
  · rfl
  · by_cases hz : pivotValue (v ∘ Sum.inl) ja.1=0
    · simp [entryProgram,Program.run,pivotExpr,columnExpr,Expr.eval,value,columnValue,
        pivotValue,Function.comp_apply] at hz ⊢
      simp [hz]
    · have hq : (pivotExpr d ja.1).eval v=pivotValue (v ∘ Sum.inl) ja.1 := rfl
      simp only [entryProgram,Program.run,Expr.eval,Rat.cast_zero,hq,value,Sum.elim_inr,
        columnValue,if_neg hz]
      by_cases hle : pivotValue (v ∘ Sum.inl) ja.1≤0
      · have hge : ¬0≤pivotValue (v ∘ Sum.inl) ja.1 := by
          intro hh; exact hz (le_antisymm hle hh)
        simp only [if_pos hle,if_neg hge]
        rfl
      · simp only [if_neg hle]
        rfl

def entries (d : ℕ) : List (Outputs d) :=
  (List.finRange d).map Sum.inl ++ (ScalarShort.entries d).map Sum.inr
def extract (d : ℕ) : Program (Registers d) :=
  ReadOnlyBatch.program (entryProgram d) (entries d)

theorem mem_entries {d : ℕ} (o : Outputs d) : o∈entries d := by
  cases o <;> simp [entries,ScalarShort.mem_entries]

theorem extract_safe {d : ℕ} (v : Registers d → ℝ) : (extract d).Safe v :=
  ReadOnlyBatch.safe _ (fun o v => entryProgram_safe o v) _ v

theorem extract_output {d : ℕ} (v : Registers d → ℝ) (o : Outputs d) :
    (extract d).run v (.inr o)=value (v ∘ Sum.inl) o := by
  have h := ReadOnlyBatch.output (entryProgram d) value
    (fun o v i => by rw [entryProgram_run]; simp)
    (fun o v => by rw [entryProgram_run]; simp; rfl)
    (fun o v a ha => by rw [entryProgram_run]; simp [ha]) (entries d) v o
  simpa only [if_pos (mem_entries o)] using h

theorem extract_bound (d : ℕ) : (extract d).bound≤10*(d+d*d) := by
  have he : ∀o : Outputs d,(entryProgram d o).bound≤10 := by
    intro o
    cases o <;> norm_num [entryProgram,Program.bound,Expr.cost,pivotExpr,columnExpr]
  have h := ReadOnlyBatch.bound_le _ (entries d) 10 he
  simp only [entries,List.length_append,List.length_map,List.length_finRange,
    ScalarShort.entries_length] at h
  change (ReadOnlyBatch.program (entryProgram d) (entries d)).bound≤_
  change (ReadOnlyBatch.program (entryProgram d) (entries d)).bound≤_ at h
  nlinarith

def program (d : ℕ) : Program (Registers d) :=
  .seq ((LDLResiduals.program d).rename Sum.inl) (extract d)

theorem program_safe {d : ℕ} (v : Registers d → ℝ) : (program d).Safe v := by
  refine ⟨?_,extract_safe _⟩
  exact (Program.safe_rename Sum.inl Sum.inl_injective _ v).mpr (LDLResiduals.program_safe _)

theorem value_correct {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ)
    (v : LDLResiduals.Registers d → ℝ)
    (hv : ∀j : Fin d, ConstraintScan.matrix v j.castSucc=MSManuscriptNumericalLDL.residual C j)
    (o : Outputs d) : value v o=Sum.elim (MSManuscriptNumericalLDL.pivot C)
      (fun ja => MSManuscriptNumericalLDL.lowerColumn C ja.1 ja.2) o := by
  have hp : ∀j,pivotValue v j=MSManuscriptNumericalLDL.pivot C j := by
    intro j
    exact congrFun (congrFun (hv j) j) j
  rcases o with j|ja
  · exact hp j
  · simp only [value,Sum.elim_inr,columnValue,hp,MSManuscriptNumericalLDL.lowerColumn]
    split_ifs
    · rfl
    · congr 1
      exact congrFun (congrFun (hv ja.1) ja.2) ja.1

theorem program_output {d : ℕ} (v : Registers d → ℝ) (o : Outputs d) :
    (program d).run v (.inr o)=
      Sum.elim (MSManuscriptNumericalLDL.pivot (ConstraintScan.matrix (v ∘ Sum.inl) 0))
        (fun ja => MSManuscriptNumericalLDL.lowerColumn
          (ConstraintScan.matrix (v ∘ Sum.inl) 0) ja.1 ja.2) o := by
  change (extract d).run (((LDLResiduals.program d).rename Sum.inl).run v) (.inr o)=_
  rw [extract_output,Program.run_rename Sum.inl Sum.inl_injective]
  apply value_correct
  intro j
  exact LDLResiduals.program_residual (v ∘ Sum.inl) j (Nat.le_of_lt j.isLt)

theorem program_bound (d : ℕ) : (program d).bound≤60*(d+1)^5 := by
  have hr := LDLResiduals.program_bound d
  have he := extract_bound d
  simp only [program,Program.bound,Program.bound_rename]
  have hpoly : 10*(d+d*d)≤12*(d+1)^5 := by
    nlinarith [Nat.zero_le (d^3),Nat.zero_le (d^4),Nat.zero_le (d^5)]
  omega

/-- Actual primitive execution computes all pivots and every guarded column
entry of the previous numerical LDL data, including all singular branches. -/
theorem program_executes {d : ℕ} (v : Registers d → ℝ) :
    ∃w : Registers d → ℝ, ∃cost≤60*(d+1)^5,
      Program.Executes (program d) v w cost ∧
      (∀j,w (.inr (.inl j))=
        MSManuscriptNumericalLDL.pivot (ConstraintScan.matrix (v ∘ Sum.inl) 0) j) ∧
      (∀j a,w (.inr (.inr (j,a)))=
        MSManuscriptNumericalLDL.lowerColumn (ConstraintScan.matrix (v ∘ Sum.inl) 0) j a) := by
  refine ⟨(program d).run v,(program d).cost v,
    ((program d).cost_le_bound v).trans (program_bound d),
    Program.executes_of_safe _ v (program_safe v),?_,?_⟩
  · intro j; exact program_output v (.inl j)
  · intro j a; exact program_output v (.inr (j,a))

/-- For PSD inputs, the actual returned registers are nonnegative LDL factors
of the original matrix. This is a consequence of the executed output equality,
not a factorization oracle in the program. -/
theorem program_factorization {d : ℕ} (v : Registers d → ℝ)
    (hC : (ConstraintScan.matrix (v ∘ Sum.inl) 0).PosSemidef) :
    (∀j,0≤(program d).run v (.inr (.inl j))) ∧
    (∑j,(program d).run v (.inr (.inl j)) •
      Matrix.vecMulVec (fun a => (program d).run v (.inr (.inr (j,a))))
        (fun a => (program d).run v (.inr (.inr (j,a)))))=
      ConstraintScan.matrix (v ∘ Sum.inl) 0 := by
  simp only [program_output,Sum.elim_inl,Sum.elim_inr,MSManuscriptNumericalLDL.pivot_eq,
    MSManuscriptNumericalLDL.lowerColumn_eq]
  exact ⟨KSEighthManuscriptLDL.pivot_nonneg hC,KSEighthManuscriptLDL.sum_terms hC⟩

end MatrixSpencer.RealRAM.LDL
