import MatrixSpencer.RealRAMMSPoint
import MatrixSpencer.RealRAMComplexArithmetic
import MatrixSpencer.RealRAMProgram
import MatrixSpencer.MSManuscriptMatrixReindex

/-! Restriction uses the already stored label array. Scalar comparisons mark
frozen coefficients, real/imaginary entry circuits add their contribution to
the offset, and the filtered array controls the live-coordinate data copies. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.MSRestriction
open JacobiIteration (Counted)
open MSPoint PhaseRestriction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

inductive MaskReg where | source | result
  deriving DecidableEq

def zeroMask : Program MaskReg := .assign .result (.constant 0)
def copyMask : Program MaskReg := .assign .result (.input .source)
def maskProgram : Program MaskReg :=
  .branchLE (.input .source) (.constant (-1))
    (.branchLE (.constant (-1)) (.input .source) copyMask zeroMask)
    (.branchLE (.input .source) (.constant 1)
      (.branchLE (.constant 1) (.input .source) copyMask zeroMask) zeroMask)
def maskInput (x : ℝ) : MaskReg→ℝ | .source => x | .result => 0

theorem mask_value (x : ℝ) : (maskProgram.run (maskInput x)) .result=
    if IsSign x then x else 0 := by
  simp only [maskProgram,copyMask,zeroMask,Program.run,Expr.eval,maskInput,
    Rat.cast_neg,Rat.cast_one,Rat.cast_zero,Function.update_self,IsSign]
  split_ifs <;> simp_all
  · exact ((‹¬x=1 ∧ ¬x = -1›).2 (le_antisymm ‹x ≤ -1› ‹-1 ≤ x›)).elim
  · rcases ‹x=1 ∨ x = -1› with h | h <;> exfalso <;> linarith
  · exact ((‹¬x=1 ∧ ¬x = -1›).1 (le_antisymm ‹x ≤ 1› ‹1 ≤ x›)).elim
  · rcases ‹x=1 ∨ x = -1› with h | h <;> exfalso <;> linarith
  · rcases ‹x=1 ∨ x = -1› with h | h <;> exfalso <;> linarith

theorem mask_safe (x : ℝ) : maskProgram.Safe (maskInput x) := by
  simp [maskProgram,copyMask,zeroMask,Program.Safe,Expr.Valid]
theorem mask_bound : maskProgram.bound=11 := by decide

def weights (L : Table ι) (x : EuclideanSpace ℝ ι) : Counted (ι→ℝ) :=
  ⟨fun i => (maskProgram.run (maskInput (x i))) .result,13*L.labels.length+1⟩
theorem weights_value (L : Table ι) (x : EuclideanSpace ℝ ι) (i : ι) :
    (weights L x).value i=if i∈frozenCoordinates x then x i else 0 := by
  simp only [weights,mask_value,mem_frozenCoordinates]
theorem weights_execution (L : Table ι) (x : EuclideanSpace ℝ ι) (i : ι) :
    ∃ v k, Program.Executes maskProgram (maskInput (x i)) v k ∧
      v .result=(weights L x).value i ∧ k≤11 := by
  refine ⟨maskProgram.run (maskInput (x i)),maskProgram.cost (maskInput (x i)),
    Program.executes_of_safe _ _ (mask_safe _),rfl,?_⟩
  rw [←mask_bound]
  exact Program.cost_le_bound _ _

def EntryReg (ι : Type*) := (ι×Fin 3)⊕Fin 2

def entryInput {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (w : ι→ℝ) (a b : Fin d) : EntryReg ι→ℝ
  | .inl (i,0) => w i
  | .inl (i,1) => (A i a b).re
  | .inl (i,2) => (A i a b).im
  | .inr 0 => (H a b).re
  | .inr 1 => (H a b).im

def entryExpr (is : List ι) : ComplexExpr (EntryReg ι) :=
  ⟨.add (.input (.inr 0)) (Expr.sumList (is.map (fun i =>
    .mul (.input (.inl (i,0))) (.input (.inl (i,1)))))),
   .add (.input (.inr 1)) (Expr.sumList (is.map (fun i =>
    .mul (.input (.inl (i,0))) (.input (.inl (i,2))))))⟩

theorem entry_valid {d : ℕ} (is : List ι) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (w : ι→ℝ) (a b : Fin d) :
    (entryExpr is).Valid (entryInput H A w a b) := by
  constructor <;> refine ⟨trivial,Expr.valid_sumList _ _ ?_⟩ <;>
    intro e he <;> obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he <;> exact ⟨trivial,trivial⟩

theorem entry_cost (is : List ι) : (entryExpr is).cost=8*is.length+6 := by
  simp [entryExpr,ComplexExpr.cost,Expr.cost,Expr.cost_sumList,List.map_map,Function.comp_def,List.map_const,List.sum_replicate]
  omega

theorem table_sum {E : Type*} [AddCommMonoid E] (L : Table ι) (f : ι→E) :
    (L.labels.map f).sum=∑i,f i := by
  have he : L.labels.toFinset=Finset.univ := by ext i; simp [L.complete]
  rw [←List.sum_toFinset f L.nodup,he]

theorem entry_value {d : ℕ} (L : Table ι) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (w : ι→ℝ) (a b : Fin d) :
    (entryExpr L.labels).eval (entryInput H A w a b)=H a b+∑i,w i • A i a b := by
  apply Complex.ext <;>
    simp [entryExpr,ComplexExpr.eval,Expr.eval,Expr.eval_sumList,List.map_map,
      entryInput,table_sum,Complex.add_re,Complex.add_im,Complex.re_sum,Complex.im_sum]

def matrix {d : ℕ} (L : Table ι) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℝ ι) :
    Counted (Matrix (Fin d) (Fin d) ℂ) :=
  let w:=weights L x
  ⟨fun a b => (entryExpr L.labels).eval (entryInput H A w.value a b),
    w.cost+d*d*((entryExpr L.labels).cost+2)+1⟩

theorem matrix_value {d : ℕ} (L : Table ι) (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    (matrix L (H:Matrix (Fin d) (Fin d) ℂ) A x).value=
      (restrictedOffset H A hA x:Matrix (Fin d) (Fin d) ℂ) := by
  have hsum := map_sum (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)).subtype
    (fun i => x i • hermitianMatrixFamily A hA i) (frozenCoordinates x)
  change (↑(∑ i ∈ frozenCoordinates x, x i • hermitianMatrixFamily A hA i :
      selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ) =
    ∑ i ∈ frozenCoordinates x, (↑(x i • hermitianMatrixFamily A hA i :
      selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ) at hsum
  simp only [selfAdjoint.val_smul,hermitianMatrixFamily] at hsum
  ext a b
  rw [show (matrix L (H:Matrix (Fin d) (Fin d) ℂ) A x).value a b=
      (entryExpr L.labels).eval (entryInput (H:Matrix (Fin d) (Fin d) ℂ) A (weights L x).value a b) from rfl,
    entry_value]
  simp only [weights_value,ite_smul,zero_smul,Finset.sum_ite_mem,Finset.univ_inter,
    restrictedOffset,AddSubgroup.coe_add,hsum,selfAdjoint.val_smul,
    Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,hermitianMatrixFamily]


theorem matrix_entry_execution {d : ℕ} (L : Table ι) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℝ ι) (a b : Fin d) :
    Expr.Executes (entryInput H A (weights L x).value a b) (entryExpr L.labels).re
      ((matrix L H A x).value a b).re (entryExpr L.labels).re.cost ∧
    Expr.Executes (entryInput H A (weights L x).value a b) (entryExpr L.labels).im
      ((matrix L H A x).value a b).im (entryExpr L.labels).im.cost :=
  ⟨Expr.executes_of_valid _ _ (entry_valid L.labels H A _ a b).1,
    Expr.executes_of_valid _ _ (entry_valid L.labels H A _ a b).2⟩

/-- Frozen-offset construction commutes with the physical index permutation. -/
theorem restrictedOffset_reindex {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q] (e : p≃q)
    (H : selfAdjoint (Matrix q q ℂ)) (A : ι→Matrix q q ℂ)
    (hA : ∀i,(A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    restrictedOffset (MSManuscriptMatrixReindex.selfAdjointReindex e H)
      (fun i => (A i).submatrix e e) (fun i => (hA i).submatrix e) x =
    MSManuscriptMatrixReindex.selfAdjointReindex e (restrictedOffset H A hA x) := by
  apply Subtype.ext
  ext a b
  simp [restrictedOffset,hermitianMatrixFamily,MSManuscriptMatrixReindex.selfAdjointReindex,
    Matrix.sum_apply,Matrix.smul_apply]

theorem matrix_cost {d : ℕ} (L : Table ι) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℝ ι) :
    (matrix L H A x).cost≤30*(Fintype.card ι+1)*(d+1)^2 := by
  simp only [matrix,weights,entry_cost,table_length]
  nlinarith

def offset {d : ℕ} (L : Table ι) (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    Counted (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) :=
  let M:=matrix L H A x
  ⟨⟨M.value,by rw [matrix_value L H A hA x]; exact (restrictedOffset H A hA x).property⟩,M.cost+1⟩
theorem offset_value {d : ℕ} (L : Table ι) (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    (offset L H A hA x).value=restrictedOffset H A hA x :=
  Subtype.ext (matrix_value L H A hA x)
theorem offset_cost {d : ℕ} (L : Table ι) (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    (offset L H A hA x).cost≤30*(Fintype.card ι+1)*(d+1)^2+1 := by
  exact Nat.add_le_add_right (matrix_cost L H A x) 1

/-- Copies are indexed by the already filtered live array. -/
def point (L : Table ι) (x : EuclideanSpace ℝ ι) : Counted (EuclideanSpace ℝ (Live x)) :=
  let t:=restricted L x
  ⟨WithLp.toLp 2 (fun i => x i),t.cost+2*t.value.labels.length+1⟩
def family {d : ℕ} (L : Table ι) (A : ι→Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℝ ι) :
    Counted (Live x→Matrix (Fin d) (Fin d) ℂ) :=
  let t:=restricted L x
  ⟨fun i a b => A i a b,t.cost+4*t.value.labels.length*d*d+1⟩
theorem point_value (L : Table ι) (x : EuclideanSpace ℝ ι) : (point L x).value=restrictPoint x := rfl
theorem family_value {d : ℕ} (L : Table ι) (A : ι→Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℝ ι) :
    (family L A x).value=restrictedFamily A x := rfl
theorem point_cost (L : Table ι) (x : EuclideanSpace ℝ ι) :
    (point L x).cost≤12*Fintype.card ι+4 := by
  have hk : Fintype.card (Live x)≤Fintype.card ι := Fintype.card_subtype_le _
  simp only [point,restricted_cost,table_length]
  omega
theorem family_cost {d : ℕ} (L : Table ι) (A : ι→Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℝ ι) :
    (family L A x).cost≤14*(Fintype.card ι+1)*(d+1)^2 := by
  have hk : Fintype.card (Live x)≤Fintype.card ι := Fintype.card_subtype_le _
  simp only [family,restricted_cost,table_length]
  nlinarith [Nat.mul_le_mul_right (d*d) hk]

end MatrixSpencer.RealRAM.MSRestriction
