import MatrixSpencer.RealRAMMSQueryFormula
import MatrixSpencer.RealRAMComplexArithmetic
import MatrixSpencer.RealRAMJacobiIteration

/-! Entry arithmetic and finite scalar tables for an actual square-MS epoch.
The table stores the original second-derivative cap for every owner dimension,
and the sum of the matched fourth-derivative caps. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.MSParameterTables
open JacobiIteration (Counted)
set_option maxHeartbeats 2000000

abbrev CenterReg (d : ℕ) := (Fin d × Fin d × Bool) ⊕ Unit

def centerInput {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) : CenterReg d→ℝ
  | .inl (i,j,false) => (H i j).re
  | .inl (i,j,true) => (H i j).im
  | .inr _ => m

def energyExpr (d : ℕ) : Expr (CenterReg d) :=
  finiteSumExpr (fun i : Fin d => finiteSumExpr (fun j : Fin d =>
    .add (.mul (.input (.inl (i,j,false))) (.input (.inl (i,j,false))))
      (.mul (.input (.inl (i,j,true))) (.input (.inl (i,j,true))))))
def centerExpr (d : ℕ) : Expr (CenterReg d) :=
  .add (.add (.constant 1) (.sqrt (energyExpr d))) (.input (.inr ()))

theorem energy_eval {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) :
    (energyExpr d).eval (centerInput H m)=KSOwnerInputBounds.matrixEnergy H := by
  simp [energyExpr,finiteSumExpr_eval,Expr.eval,centerInput,KSOwnerInputBounds.matrixEnergy,pow_two]

theorem center_eval {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) :
    (centerExpr d).eval (centerInput H m)=KSOwnerInputBounds.matrixBound H+(m:ℝ) := by
  simp [centerExpr,Expr.eval,energy_eval,centerInput,KSOwnerInputBounds.matrixBound]

theorem center_valid {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) :
    (centerExpr d).Valid (centerInput H m) := by
  have he : (energyExpr d).Valid (centerInput H m) :=
    finiteSumExpr_valid _ _ (fun i => finiteSumExpr_valid _ _ (fun j => ⟨⟨trivial,trivial⟩,trivial,trivial⟩))
  exact ⟨⟨trivial,he,by rw [energy_eval]; exact KSOwnerInputBounds.matrixEnergy_nonneg H⟩,trivial⟩

theorem center_cost (d : ℕ) : (centerExpr d).cost≤20*(d+1)^2 := by
  simp [centerExpr,energyExpr,Expr.cost,finiteSumExpr_cost]
  nlinarith

def center {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) : Counted ℝ :=
  ⟨(centerExpr d).eval (centerInput H m),(centerExpr d).cost+1⟩
theorem center_value {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) :
    (center H m).value=KSOwnerInputBounds.matrixBound H+(m:ℝ) := center_eval H m

theorem center_execution {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) :
    Expr.Executes (centerInput H m) (centerExpr d) (center H m).value (centerExpr d).cost :=
  Expr.executes_of_valid _ _ (center_valid H m)

def secondTable (R : ℝ) (m d : ℕ) : Counted (Fin (m+1)→ℝ) :=
  ⟨fun k => MSQueryFormula.second.eval (MSQueryFormula.input R k m d),
    (m+1)*(MSQueryFormula.second.cost+5)⟩
def fourthTable (R : ℝ) (m d : ℕ) : Counted (Fin (m+1)→ℝ) :=
  ⟨fun k => MSQueryFormula.movementFourth.eval (MSQueryFormula.input R k m d),
    (m+1)*(MSQueryFormula.movementFourth.cost+5)⟩

theorem secondTable_value (R : ℝ) (m d : ℕ) (k : Fin (m+1)) :
    (secondTable R m d).value k=MSManuscriptGammaInputBoundScaled.secondCap k d R 1 (1/8192) m :=
  MSQueryFormula.second_eval R k m d

theorem fourthTable_value (R : ℝ) (m d : ℕ) (k : Fin (m+1)) :
    (fourthTable R m d).value k=MSManuscriptMovementDrift.movementBudget m k d R 1 (1/8192) :=
  MSQueryFormula.movementFourth_eval R k m d

theorem secondTable_execution (R : ℝ) (m d : ℕ) (hR : 0≤R) (hd : 0<d) (k : Fin (m+1)) :
    Expr.Executes (MSQueryFormula.input R k m d) MSQueryFormula.second
      ((secondTable R m d).value k) MSQueryFormula.second.cost :=
  Expr.executes_of_valid _ _ (MSQueryFormula.second_valid R k m d hR hd)

theorem fourthTable_execution (R : ℝ) (m d : ℕ) (hR : 0≤R) (hd : 0<d) (k : Fin (m+1)) :
    Expr.Executes (MSQueryFormula.input R k m d) MSQueryFormula.movementFourth
      ((fourthTable R m d).value k) MSQueryFormula.movementFourth.cost :=
  Expr.executes_of_valid _ _ (MSQueryFormula.movementFourth_valid R k m d hR hd)

theorem secondTable_cost (R : ℝ) (m d : ℕ) :
    (secondTable R m d).cost≤2000005*(m+1) := by
  dsimp [secondTable]
  nlinarith [MSQueryFormula.second_cost]
theorem fourthTable_cost (R : ℝ) (m d : ℕ) :
    (fourthTable R m d).cost≤2000005*(m+1) := by
  dsimp [fourthTable]
  nlinarith [MSQueryFormula.movementFourth_cost]

def sumExpr (m : ℕ) : Expr (Fin (m+1)) := .add (.constant 1) (finiteSumExpr Expr.input)
def sumTable {m : ℕ} (t : Fin (m+1)→ℝ) : Counted ℝ :=
  ⟨(sumExpr m).eval t,(sumExpr m).cost+1⟩
theorem sumTable_value {m : ℕ} (t : Fin (m+1)→ℝ) : (sumTable t).value=1+∑k,t k := by
  simp [sumTable,sumExpr,Expr.eval,finiteSumExpr_eval]
theorem sumTable_execution {m : ℕ} (t : Fin (m+1)→ℝ) :
    Expr.Executes t (sumExpr m) (sumTable t).value (sumExpr m).cost :=
  Expr.executes_of_valid _ _ ⟨trivial,finiteSumExpr_valid _ _ (fun _ => trivial)⟩
theorem sumTable_cost {m : ℕ} (t : Fin (m+1)→ℝ) : (sumTable t).cost=2*m+6 := by
  simp [sumTable,sumExpr,Expr.cost,finiteSumExpr_cost]
  omega

def curvature (R : ℝ) (m d : ℕ) : Counted ℝ :=
  let t := secondTable R m d
  let s := sumTable t.value
  ⟨s.value,t.cost+s.cost⟩
def fourth (R : ℝ) (m d : ℕ) : Counted ℝ :=
  let t := fourthTable R m d
  let s := sumTable t.value
  ⟨s.value,t.cost+s.cost⟩

theorem curvature_value (R : ℝ) (m d : ℕ) :
    (curvature R m d).value=1+∑k : Fin (m+1),MSManuscriptGammaInputBoundScaled.secondCap k d R 1 (1/8192) m := by
  simp [curvature,sumTable_value,secondTable_value]

theorem fourth_value (R : ℝ) (m d : ℕ) :
    (fourth R m d).value=MSManuscriptMovementDrift.uniformBudget m d R 1 (1/8192) := by
  simp only [fourth,sumTable_value,fourthTable_value,MSManuscriptMovementDrift.uniformBudget]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k => MSManuscriptMovementDrift.movementBudget m k d R 1 (1/8192)) (m+1)

theorem curvature_cost (R : ℝ) (m d : ℕ) : (curvature R m d).cost≤2000011*(m+1) := by
  dsimp only [curvature]
  rw [sumTable_cost]
  nlinarith [secondTable_cost R m d]
theorem fourth_cost (R : ℝ) (m d : ℕ) : (fourth R m d).cost≤2000011*(m+1) := by
  dsimp only [fourth]
  rw [sumTable_cost]
  nlinarith [fourthTable_cost R m d]

/-- A stored table entry is one real register load. -/
def lookup {m : ℕ} (t : Fin (m+1)→ℝ) (k : Fin (m+1)) : Counted ℝ :=
  ⟨(Expr.input k).eval t,1⟩
theorem lookup_value {m : ℕ} (t : Fin (m+1)→ℝ) (k : Fin (m+1)) : (lookup t k).value=t k := rfl
theorem lookup_execution {m : ℕ} (t : Fin (m+1)→ℝ) (k : Fin (m+1)) :
    Expr.Executes t (.input k) (lookup t k).value (lookup t k).cost := Expr.Executes.input k

end MatrixSpencer.RealRAM.MSParameterTables
