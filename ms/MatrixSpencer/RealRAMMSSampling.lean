import MatrixSpencer.KSEighthCountedMovement
import MatrixSpencer.MSManuscriptNumericalSamplerData
import MatrixSpencer.RealRAMMSGammaTop

/-! Literal guarded LDL weights and selected increment for the square walk.
The ordered positive-pivot scan is charged, and all categorical weights are
formed by scalar operations. Choosing a categorical index is separate. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.MSSampling
open JacobiIteration (Counted Mat)
open MSManuscriptNumericalSamplerData (Draws)
attribute [local instance] Classical.propDecidable
variable {k : ℕ}
set_option maxRecDepth 4096

def squareSumExpr : Expr (Fin k) :=
  Expr.sumList (List.ofFn (fun i : Fin k => .mul (.input i) (.input i)))
@[simp] theorem squareSum_eval (v : Fin k → ℝ) :
    squareSumExpr.eval v=∑i,v i^2 := by
  simp [squareSumExpr,Expr.eval_sumList,List.map_ofFn,List.sum_ofFn,Expr.eval,pow_two]
@[simp] theorem squareSum_cost : (squareSumExpr (k:=k)).cost=4*k+1 := by
  simp [squareSumExpr,Expr.cost_sumList,List.map_ofFn,List.sum_ofFn,Expr.cost]
  omega
theorem squareSum_execution (v : Fin k → ℝ) :
    Expr.Executes v squareSumExpr (∑i,v i^2) (4*k+1) := by
  have hv : squareSumExpr.Valid v := by
    apply Expr.valid_sumList
    intro e he
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he
    trivial
  simpa only [squareSum_eval,squareSum_cost] using Expr.executes_of_valid v squareSumExpr hv

def traceExpr : Expr (Fin k×Fin k) :=
  Expr.sumList (List.ofFn (fun i : Fin k => .input (i,i)))
@[simp] theorem trace_eval (Q : Mat k) :
    traceExpr.eval (JacobiIteration.entries Q)=realTrace Q := by
  simp [traceExpr,Expr.eval_sumList,List.map_ofFn,List.sum_ofFn,Expr.eval,
    JacobiIteration.entries,realTrace,Matrix.trace]
@[simp] theorem trace_cost : (traceExpr (k:=k)).cost=2*k+1 := by
  simp [traceExpr,Expr.cost_sumList,List.map_ofFn,List.sum_ofFn,Expr.cost]
  omega

def labels (p : Fin k → ℝ) : List (Fin k) → Counted (List (Fin k))
  | [] => ⟨[],1⟩
  | j::js => let t:=labels p js
             ⟨if 0<p j then j::t.value else t.value,t.cost+5⟩
theorem labels_value (p : Fin k → ℝ) (js : List (Fin k)) :
    (labels p js).value=js.filter (fun j=>decide (0<p j)) := by
  induction js with
  | nil=>rfl
  | cons j js ih=>simp [labels,ih];split_ifs <;>simp_all

theorem labels_cost (p : Fin k → ℝ) (js : List (Fin k)) :
    (labels p js).cost=5*js.length+1 := by
  induction js with
  | nil=>rfl
  | cons j js ih=>simp [labels,ih];omega

structure Data (k : ℕ) where
  pivots : Fin k → ℝ
  columns : Fin k → Fin k → ℝ
  energies : Fin k → ℝ
  trace : ℝ
  labels : List (Fin k)

def data (Q : Mat k) : Counted (Data k) :=
  let f:=KSEighthCountedMovement.factor Q
  let ls:=labels f.value.1 (List.finRange k)
  ⟨{pivots:=f.value.1,columns:=f.value.2,
    energies:=fun j=>squareSumExpr.eval (f.value.2 j),
    trace:=traceExpr.eval (JacobiIteration.entries Q),labels:=ls.value},
    f.cost+ls.cost+k*((squareSumExpr (k:=k)).cost+2)+(traceExpr (k:=k)).cost+10*(k+1)^2⟩

@[simp] theorem data_pivots (Q : Mat k) (j : Fin k) :
    (data Q).value.pivots j=MSManuscriptNumericalLDL.pivot Q j := by
  simp only [data,KSEighthCountedMovement.factor_pivot,MSManuscriptNumericalLDL.pivot_eq]
@[simp] theorem data_columns (Q : Mat k) (j i : Fin k) :
    (data Q).value.columns j i=MSManuscriptNumericalLDL.lowerColumn Q j i := by
  simp only [data,KSEighthCountedMovement.factor_column,MSManuscriptNumericalLDL.lowerColumn_eq]
@[simp] theorem data_energies (Q : Mat k) (j : Fin k) :
    (data Q).value.energies j=MSManuscriptNumericalSamplerData.columnEnergy Q j := by
  simp only [data,squareSum_eval,KSEighthCountedMovement.factor_column,
    MSManuscriptNumericalSamplerData.columnEnergy,MSManuscriptNumericalLDL.lowerColumn_eq]
@[simp] theorem data_trace (Q : Mat k) : (data Q).value.trace=realTrace Q := by
  simp only [data,trace_eval]
@[simp] theorem data_labels (Q : Mat k) :
    (data Q).value.labels=MSManuscriptNumericalSamplerData.labels Q := by
  simp only [data,labels_value,MSManuscriptNumericalSamplerData.labels,
    MSManuscriptNumericalLDL.pivot_eq,KSEighthCountedMovement.factor_pivot]

theorem data_cost (Q : Mat k) : (data Q).cost≤120*(k+1)^5 := by
  have hf:=KSEighthCountedMovement.factor_cost Q
  have hl:=labels_cost (KSEighthCountedMovement.factor Q).value.1 (List.finRange k)
  simp only [List.length_finRange] at hl
  have hp2 : (k+1)^2≤(k+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1≤(k+1)^5 := Nat.one_le_pow _ _ (by omega)
  dsimp only [data]
  rw [hl,squareSum_cost,trace_cost]
  nlinarith

def weightExpr : Expr (Fin 3) :=
  .div (.mul (.input 0) (.input 1)) (.mul (.constant 2) (.input 2))
@[simp] theorem weight_eval (p e t : ℝ) : weightExpr.eval ![p,e,t]=p*e/(2*t) := by
  norm_num [weightExpr,Expr.eval,Matrix.cons_val_two]

def weights (Q : Mat k) : Counted (Draws Q → ℝ) :=
  let f:=data Q
  ⟨fun z=>
    let j:=MSManuscriptNumericalSamplerData.selectedLabel Q z
    weightExpr.eval ![f.value.pivots j,f.value.energies j,f.value.trace],
    f.cost+40*(k+1)^2⟩

theorem weights_value (Q : Mat k) (z : Draws Q) :
    (weights Q).value z=MSManuscriptNumericalSamplerData.weight Q z := by
  simp only [weights,data_pivots,data_energies,data_trace,weight_eval,
    MSManuscriptNumericalSamplerData.weight]

theorem weight_execution (Q : Mat k) (hq : 0<realTrace Q) (z : Draws Q) :
    let j:=MSManuscriptNumericalSamplerData.selectedLabel Q z
    Expr.Executes ![(data Q).value.pivots j,(data Q).value.energies j,(data Q).value.trace]
      weightExpr (MSManuscriptNumericalSamplerData.weight Q z) 7 := by
  dsimp only
  have ht : (data Q).value.trace≠0 := by rw [data_trace];exact hq.ne'
  have hv : weightExpr.Valid ![(data Q).value.pivots (MSManuscriptNumericalSamplerData.selectedLabel Q z),
      (data Q).value.energies (MSManuscriptNumericalSamplerData.selectedLabel Q z),(data Q).value.trace] := by
    simp [weightExpr,Expr.Valid,Expr.eval,Matrix.cons_val_two,hq.ne']
  have h:=Expr.executes_of_valid _ weightExpr hv
  rw [weight_eval] at h
  simpa only [data_pivots,data_energies,data_trace,weightExpr,Expr.cost,
    MSManuscriptNumericalSamplerData.weight] using h

theorem weights_cost (Q : Mat k) : (weights Q).cost≤160*(k+1)^5 := by
  have h:=data_cost Q
  have hp : (k+1)^2≤(k+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  dsimp only [weights]
  omega

def scaleExpr : Expr (Fin 2) := .div (.sqrt (.input 0)) (.sqrt (.input 1))
@[simp] theorem scale_eval (t e : ℝ) : scaleExpr.eval ![t,e]=Real.sqrt t/Real.sqrt e := by
  simp [scaleExpr,Expr.eval]

def increment (Q : Mat k) (z : Draws Q) : Counted (EuclideanSpace ℝ (Fin k)) :=
  let f:=data Q
  let j:=MSManuscriptNumericalSamplerData.selectedLabel Q z
  let a:=scaleExpr.eval ![f.value.trace,f.value.energies j]
  ⟨WithLp.toLp 2 (fun i=>if z.2 then a*f.value.columns j i else -(a*f.value.columns j i)),
    f.cost+30*k+30⟩

theorem increment_value (Q : Mat k) (z : Draws Q) :
    (increment Q z).value=MSManuscriptNumericalSamplerData.increment Q z := by
  ext i
  simp only [increment,data_columns,data_trace,data_energies,scale_eval,
    MSManuscriptNumericalSamplerData.increment]
  cases z.2 <;> simp

theorem increment_cost (Q : Mat k) (z : Draws Q) :
    (increment Q z).cost≤180*(k+1)^5 := by
  have h:=data_cost Q
  have hp : k+1≤(k+1)^5 := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (show 1≤k+1 by omega) (show 1≤5 by omega))
  dsimp only [increment]
  omega

theorem scale_execution (Q : Mat k) (hq : 0<realTrace Q) (z : Draws Q) :
    let j:=MSManuscriptNumericalSamplerData.selectedLabel Q z
    Expr.Executes ![(data Q).value.trace,(data Q).value.energies j] scaleExpr
      (Real.sqrt (realTrace Q)/Real.sqrt (MSManuscriptNumericalSamplerData.columnEnergy Q j)) 5 := by
  dsimp only
  have he:=(MSManuscriptNumericalSamplerData.denominators_positive Q hq z).2.1
  have hp:0≤MSManuscriptNumericalSamplerData.columnEnergy Q
      (MSManuscriptNumericalSamplerData.selectedLabel Q z) := by
    unfold MSManuscriptNumericalSamplerData.columnEnergy
    positivity
  have hv : scaleExpr.Valid ![(data Q).value.trace,(data Q).value.energies
      (MSManuscriptNumericalSamplerData.selectedLabel Q z)] := by
    change (True ∧ 0≤(data Q).value.trace) ∧
      (True ∧ 0≤(data Q).value.energies _) ∧ Real.sqrt ((data Q).value.energies _)≠0
    rw [data_trace,data_energies]
    exact ⟨⟨trivial,hq.le⟩,⟨trivial,hp⟩,he.ne'⟩
  have h:=Expr.executes_of_valid _ scaleExpr hv
  rw [scale_eval] at h
  simpa only [data_trace,data_energies,scaleExpr,Expr.cost] using h

end MatrixSpencer.RealRAM.MSSampling
