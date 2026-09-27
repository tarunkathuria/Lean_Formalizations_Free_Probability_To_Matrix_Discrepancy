import MatrixSpencer.RealRAMJacobiIteration
import MatrixSpencer.KSManuscriptInputBudgetBounds
import MatrixSpencer.KSEighthManuscriptPreprocess

/-!
# Primitive entry arithmetic for the actual KS input budgets

Each atom size is computed from original real and imaginary entries. Exact
rank-one energy identities reduce all lifted matrix budgets to scalar square
roots of these sizes. No matrix norm, eigensolver, or matrix square root is
evaluated. The finite maximum and zero-label filter preserve their original
ordered-list definitions. This module counts arithmetic and finite control;
the following scalar parameter circuit composes these stored outputs.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RealRAM.KSInputSetup
open JacobiIteration (Counted)
open KSManuscriptInputBudgetBounds KSOwnerInputBounds
variable {N d : ℕ}

abbrev Registers (N d : ℕ) := Fin N × Fin d × Bool

def input (v : Fin N → Fin d → ℂ) : Registers N d → ℝ :=
  fun p => if p.2.2 then (v p.1 p.2.1).im else (v p.1 p.2.1).re

def square {ι : Type*} (e : Expr ι) : Expr ι := .mul e e

theorem square_eval {ι : Type*} (e : Expr ι) (v : ι → ℝ) :
    (square e).eval v = (e.eval v)^2 := by simp [square,Expr.eval,pow_two]

def normSqExpr (i : Fin N) (j : Fin d) : Expr (Registers N d) :=
  .add (square (.input (i,j,false))) (square (.input (i,j,true)))

theorem normSqExpr_eval (v : Fin N → Fin d → ℂ) (i : Fin N) (j : Fin d) :
    (normSqExpr i j).eval (input v) = Complex.normSq (v i j) := by
  simp [normSqExpr,square,Expr.eval,input,Complex.normSq_apply]

theorem normSqExpr_valid (v : Registers N d → ℝ) (i : Fin N) (j : Fin d) :
    (normSqExpr i j).Valid v := by simp [normSqExpr,square,Expr.Valid]

def sizeExpr (i : Fin N) : Expr (Registers N d) :=
  Expr.sumList (List.ofFn (normSqExpr i))

theorem sizeExpr_eval (v : Fin N → Fin d → ℂ) (i : Fin N) :
    (sizeExpr i).eval (input v) = KSEighthManuscriptPreprocess.size v i := by
  simp [sizeExpr,Expr.eval_sumList,List.map_ofFn,normSqExpr_eval,List.sum_ofFn,
    KSEighthManuscriptPreprocess.size]

theorem sizeExpr_valid (v : Registers N d → ℝ) (i : Fin N) : (sizeExpr i).Valid v := by
  apply Expr.valid_sumList
  intro e he
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
  exact normSqExpr_valid v i j

theorem sizeExpr_cost (i : Fin N) : (sizeExpr (d:=d) i).cost = 8*d+1 := by
  simp [sizeExpr,Expr.cost_sumList,List.map_ofFn,List.sum_ofFn,normSqExpr,square,Expr.cost]
  omega

def sizes (v : Fin N → Fin d → ℂ) : Counted (Fin N → ℝ) :=
  ⟨fun i => (sizeExpr i).eval (input v),N*(8*d+4)+1⟩

theorem sizes_value (v : Fin N → Fin d → ℂ) :
    (sizes v).value = KSEighthManuscriptPreprocess.size v := by
  funext i
  exact sizeExpr_eval v i

theorem sizes_entry_execution (v : Fin N → Fin d → ℂ) (i : Fin N) :
    Expr.Executes (input v) (sizeExpr i) ((sizes v).value i) (8*d+1) := by
  simpa only [sizeExpr_cost] using Expr.executes_of_valid (input v) (sizeExpr i) (sizeExpr_valid _ i)

def maximum : List ℝ → Counted ℝ
  | [] => ⟨0,2⟩
  | a::as => let t := maximum as; ⟨if a ≤ t.value then t.value else a,t.cost+5⟩

theorem maximum_value (as : List ℝ) :
    (maximum as).value = KSEighthManuscriptPreprocess.maximum as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [maximum,ih,KSEighthManuscriptPreprocess.maximum,max_def]

theorem maximum_cost (as : List ℝ) : (maximum as).cost = 5*as.length+2 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [maximum,ih]; omega

def filterLabels (q : Fin N → ℝ) : List (Fin N) → Counted (List (Fin N))
  | [] => ⟨[],1⟩
  | i::is => let t := filterLabels q is
            ⟨if q i=0 then t.value else i::t.value,t.cost+8⟩

theorem filterLabels_value (q : Fin N → ℝ) (is : List (Fin N)) :
    (filterLabels q is).value = is.filter (fun i => decide (q i≠0)) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [filterLabels,ih]; split_ifs <;> simp_all

theorem filterLabels_cost (q : Fin N → ℝ) (is : List (Fin N)) :
    (filterLabels q is).cost = 8*is.length+1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [filterLabels,ih]; omega

def atomBoundExpr (i : Fin N) : Expr (Fin N) :=
  .add (.constant 1) (.sqrt (square (.input i)))

def liftBoundExpr (i : Fin N) : Expr (Fin N) :=
  .add (.constant 1) (.sqrt (.mul (.constant 2) (square (.input i))))

theorem atomBoundExpr_eval (q : Fin N → ℝ) (i : Fin N) :
    (atomBoundExpr i).eval q = 1+Real.sqrt (q i^2) := by
  simp [atomBoundExpr,Expr.eval,square_eval]

theorem liftBoundExpr_eval (q : Fin N → ℝ) (i : Fin N) :
    (liftBoundExpr i).eval q = 1+Real.sqrt (2*q i^2) := by
  simp [liftBoundExpr,Expr.eval,square_eval]

theorem atomBoundExpr_valid (q : Fin N → ℝ) (i : Fin N) : (atomBoundExpr i).Valid q := by
  simp only [atomBoundExpr,Expr.Valid,square,Expr.eval]
  exact ⟨trivial,⟨⟨trivial,trivial⟩,mul_self_nonneg _⟩⟩

theorem liftBoundExpr_valid (q : Fin N → ℝ) (i : Fin N) : (liftBoundExpr i).Valid q := by
  simp only [liftBoundExpr,Expr.Valid,square,Expr.eval]
  refine ⟨trivial,⟨⟨trivial,⟨trivial,trivial⟩⟩,?_⟩⟩
  exact mul_nonneg (by norm_num) (mul_self_nonneg _)

theorem atomBound_eq (v : Fin N → Fin d → ℂ) (i : Fin N) :
    (atomBoundExpr i).eval (KSEighthManuscriptPreprocess.size v) = matrixBound (KSRankOne.atom (v i)) := by
  rw [atomBoundExpr_eval,KSEighthManuscriptPreprocess.size_eq_norm]
  simp [matrixBound,energy_atom]

theorem liftBound_eq (v : Fin N → Fin d → ℂ) (i : Fin N) :
    (liftBoundExpr i).eval (KSEighthManuscriptPreprocess.size v) =
      matrixBound (signedLift (KSRankOne.atom (v i))) := by
  rw [liftBoundExpr_eval,KSEighthManuscriptPreprocess.size_eq_norm]
  simp [matrixBound,energy_signedLift,energy_atom]

theorem doubledBound_eq (v : Fin N → Fin d → ℂ) (i : Fin N) :
    (liftBoundExpr i).eval (KSEighthManuscriptPreprocess.size v) =
      matrixBound (KSSpinSource.doubled (KSRankOne.atom (v i))) := by
  rw [liftBoundExpr_eval,KSEighthManuscriptPreprocess.size_eq_norm]
  simp [matrixBound,energy_doubled,energy_atom]

theorem pauliBound_eq (v : Fin N → Fin d → ℂ) (i : Fin N) (b : Fin 4) :
    (liftBoundExpr i).eval (KSEighthManuscriptPreprocess.size v) =
      matrixBound (KSSpinSource.family (fun j => KSRankOne.atom (v j)) (i,b)) := by
  rw [liftBoundExpr_eval,KSEighthManuscriptPreprocess.size_eq_norm]
  simp [matrixBound,KSSpinSource.family,energy_pauli,energy_atom]

theorem independentBound_eq (v : Fin N → Fin d → ℂ) (i : Fin N) (b : Bool) :
    (atomBoundExpr i).eval (KSEighthManuscriptPreprocess.size v) =
      matrixBound (KSEighthActualState.family v (i,b)) := by
  rw [atomBoundExpr_eval,KSEighthManuscriptPreprocess.size_eq_norm]
  cases b <;> simp [matrixBound,KSEighthActualState.family,KSIndependentSource.family,
    energy_leftDensity,energy_rightDensity,energy_atom]

def sumExpr (f : Fin N → Expr (Fin N)) := Expr.sumList (List.ofFn f)

theorem sumExpr_eval (f : Fin N → Expr (Fin N)) (q : Fin N → ℝ) :
    (sumExpr f).eval q = ∑i,(f i).eval q := by
  simp [sumExpr,Expr.eval_sumList,List.map_ofFn,List.sum_ofFn]

theorem sumExpr_valid (f : Fin N → Expr (Fin N)) (q : Fin N → ℝ)
    (hf : ∀i,(f i).Valid q) : (sumExpr f).Valid q := by
  apply Expr.valid_sumList
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  exact hf i

def budgetCircuit (N d : ℕ) : Circuit (Fin N) (Fin 5) where
  output k := if k=0 then .add (.constant 1) (sumExpr atomBoundExpr)
    else if k=1 then .add (.constant 1) (sumExpr liftBoundExpr)
    else if k=2 then .add (.constant 1)
      (.mul (.constant 128) (sumExpr (fun i => square (liftBoundExpr i))))
    else if k=3 then .add (.constant 1)
      (.mul (.constant (2560*d)) (sumExpr (fun i => square (liftBoundExpr i))))
    else .add (.constant 1)
      (.mul (.constant (5120*d)) (sumExpr (fun i => square (atomBoundExpr i))))

theorem budgetCircuit_valid (q : Fin N → ℝ) : (budgetCircuit N d).Valid q := by
  intro k
  dsimp [budgetCircuit]
  split_ifs <;> simp only [Expr.Valid]
  · exact ⟨trivial,sumExpr_valid _ q (atomBoundExpr_valid q)⟩
  · exact ⟨trivial,sumExpr_valid _ q (liftBoundExpr_valid q)⟩
  · exact ⟨trivial,⟨trivial,sumExpr_valid _ q (fun i => ⟨liftBoundExpr_valid q i,liftBoundExpr_valid q i⟩)⟩⟩
  · exact ⟨trivial,⟨trivial,sumExpr_valid _ q (fun i => ⟨liftBoundExpr_valid q i,liftBoundExpr_valid q i⟩)⟩⟩
  · exact ⟨trivial,⟨trivial,sumExpr_valid _ q (fun i => ⟨atomBoundExpr_valid q i,atomBoundExpr_valid q i⟩)⟩⟩

theorem budgetCircuit_cost : (budgetCircuit N d).cost ≤ 200*(N+1) := by
  have hf (k : Fin 5) : ((budgetCircuit N d).output k).cost+1 ≤ 40*(N+1) := by
    dsimp [budgetCircuit]
    split_ifs <;> simp [Expr.cost,sumExpr,Expr.cost_sumList,List.map_ofFn,List.sum_ofFn,
      atomBoundExpr,liftBoundExpr,square] <;> omega
  calc
    _ ≤ ∑_k : Fin 5,40*(N+1) := Finset.sum_le_sum fun k _ => hf k
    _ = _ := by simp; ring

theorem budgetCircuit_outputs (v : Fin N → Fin d → ℂ) :
    let b := (budgetCircuit N d).eval (KSEighthManuscriptPreprocess.size v)
    b 0 = KSDebitUniformFloor.atomBudget v ∧
    b 1 = KSComplexPolynomialBounds.slopeBudget v ∧
    b 2 = KSDebitUniformFloor.spinBudget v ∧
    b 3 = KSComplexPolynomialBounds.sourceBudget v ∧
    b 4 = KSEighthInputTaylorBound.sourceCap v := by
  dsimp only
  have hpauli : (∑j : Fin N × Fin 4,
      matrixBound (KSSpinSource.family (fun i => KSRankOne.atom (v i)) j)^2) =
      4 * ∑i,((liftBoundExpr i).eval (KSEighthManuscriptPreprocess.size v))^2 := by
    simp only [Fintype.sum_prod_type,←pauliBound_eq,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum]
    norm_num
  have hind : (∑j : Fin N × Bool,matrixBound (KSEighthActualState.family v j)^2) =
      2 * ∑i,((atomBoundExpr i).eval (KSEighthManuscriptPreprocess.size v))^2 := by
    simp only [Fintype.sum_prod_type,←independentBound_eq,Finset.sum_const,Finset.card_univ,
      Fintype.card_bool,nsmul_eq_mul,←Finset.mul_sum]
    norm_num
  constructor
  · simp [Circuit.eval,budgetCircuit,Expr.eval,sumExpr_eval,atomBound_eq,KSDebitUniformFloor.atomBudget]
  constructor
  · simp [Circuit.eval,budgetCircuit,Expr.eval,sumExpr_eval,liftBound_eq,KSComplexPolynomialBounds.slopeBudget]
  constructor
  · simp [Circuit.eval,budgetCircuit,Expr.eval,sumExpr_eval,square_eval,KSDebitUniformFloor.spinBudget,hpauli]
    ring
  constructor
  · change (Expr.add (.constant 1) (.mul (.constant (2560*d))
      (sumExpr (fun i => square (liftBoundExpr i))))).eval
      (KSEighthManuscriptPreprocess.size v) = KSComplexPolynomialBounds.sourceBudget v
    simp only [Expr.eval,sumExpr_eval,square_eval,
      KSComplexPolynomialBounds.sourceBudget,KSComplexSpinSource.atom,←doubledBound_eq,
      Fintype.card_sum,Fintype.card_fin,Nat.cast_add,Rat.cast_one,Rat.cast_mul,
      Rat.cast_natCast,Rat.cast_ofNat]
    ring
  · simp [Circuit.eval,budgetCircuit,Expr.eval,sumExpr_eval,square_eval,
      KSEighthInputTaylorBound.sourceCap,KSComplexTraceBounds.sourceBudget,hind]
    ring

structure Data (N : ℕ) where
  sizes : Fin N → ℝ
  epsilon : ℝ
  labels : List (Fin N)
  budgets : Fin 5 → ℝ

def compute (v : Fin N → Fin d → ℂ) : Counted (Data N) :=
  let q := sizes v
  let eps := maximum ((List.finRange N).map q.value)
  let labels := filterLabels q.value (List.finRange N)
  let b := budgetCircuit N d
  ⟨⟨q.value,eps.value,labels.value,b.eval q.value⟩,
    q.cost+eps.cost+labels.cost+b.cost+10*N+20⟩

theorem compute_outputs (v : Fin N → Fin d → ℂ) :
    (compute v).value.sizes = KSEighthManuscriptPreprocess.size v ∧
    (compute v).value.epsilon = KSEighthManuscriptPreprocess.epsilon v ∧
    (compute v).value.labels = KSEighthManuscriptPreprocess.labels v ∧
    (compute v).value.budgets 0 = KSDebitUniformFloor.atomBudget v ∧
    (compute v).value.budgets 1 = KSComplexPolynomialBounds.slopeBudget v ∧
    (compute v).value.budgets 2 = KSDebitUniformFloor.spinBudget v ∧
    (compute v).value.budgets 3 = KSComplexPolynomialBounds.sourceBudget v ∧
    (compute v).value.budgets 4 = KSEighthInputTaylorBound.sourceCap v := by
  have hb := budgetCircuit_outputs v
  simpa [compute,sizes_value,maximum_value,filterLabels_value,
    KSEighthManuscriptPreprocess.epsilon,KSEighthManuscriptPreprocess.labels] using hb

theorem compute_cost (v : Fin N → Fin d → ℂ) : (compute v).cost ≤ 300*(N+1)*(d+1) := by
  have hb := budgetCircuit_cost (N:=N) (d:=d)
  simp only [compute,sizes,maximum_cost,filterLabels_cost,List.length_map,List.length_finRange]
  nlinarith

theorem budget_entry_execution (v : Fin N → Fin d → ℂ) (k : Fin 5) :
    Expr.Executes (sizes v).value ((budgetCircuit N d).output k)
      ((compute v).value.budgets k) ((budgetCircuit N d).output k).cost :=
  Expr.executes_of_valid _ _ (budgetCircuit_valid _ k)

end MatrixSpencer.RealRAM.KSInputSetup
