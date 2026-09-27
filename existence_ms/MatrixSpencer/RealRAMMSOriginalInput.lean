import MatrixSpencer.MSConvexRawInput
import MatrixSpencer.RealRAMComplexArithmetic
import MatrixSpencer.RealRAMKSLoopCapSetup

/-! Original-matrix preprocessing by literal real-entry arithmetic and finite
address operations. The physical equivalence is the explicit test i<D followed
by a subtraction, with a proved identity to finSumFinEquiv.symm. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.MSOriginalInput
open JacobiIteration (Counted)
variable {N D : ℕ}
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

def block (i : Fin (D+D)) : Fin D⊕Fin D :=
  if h:i.val<D then .inl ⟨i.val,h⟩ else .inr ⟨i.val-D,by have hi:=i.isLt;omega⟩

theorem block_value (i : Fin (D+D)) : block i=finSumFinEquiv.symm i := by
  apply finSumFinEquiv.injective
  rw [Equiv.apply_symm_apply]
  unfold block
  split_ifs <;> apply Fin.ext <;> simp [finSumFinEquiv] <;> omega

/-- This array uses one natural comparison and at most one subtraction per
entry; its charge includes writes and the two tagged coordinate arrays. -/
def blockTable (D : ℕ) : Counted (Fin (D+D) → Fin D⊕Fin D) :=
  ⟨block,10*(D+D)+1⟩
theorem blockTable_value : (blockTable D).value=finSumFinEquiv.symm := funext block_value

abbrev Entries (D : ℕ) := Fin D×Fin D×Bool
def input (A : CMatrix D) : Entries D → ℝ :=
  fun p=>if p.2.2 then (A p.1 p.2.1).im else (A p.1 p.2.1).re
def atom (i j : Fin D) : ComplexExpr (Entries D) :=
  ⟨.input (i,j,false),.input (i,j,true)⟩
def liftExpr : (Fin D⊕Fin D) → (Fin D⊕Fin D) → ComplexExpr (Entries D)
  | .inl i,.inl j=>atom i j
  | .inr i,.inr j=>.smul (.constant (-1)) (atom i j)
  | _,_=>.zero

theorem liftExpr_eval (A : CMatrix D) (i j : Fin D⊕Fin D) :
    (liftExpr i j).eval (input A)=signedLift A i j := by
  cases i <;> cases j <;> apply Complex.ext <;>
    simp [liftExpr,atom,input,ComplexExpr.eval,ComplexExpr.zero,ComplexExpr.smul,
      Expr.eval,signedLift,Matrix.fromBlocks,Matrix.neg_apply]

theorem liftExpr_valid (v : Entries D → ℝ) (i j : Fin D⊕Fin D) :
    (liftExpr i j).Valid v := by
  cases i <;> cases j <;> simp [liftExpr,atom,ComplexExpr.Valid,ComplexExpr.zero,
    ComplexExpr.smul,Expr.Valid]

theorem liftExpr_cost (i j : Fin D⊕Fin D) : (liftExpr i j).cost ≤ 6 := by
  cases i <;> cases j <;> norm_num [liftExpr,atom,ComplexExpr.cost,ComplexExpr.zero,
    ComplexExpr.smul,Expr.cost]

def lift (A : CMatrix D) : Counted (Matrix (Fin D⊕Fin D) (Fin D⊕Fin D) ℂ) :=
  ⟨fun i j=>(liftExpr i j).eval (input A),
    (∑i:Fin D⊕Fin D,∑j:Fin D⊕Fin D,((liftExpr i j).cost+2))+10*(D+D)^2+1⟩
theorem lift_value (A : CMatrix D) : (lift A).value=signedLift A := by
  ext i j
  exact liftExpr_eval A i j
theorem lift_cost (A : CMatrix D) : (lift A).cost ≤ 80*(D+1)^2 := by
  have h:=Finset.sum_le_sum (fun (i : Fin D⊕Fin D) (_ : i∈Finset.univ)=>Finset.sum_le_sum
    (fun (j : Fin D⊕Fin D) (_ : j∈Finset.univ)=>Nat.add_le_add_right (liftExpr_cost i j) 2))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_sum,Fintype.card_fin,smul_eq_mul] at h
  dsimp only [lift]
  nlinarith

theorem lift_execution (A : CMatrix D) (i j : Fin D⊕Fin D) :
    Expr.Executes (input A) (liftExpr i j).re ((signedLift A i j).re) (liftExpr i j).re.cost ∧
    Expr.Executes (input A) (liftExpr i j).im ((signedLift A i j).im) (liftExpr i j).im.cost := by
  have h:=liftExpr_eval A i j
  have hv:=liftExpr_valid (input A) i j
  constructor
  · convert Expr.executes_of_valid (input A) (liftExpr i j).re hv.1 using 1
    exact (congrArg Complex.re h).symm
  · convert Expr.executes_of_valid (input A) (liftExpr i j).im hv.2 using 1
    exact (congrArg Complex.im h).symm

def marginExpr : Expr Unit :=
  .div (.constant 1) (.mul (.constant 1000) (.add (.input ()) (.constant 1)))
theorem margin_execution (N : ℕ) :
    Expr.Executes (fun _=>(N:ℝ)) marginExpr (signingEpsilon (Fin N)) 7 := by
  have hv:marginExpr.Valid (fun _=>(N:ℝ)) := by
    simp only [marginExpr,Expr.Valid,Expr.eval]
    norm_num
    positivity
  simpa [marginExpr,Expr.eval,Expr.cost,signingEpsilon] using Expr.executes_of_valid _ _ hv

def retryExpr : NatExpr Unit :=
  .add (.mul (.add (.input ()) (.constant 1)) (.constant 98625)) (.constant 1)
theorem retry_value (N : ℕ) : retryExpr.eval (fun _=>N)=
    MSManuscriptRetryBudget.retries N MSManuscriptNumericalHalfPhase.epochCalls := rfl
theorem retry_cost : retryExpr.cost=7 := rfl
theorem retry_execution (N : ℕ) :
    NatExpr.Executes (fun _=>N) retryExpr
      (MSManuscriptRetryBudget.retries N MSManuscriptNumericalHalfPhase.epochCalls) 7 :=
  retryExpr.executes _

structure Data (N D : ℕ) where
  family : Fin N → Matrix (Fin D⊕Fin D) (Fin D⊕Fin D) ℂ
  coordinates : Fin (D+D) → Fin D⊕Fin D
  flat : Fin N → CMatrix (D+D)
  start : EuclideanSpace ℝ (Fin N)
  offset : Matrix (Fin D⊕Fin D) (Fin D⊕Fin D) ℂ
  margin : ℝ
  retries : ℕ

def setup (A : Fin N → CMatrix D) : Counted (Data N D) :=
  let f:=fun i=>lift (A i)
  let e:=blockTable D
  ⟨⟨fun i=>(f i).value,e.value,fun i=>(f i).value.submatrix e.value e.value,
      WithLp.toLp 2 (fun _=>0),fun _ _=>0,marginExpr.eval (fun _=>(N:ℝ)),
      retryExpr.eval (fun _=>N)⟩,
    (∑i,(f i).cost)+e.cost+30*N*(D+D)^2+20*(N+D+1)^2+marginExpr.cost+retryExpr.cost+20⟩

theorem family_value (A : Fin N → CMatrix D) :
    (setup A).value.family=fun i=>signedLift (A i) := funext (fun i=>lift_value (A i))
theorem coordinates_value (A : Fin N → CMatrix D) :
    (setup A).value.coordinates=finSumFinEquiv.symm := blockTable_value
theorem flat_value (A : Fin N → CMatrix D) :
    (setup A).value.flat=fun i=>(signedLift (A i)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  simp only [setup,lift_value,blockTable_value]
theorem start_value (A : Fin N → CMatrix D) : (setup A).value.start=0 := by
  ext i
  rfl
theorem offset_value (A : Fin N → CMatrix D) : (setup A).value.offset=0 := rfl
theorem margin_value (A : Fin N → CMatrix D) :
    (setup A).value.margin=signingEpsilon (Fin N) := by
  simp [setup,marginExpr,Expr.eval,signingEpsilon]
theorem retries_value (A : Fin N → CMatrix D) :
    (setup A).value.retries=MSManuscriptRetryBudget.retries N MSManuscriptNumericalHalfPhase.epochCalls := rfl

theorem setup_cost (A : Fin N → CMatrix D) : (setup A).cost ≤ 1000*(N+D+1)^3 := by
  have h:=Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>lift_cost (A i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  have hND : N*(D+1)^2 ≤ (N+D+1)^3 := by
    calc _ ≤ (N+D+1)*(N+D+1)^2 := by gcongr <;> omega
         _=_ := by ring
  have hND' : N*(D+D)^2 ≤ 4*(N+D+1)^3 := by
    have hsq : (D+D)^2 ≤ 4*(D+1)^2 := by
      calc _=4*D^2 := by ring
           _ ≤ _ := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.le_succ D) 2)
    have hmul:=Nat.mul_le_mul_left N hsq
    nlinarith
  have h2 : (N+D+1)^2 ≤ (N+D+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : N+D+1 ≤ (N+D+1)^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (n:=N+D+1) (by omega) (show 1≤3 by omega)
  dsimp only [setup,blockTable]
  norm_num only [marginExpr,Expr.cost,retry_cost]
  nlinarith

end MatrixSpencer.RealRAM.MSOriginalInput
