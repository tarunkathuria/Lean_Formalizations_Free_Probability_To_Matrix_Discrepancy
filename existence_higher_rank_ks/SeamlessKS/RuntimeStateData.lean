import SeamlessKS.Value
import SeamlessKS.SourceEvaluation
import MatrixSpencer.RealRAMComplexArithmetic
import MatrixSpencer.RealRAMProgram

/-! Primitive construction of the actual smooth-walk query data. The input
contains only original vectors and current coefficients; there is no
rounding account or debit register. Every complex entry is a pair of real arithmetic expressions.
The covariance coefficients use the new smooth source expression. -/
open Matrix Set
open scoped BigOperators
noncomputable section
namespace SeamlessKS.RuntimeStateData
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
variable {N d : ℕ}

abbrev Registers (N d : ℕ) := ((Fin N × Fin d) × Bool) ⊕ Fin N

def input (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) : Registers N d → ℝ :=
  Sum.elim (fun p => if p.2 then (v p.1.1 p.1.2).im else (v p.1.1 p.1.2).re)
    x

def vectorExpr (i : Fin N) (j : Fin d) : ComplexExpr (Registers N d) :=
  ⟨.input (.inl ((i,j),false)),.input (.inl ((i,j),true))⟩

@[simp] theorem vectorExpr_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ)
    (i : Fin N) (j : Fin d) : (vectorExpr i j).eval (input v x)=v i j := by
  apply Complex.ext <;> rfl

def atomExpr (i : Fin N) (j k : Fin d) : ComplexExpr (Registers N d) :=
  .mul (vectorExpr i j) (.conj (vectorExpr i k))

@[simp] theorem atomExpr_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ)
    (i : Fin N) (j k : Fin d) : (atomExpr i j k).eval (input v x)=KSRankOne.atom (v i) j k := by
  simp [atomExpr,KSRankOne.atom_apply]

@[simp] theorem atomExpr_cost (i : Fin N) (j k : Fin d) : (atomExpr i j k).cost=18 := rfl

theorem atomExpr_valid (u : Registers N d → ℝ) (i : Fin N) (j k : Fin d) :
    (atomExpr i j k).Valid u := by
  exact ComplexExpr.valid_mul ⟨trivial,trivial⟩
    (ComplexExpr.valid_conj ⟨trivial,trivial⟩)

def sumExpr (j k : Fin d) : ComplexExpr (Registers N d) :=
  .sum (fun i => .smul (.input (.inr i)) (atomExpr i j k))

@[simp] theorem sumExpr_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ)
    (j k : Fin d) : (sumExpr j k).eval (input v x)=
      StatePotential.signedSum v x j k := by
  rw [sumExpr,ComplexExpr.eval_sum]
  simp only [ComplexExpr.eval_smul,atomExpr_eval]
  simp [Expr.eval,input,StatePotential.signedSum,Matrix.sum_apply,Matrix.smul_apply]

@[simp] theorem sumExpr_cost (j k : Fin d) : (sumExpr (N:=N) j k).cost=24*N+2 := by
  simp [sumExpr,ComplexExpr.cost_sum,ComplexExpr.cost_smul,Expr.cost]
  omega

theorem sumExpr_valid (u : Registers N d → ℝ) (j k : Fin d) :
    (sumExpr j k).Valid u :=
  ComplexExpr.valid_sum _ _ (fun i => ComplexExpr.valid_smul trivial (atomExpr_valid u i j k))

/-- The center is exactly the signed lift of the current discrepancy.
There is no additional state array or accumulated rounding term. -/
def blockCenterExpr : (Fin d ⊕ Fin d) → (Fin d ⊕ Fin d) → ComplexExpr (Registers N d)
  | .inl j,.inl k => sumExpr j k
  | .inr j,.inr k => .smul (.constant (-1)) (sumExpr j k)
  | _,_ => .zero

@[simp] theorem blockCenterExpr_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ)
    (j k : Fin d ⊕ Fin d) : (blockCenterExpr j k).eval (input v x)=
      KSDebitCenter.center (StatePotential.signedSum v x) 0 j k := by
  rw [KSDebitCenter.center_eq_blocks]
  cases j <;> cases k <;>
    simp [blockCenterExpr,Expr.eval,Matrix.fromBlocks,Matrix.neg_apply,sub_eq_add_neg]

theorem blockCenterExpr_cost (j k : Fin d ⊕ Fin d) :
    (blockCenterExpr (N:=N) j k).cost≤100*(N+1) := by
  cases j <;> cases k <;>
    simp [blockCenterExpr,ComplexExpr.cost_smul,ComplexExpr.cost_zero,Expr.cost] <;> omega

theorem blockCenterExpr_valid (u : Registers N d → ℝ) (j k : Fin d ⊕ Fin d) :
    (blockCenterExpr j k).Valid u := by
  cases j <;> cases k
  · exact sumExpr_valid u _ _
  · exact ComplexExpr.valid_zero u
  · exact ComplexExpr.valid_zero u
  · exact ComplexExpr.valid_smul trivial (sumExpr_valid u _ _)

def pauliExpr (i : Fin N) : Fin 4 → (Fin d ⊕ Fin d) → (Fin d ⊕ Fin d) → ComplexExpr (Registers N d)
  | 0,.inl j,.inl k => atomExpr i j k
  | 0,.inr j,.inr k => atomExpr i j k
  | 1,.inl j,.inr k => atomExpr i j k
  | 1,.inr j,.inl k => atomExpr i j k
  | 2,.inl j,.inr k => .mul ⟨.constant 0,.constant (-1)⟩ (atomExpr i j k)
  | 2,.inr j,.inl k => .mul ⟨.constant 0,.constant 1⟩ (atomExpr i j k)
  | 3,.inl j,.inl k => atomExpr i j k
  | 3,.inr j,.inr k => .smul (.constant (-1)) (atomExpr i j k)
  | _,_,_ => .zero

theorem pauliExpr_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ)
    (i : Fin N) (a : Fin 4) (j k : Fin d ⊕ Fin d) :
    (pauliExpr i a j k).eval (input v x)=KSSpinSource.family (fun i => KSRankOne.atom (v i)) (i,a) j k := by
  fin_cases a <;> cases j <;> cases k <;>
    simp [pauliExpr,KSSpinSource.family,KSSpinSource.pauli,KSSpinSource.doubled,
      signedLift,Matrix.fromBlocks,Matrix.smul_apply,atomExpr_eval,Expr.eval] <;>
    norm_num [ComplexExpr.eval,Expr.eval,Complex.ext_iff]


theorem pauliExpr_cost (i : Fin N) (a : Fin 4) (j k : Fin d ⊕ Fin d) :
    (pauliExpr i a j k).cost≤46 := by
  fin_cases a <;> cases j <;> cases k <;>
    simp [pauliExpr,ComplexExpr.cost_zero,ComplexExpr.cost_mul,ComplexExpr.cost_smul,
      atomExpr_cost,Expr.cost] <;> norm_num [ComplexExpr.cost,Expr.cost]

theorem pauliExpr_valid (u : Registers N d → ℝ) (i : Fin N) (a : Fin 4)
    (j k : Fin d ⊕ Fin d) : (pauliExpr i a j k).Valid u := by
  fin_cases a <;> cases j <;> cases k <;>
    first | exact atomExpr_valid u _ _ _ | exact ComplexExpr.valid_zero u |
      exact ComplexExpr.valid_smul trivial (atomExpr_valid u _ _ _) |
      exact ComplexExpr.valid_mul ⟨trivial,trivial⟩ (atomExpr_valid u _ _ _)



/-- The precise block enumeration used by `Value.report`. -/
abbrev dimension (d : ℕ) := Fintype.card (Fin d ⊕ Fin d)
def blockIndex (d : ℕ) : Fin (dimension d) ≃ (Fin d ⊕ Fin d) :=
  Value.blockIndex d

@[simp] theorem dimension_eq (d : ℕ) : dimension d=d+d := by simp [dimension]

/-- Runtime block routing takes the physical dimension and index as inputs,
and returns a left/right tag and the within-block index using one comparison
and, in the right block, one subtraction.
Both indices of every matrix entry are routed; these operations are charged
in `compute`, independently of scalar entry evaluation. -/
def routeProgram : Program (Fin 4) :=
  .branchLE (.input 1) (.input 0)
    (.seq (.assign 2 (.constant 1)) (.assign 3 (.sub (.input 0) (.input 1))))
    (.seq (.assign 2 (.constant 0)) (.assign 3 (.input 0)))

def routeInput (d : ℕ) (j : Fin (dimension d)) : Fin 4 → ℝ := ![(j.val:ℝ),(d:ℝ),0,0]

@[simp] theorem blockIndex_symm_inl_val (d : ℕ) (i : Fin d) :
    ((blockIndex d).symm (.inl i)).val=i.val := rfl
@[simp] theorem blockIndex_symm_inr_val (d : ℕ) (i : Fin d) :
    ((blockIndex d).symm (.inr i)).val=d+i.val := rfl

theorem routeProgram_output (d : ℕ) (j : Fin (dimension d)) :
    (routeProgram.run (routeInput d j) 2 = Sum.elim (fun _ => (0:ℝ)) (fun _ => 1) (blockIndex d j)) ∧
    (routeProgram.run (routeInput d j) 3 = Sum.elim (fun i => (i.val:ℝ)) (fun i => (i.val:ℝ)) (blockIndex d j)) := by
  obtain ⟨i,rfl⟩ := (blockIndex d).symm.surjective j
  rw [Equiv.apply_symm_apply]
  cases i with
  | inl i =>
    have hi : ¬ (d:ℝ)≤(i.val:ℝ) := by exact_mod_cast not_le.mpr i.isLt
    simp [routeInput,routeProgram,Program.run,Expr.eval,hi]
  | inr i =>
    have hi : (d:ℝ)≤(d:ℝ)+(i.val:ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
    simp [routeInput,routeProgram,Program.run,Expr.eval,hi]

theorem routeProgram_safe (v : Fin 4 → ℝ) : routeProgram.Safe v := by
  simp [routeProgram,Program.Safe,Expr.Valid]

theorem routeProgram_bound : routeProgram.bound=9 := rfl


/-- A uniform primitive execution computes the exact mathematical block map.
The program is independent of the dimension; `d` and `j` are its inputs. -/
theorem blockIndex_execution (d : ℕ) (j : Fin (dimension d)) :
    ∃ w k, Program.Executes routeProgram (routeInput d j) w k ∧ k≤9 ∧
      w 2=Sum.elim (fun _ => (0:ℝ)) (fun _ => 1) (blockIndex d j) ∧
      w 3=Sum.elim (fun i => (i.val:ℝ)) (fun i => (i.val:ℝ)) (blockIndex d j) := by
  refine ⟨routeProgram.run (routeInput d j),routeProgram.cost (routeInput d j),
    Program.executes_of_safe _ _ (routeProgram_safe _),?_,
    (routeProgram_output d j).1,(routeProgram_output d j).2⟩
  simpa only [routeProgram_bound] using Program.cost_le_bound routeProgram (routeInput d j)

def covarianceExpr (i j : Fin N × Fin 4) : Expr (Fin 2) :=
  if i=j then .div SourceEvaluation.weightExpr (.constant 2) else .constant 0

@[simp] theorem covarianceExpr_eval (x : Fin N → ℝ) (ζ : ℝ) (i j : Fin N × Fin 4) :
    (covarianceExpr i j).eval (SourceEvaluation.registers (x i.1) ζ)=
      KSSpinSource.coefficientCovariance (SourceTransport.smoothWeights ζ x) i j := by
  by_cases he : i=j <;> simp [covarianceExpr,he,Expr.eval,KSSpinSource.coefficientCovariance,
    SourceTransport.smoothWeights]

theorem covarianceExpr_valid (x : Fin N → ℝ) (ζ : ℝ) (i j : Fin N × Fin 4) :
    (covarianceExpr i j).Valid (SourceEvaluation.registers (x i.1) ζ) := by
  unfold covarianceExpr
  split_ifs
  · exact ⟨SourceEvaluation.weightExpr_valid _ _,trivial,by norm_num [Expr.eval]⟩
  · trivial

theorem covarianceExpr_cost (i j : Fin N × Fin 4) : (covarianceExpr i j).cost≤30 := by
  unfold covarianceExpr
  split_ifs <;> norm_num [Expr.cost,SourceEvaluation.weightExpr_cost]

structure Data (N d : ℕ) where
  H : Matrix (Fin (dimension d)) (Fin (dimension d)) ℂ
  A : (Fin N × Fin 4) → Matrix (Fin (dimension d)) (Fin (dimension d)) ℂ
  C : Matrix (Fin N × Fin 4) (Fin N × Fin 4) ℝ

/-- Literal finite arrays. Entry evaluation, stores, and finite routing work
are charged separately from constructing the SDP pencil. -/
def compute (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (ζ : ℝ) : Counted (Data N d) :=
  let e := blockIndex d
  let H : Matrix (Fin (dimension d)) (Fin (dimension d)) ℂ := fun j k =>
    (blockCenterExpr (e j) (e k)).eval (input v x)
  let A : (Fin N × Fin 4) → Matrix (Fin (dimension d)) (Fin (dimension d)) ℂ := fun i j k =>
    (pauliExpr i.1 i.2 (e j) (e k)).eval (input v x)
  let C : Matrix (Fin N × Fin 4) (Fin N × Fin 4) ℝ := fun i j =>
    (covarianceExpr i j).eval (SourceEvaluation.registers (x i.1) ζ)
  ⟨⟨H,A,C⟩,
    (∑ j : Fin (dimension d),∑ k : Fin (dimension d),((blockCenterExpr (N:=N) (e j) (e k)).cost+22))+
    (∑ i : Fin N×Fin 4,∑ j : Fin (dimension d),∑ k : Fin (dimension d),
      ((pauliExpr i.1 i.2 (e j) (e k)).cost+22))+
    (∑ i : Fin N×Fin 4,∑ j : Fin N×Fin 4,((covarianceExpr i j).cost+2))+
    10*(N+d+1)^2⟩

@[simp] theorem compute_H (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (ζ : ℝ) :
    (compute v x ζ).value.H=(KSDebitCenter.center
      (StatePotential.signedSum v x) 0).submatrix
        (blockIndex d) (blockIndex d) := by
  ext j k
  exact blockCenterExpr_eval v x _ _

@[simp] theorem compute_A (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (ζ : ℝ) :
    (compute v x ζ).value.A=(fun i =>
      (KSSpinSource.family (fun i => KSRankOne.atom (v i)) i).submatrix
        (blockIndex d) (blockIndex d)) := by
  funext i
  ext j k
  exact pauliExpr_eval v x i.1 i.2 _ _

@[simp] theorem compute_C (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (ζ : ℝ) :
    (compute v x ζ).value.C=KSSpinSource.coefficientCovariance
      (SourceTransport.smoothWeights ζ x) := by
  ext i j
  exact covarianceExpr_eval x ζ i j

/-- Every real and imaginary center entry has an actual primitive execution. -/
theorem compute_H_execution (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (ζ : ℝ)
    (j k : Fin (dimension d)) :
    Expr.Executes (input v x) (blockCenterExpr (blockIndex d j) (blockIndex d k)).re
      ((compute v x ζ).value.H j k).re
      (blockCenterExpr (N:=N) (blockIndex d j) (blockIndex d k)).re.cost ∧
    Expr.Executes (input v x) (blockCenterExpr (blockIndex d j) (blockIndex d k)).im
      ((compute v x ζ).value.H j k).im
      (blockCenterExpr (N:=N) (blockIndex d j) (blockIndex d k)).im.cost :=
  ComplexExpr.executes _ _ (blockCenterExpr_valid _ _ _)

theorem compute_A_execution (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (ζ : ℝ)
    (i : Fin N×Fin 4) (j k : Fin (dimension d)) :
    Expr.Executes (input v x) (pauliExpr i.1 i.2 (blockIndex d j) (blockIndex d k)).re
      ((compute v x ζ).value.A i j k).re
      (pauliExpr i.1 i.2 (blockIndex d j) (blockIndex d k)).re.cost ∧
    Expr.Executes (input v x) (pauliExpr i.1 i.2 (blockIndex d j) (blockIndex d k)).im
      ((compute v x ζ).value.A i j k).im
      (pauliExpr i.1 i.2 (blockIndex d j) (blockIndex d k)).im.cost :=
  ComplexExpr.executes _ _ (pauliExpr_valid _ _ _ _ _)

theorem compute_C_execution (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (ζ : ℝ)
    (i j : Fin N×Fin 4) :
    Expr.Executes (SourceEvaluation.registers (x i.1) ζ) (covarianceExpr i j)
      ((compute v x ζ).value.C i j) (covarianceExpr i j).cost :=
  Expr.executes_of_valid _ _ (covarianceExpr_valid x ζ i j)

def costBound (N d : ℕ) := 10000*(N+1)^2*(d+1)^2

theorem compute_cost (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (ζ : ℝ) :
    (compute v x ζ).cost≤costBound N d := by
  let e := blockIndex d
  have hh := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin (dimension d)))) =>
    Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => Nat.add_le_add_right (blockCenterExpr_cost (N:=N) (e j) (e k)) 22))
  have ha := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin N × Fin 4))) =>
    Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin (dimension d)))) =>
      Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => Nat.add_le_add_right (pauliExpr_cost i.1 i.2 (e j) (e k)) 22)))
  have hc := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin N × Fin 4))) =>
    Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => Nat.add_le_add_right (covarianceExpr_cost i j) 2))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Fintype.card_prod,smul_eq_mul] at hh ha hc
  dsimp only [e] at hh ha
  dsimp only [compute]
  calc
    _ ≤ (dimension d)*((dimension d)*(100*(N+1)+22))+
      (N*4)*((dimension d)*((dimension d)*(46+22)))+(N*4)*((N*4)*(30+2))+
      10*(N+d+1)^2 := by omega
    _ ≤ _ := by simp only [dimension_eq,costBound];ring_nf;omega

end SeamlessKS.RuntimeStateData
