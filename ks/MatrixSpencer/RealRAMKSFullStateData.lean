import MatrixSpencer.RealRAMComplexArithmetic
import MatrixSpencer.RealRAMJacobiIteration
import MatrixSpencer.KSFullConvexOracleValue

/-! Primitive construction of the full-cube value query's matrix center,
Pauli family, and real coefficient covariance, from the original vectors and
current state. Complex arithmetic is executed as pairs of real expressions.
The frozen mask and nonnegative owner clamp are finite comparison operations.
No spectral operation occurs in this data construction. -/
open Matrix Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.KSFullStateData
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open JacobiIteration (Counted)
attribute [local instance] Classical.propDecidable
variable {N d : ℕ}

abbrev Registers (N d : ℕ) := ((Fin N × Fin d) × Bool) ⊕ (Fin N ⊕ Fin 2)

def input (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ) : Registers N d → ℝ :=
  Sum.elim (fun p => if p.2 then (v p.1.1 p.1.2).im else (v p.1.1 p.1.2).re)
    (Sum.elim x (fun j => if j=0 then δ else η))

def vectorExpr (i : Fin N) (j : Fin d) : ComplexExpr (Registers N d) :=
  ⟨.input (.inl ((i,j),false)),.input (.inl ((i,j),true))⟩

theorem vectorExpr_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ)
    (i : Fin N) (j : Fin d) : (vectorExpr i j).eval (input v x δ η)=v i j := by
  apply Complex.ext <;> rfl

def atomExpr (i : Fin N) (j k : Fin d) : ComplexExpr (Registers N d) :=
  .mul (vectorExpr i j) (.conj (vectorExpr i k))

theorem atomExpr_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ)
    (i : Fin N) (j k : Fin d) : (atomExpr i j k).eval (input v x δ η)=KSRankOne.atom (v i) j k := by
  simp [atomExpr,vectorExpr_eval,KSRankOne.atom_apply]

theorem atomExpr_cost (i : Fin N) (j k : Fin d) : (atomExpr i j k).cost=18 := rfl

theorem atomExpr_valid (u : Registers N d → ℝ) (i : Fin N) (j k : Fin d) :
    (atomExpr i j k).Valid u := by
  apply ComplexExpr.valid_mul
  · exact ⟨trivial,trivial⟩
  · exact ComplexExpr.valid_conj ⟨trivial,trivial⟩

def frozenMask (x : Fin N → ℝ) : Counted (Fin N → Bool) :=
  ⟨fun i => decide (x i=1 ∨ x i= -1),12*N+1⟩

theorem frozenMask_value (x : Fin N → ℝ) (i : Fin N) :
    (frozenMask x).value i=decide (i∈ksFrozen 1 x) := by
  simp [frozenMask,ksFrozen,abs_eq (by norm_num : (0:ℝ)≤1),or_comm]

def countExpr (b : Fin N → Bool) : Expr (Registers N d) :=
  finiteSumExpr (fun i => .constant (if b i then 1 else 0))

theorem countExpr_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ) :
    (countExpr (frozenMask x).value).eval (input v x δ η)=(ksFrozen 1 x).card := by
  simp [countExpr,finiteSumExpr_eval,frozenMask_value,Expr.eval,apply_ite]

def centerExpr (j k : Fin d) : ComplexExpr (Registers N d) :=
  .sum (fun i => .smul (.input (.inr (.inl i))) (atomExpr i j k))

theorem centerExpr_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ)
    (j k : Fin d) : (centerExpr j k).eval (input v x δ η)=
      KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x j k := by
  rw [centerExpr,ComplexExpr.eval_sum]
  simp only [ComplexExpr.eval_smul,atomExpr_eval]
  simp [Expr.eval,input,KSPotentialModels.center,Matrix.sum_apply,Matrix.smul_apply]

def debitExpr (b : Fin N → Bool) (j k : Fin d) : ComplexExpr (Registers N d) :=
  .add (.smul (.input (.inr (.inr 0)))
    (.sum (fun i => if b i then atomExpr i j k else .zero)))
    (.smul (.mul (.input (.inr (.inr 1))) (countExpr b))
      (.real (.constant (if j=k then 1 else 0))))

theorem debitExpr_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ)
    (j k : Fin d) : (debitExpr (frozenMask x).value j k).eval (input v x δ η)=
      KSDebitBudget.debit (fun i => KSRankOne.atom (v i)) δ η x j k := by
  rw [debitExpr,ComplexExpr.eval_add,ComplexExpr.eval_smul,ComplexExpr.eval_smul,
    ComplexExpr.eval_sum,ComplexExpr.eval_real]
  have hf (i : Fin N) :
      (if (frozenMask x).value i then atomExpr i j k else ComplexExpr.zero).eval (input v x δ η)=
      if i∈ksFrozen 1 x then KSRankOne.atom (v i) j k else 0 := by
    rw [frozenMask_value]
    by_cases hi : i∈ksFrozen 1 x <;> simp [hi,atomExpr_eval]
  simp only [hf,Expr.eval, countExpr_eval]
  simp only [input,Sum.elim_inr,Sum.elim_inl,Fin.zero_eta,Fin.isValue,
    ite_true,ite_false,Rat.cast_one,Rat.cast_zero]
  norm_num only
  simp only [KSDebitBudget.debit,Matrix.add_apply,Matrix.smul_apply,Matrix.sum_apply,
    Finset.sum_filter,Matrix.one_apply]
  by_cases he : j=k <;> simp [he,smul_eq_mul] <;> ring

def blockCenterExpr (b : Fin N → Bool) : (Fin d ⊕ Fin d) → (Fin d ⊕ Fin d) → ComplexExpr (Registers N d)
  | .inl j,.inl k => .add (centerExpr j k) (.smul (.constant (-1)) (debitExpr b j k))
  | .inr j,.inr k => .add (.smul (.constant (-1)) (centerExpr j k)) (.smul (.constant (-1)) (debitExpr b j k))
  | _,_ => .zero

theorem blockCenterExpr_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ)
    (j k : Fin d ⊕ Fin d) : (blockCenterExpr (frozenMask x).value j k).eval (input v x δ η)=
      KSDebitCenter.center (KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x)
        (KSDebitBudget.debit (fun i => KSRankOne.atom (v i)) δ η x) j k := by
  rw [KSDebitCenter.center_eq_blocks]
  cases j <;> cases k <;>
    simp [blockCenterExpr,centerExpr_eval,debitExpr_eval,Expr.eval,
      Matrix.fromBlocks,Matrix.sub_apply,Matrix.neg_apply,sub_eq_add_neg]

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

theorem pauliExpr_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ)
    (i : Fin N) (a : Fin 4) (j k : Fin d ⊕ Fin d) :
    (pauliExpr i a j k).eval (input v x δ η)=KSSpinSource.family (fun i => KSRankOne.atom (v i)) (i,a) j k := by
  fin_cases a <;> cases j <;> cases k <;>
    simp [pauliExpr,KSSpinSource.family,KSSpinSource.pauli,KSSpinSource.doubled,
      signedLift,Matrix.fromBlocks,Matrix.smul_apply,atomExpr_eval,Expr.eval] <;>
    norm_num [ComplexExpr.eval,Expr.eval,Complex.ext_iff]

def ownerExpr (i : Fin N) : Expr (Registers N d) :=
  .mul (.constant 64) (.sub (.constant 1)
    (.mul (.input (.inr (.inl i))) (.input (.inr (.inl i)))))

def owners (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ) : Counted (Fin N → ℝ) :=
  ⟨fun i => let y := (ownerExpr i).eval (input v x δ η); if 0≤y then y else 0,15*N+1⟩

theorem owners_value (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ) (i : Fin N) :
    (owners v x δ η).value i=max 0 (KSPotentialModels.naturalOwners 64 x i) := by
  simp only [owners,ownerExpr,Expr.eval,input,Sum.elim_inr,Sum.elim_inl,Rat.cast_ofNat,Rat.cast_one]
  change (if 0≤64*(1-x i*x i) then _ else _)=_
  rw [max_def]
  simp [KSPotentialModels.naturalOwners,pow_two]

structure Data (N d : ℕ) where
  H : Matrix (Fin (d+d)) (Fin (d+d)) ℂ
  A : (Fin N × Fin 4) → Matrix (Fin (d+d)) (Fin (d+d)) ℂ
  C : Matrix (Fin N × Fin 4) (Fin N × Fin 4) ℝ

def compute (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ) : Counted (Data N d) :=
  let mask := frozenMask x
  let c := owners v x δ η
  let e := KSFullConvexOracleValue.blockIndex d
  let h : Matrix (Fin (d+d)) (Fin (d+d)) ℂ := fun j k =>
    (blockCenterExpr mask.value (e j) (e k)).eval (input v x δ η)
  let a : (Fin N × Fin 4) → Matrix (Fin (d+d)) (Fin (d+d)) ℂ := fun i j k =>
    (pauliExpr i.1 i.2 (e j) (e k)).eval (input v x δ η)
  let cov : Matrix (Fin N × Fin 4) (Fin N × Fin 4) ℝ := fun i j =>
    if i=j then (Expr.div (.input ()) (.constant 2)).eval (fun _ => c.value i.1) else 0
  ⟨⟨h,a,cov⟩,mask.cost+c.cost+
    (∑ j : Fin (d+d),∑ k : Fin (d+d),((blockCenterExpr mask.value (e j) (e k)).cost+12))+
    (∑ i : Fin N×Fin 4,∑ j : Fin (d+d),∑ k : Fin (d+d),((pauliExpr i.1 i.2 (e j) (e k)).cost+12))+
    10*(4*N)^2+10*N*d+10⟩

theorem compute_H (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ) :
    (compute v x δ η).value.H=(KSDebitCenter.center
      (KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x)
      (KSDebitBudget.debit (fun i => KSRankOne.atom (v i)) δ η x)).submatrix
        (KSFullConvexOracleValue.blockIndex d) (KSFullConvexOracleValue.blockIndex d) := by
  ext j k
  exact blockCenterExpr_eval v x δ η _ _

theorem compute_A (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ) :
    (compute v x δ η).value.A=(fun i =>
      (KSSpinSource.family (fun i => KSRankOne.atom (v i)) i).submatrix
        (KSFullConvexOracleValue.blockIndex d) (KSFullConvexOracleValue.blockIndex d)) := by
  funext i
  ext j k
  exact pauliExpr_eval v x δ η i.1 i.2 _ _

theorem compute_C (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ) :
    (compute v x δ η).value.C=KSSpinSource.coefficientCovariance
      (fun i => max 0 (KSPotentialModels.naturalOwners 64 x i)) := by
  ext i j
  simp [compute,owners_value,Expr.eval,KSSpinSource.coefficientCovariance,Matrix.diagonal_apply]


theorem centerExpr_cost (j k : Fin d) : (centerExpr (N := N) j k).cost=24*N+2 := by
  simp [centerExpr,ComplexExpr.cost_sum,ComplexExpr.cost_smul,atomExpr_cost,Expr.cost]
  omega

theorem centerExpr_valid (u : Registers N d → ℝ) (j k : Fin d) : (centerExpr j k).Valid u := by
  apply ComplexExpr.valid_sum
  intro i
  exact ComplexExpr.valid_smul trivial (atomExpr_valid u i j k)

theorem countExpr_cost (b : Fin N → Bool) : (countExpr (d := d) b).cost≤2*N+1 := by
  apply (finiteSumExpr_cost_le _ 1 (by intro i; split_ifs <;> rfl)).trans_eq
  simp; ring

theorem countExpr_valid (u : Registers N d → ℝ) (b : Fin N → Bool) : (countExpr b).Valid u := by
  apply finiteSumExpr_valid
  intro i
  exact trivial

theorem debitExpr_cost (b : Fin N → Bool) (j k : Fin d) :
    (debitExpr b j k).cost≤100*(N+1) := by
  have hs : (ComplexExpr.sum (fun i => if b i then atomExpr i j k else .zero)).cost≤20*N+2 := by
    apply (ComplexExpr.cost_sum_le _ 18 (by intro i; split_ifs <;> simp [atomExpr_cost,ComplexExpr.cost_zero])).trans_eq
    simp; ring
  have hc := countExpr_cost (d := d) b
  simp only [debitExpr,ComplexExpr.cost_add,ComplexExpr.cost_smul,ComplexExpr.cost_real,Expr.cost]
  omega

theorem debitExpr_valid (u : Registers N d → ℝ) (b : Fin N → Bool) (j k : Fin d) :
    (debitExpr b j k).Valid u := by
  unfold debitExpr
  apply ComplexExpr.valid_add
  · apply ComplexExpr.valid_smul (by trivial)
    apply ComplexExpr.valid_sum
    intro i
    split_ifs
    · exact atomExpr_valid u i j k
    · exact ComplexExpr.valid_zero u
  · exact ComplexExpr.valid_smul ⟨trivial,countExpr_valid u b⟩ ⟨trivial,trivial⟩

theorem blockCenterExpr_cost (b : Fin N → Bool) (j k : Fin d ⊕ Fin d) :
    (blockCenterExpr b j k).cost≤200*(N+1) := by
  cases j with
  | inl j =>
    cases k with
    | inl k =>
      have h := debitExpr_cost b j k
      simp only [blockCenterExpr,ComplexExpr.cost_add,ComplexExpr.cost_smul,Expr.cost,centerExpr_cost]
      omega
    | inr k => simp [blockCenterExpr,ComplexExpr.cost_zero]; omega
  | inr j =>
    cases k with
    | inl k => simp [blockCenterExpr,ComplexExpr.cost_zero]; omega
    | inr k =>
      have h := debitExpr_cost b j k
      simp only [blockCenterExpr,ComplexExpr.cost_add,ComplexExpr.cost_smul,Expr.cost,centerExpr_cost]
      omega

theorem blockCenterExpr_valid (u : Registers N d → ℝ) (b : Fin N → Bool)
    (j k : Fin d ⊕ Fin d) : (blockCenterExpr b j k).Valid u := by
  cases j <;> cases k
  · exact ComplexExpr.valid_add (centerExpr_valid u _ _)
      (ComplexExpr.valid_smul trivial (debitExpr_valid u b _ _))
  · exact ComplexExpr.valid_zero u
  · exact ComplexExpr.valid_zero u
  · exact ComplexExpr.valid_add (ComplexExpr.valid_smul trivial (centerExpr_valid u _ _))
      (ComplexExpr.valid_smul trivial (debitExpr_valid u b _ _))

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

theorem compute_cost (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ) :
    (compute v x δ η).cost≤10000*(N+1)^2*(d+1)^2 := by
  let b := (frozenMask x).value
  let e := KSFullConvexOracleValue.blockIndex d
  have hh := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin (d+d)))) =>
    Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => Nat.add_le_add_right (blockCenterExpr_cost b (e j) (e k)) 12))
  have ha := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin N × Fin 4))) =>
    Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin (d+d)))) =>
      Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => Nat.add_le_add_right (pauliExpr_cost i.1 i.2 (e j) (e k)) 12)))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Fintype.card_prod,smul_eq_mul] at hh ha
  dsimp only [compute]
  change (12*N+1)+(15*N+1)+
    (∑ j : Fin (d+d),∑ k : Fin (d+d),((blockCenterExpr b (e j) (e k)).cost+12))+
    (∑ i : Fin N×Fin 4,∑ j : Fin (d+d),∑ k : Fin (d+d),((pauliExpr i.1 i.2 (e j) (e k)).cost+12))+
    10*(4*N)^2+10*N*d+10≤_
  calc
    _ ≤ (12*N+1)+(15*N+1)+(d+d)*((d+d)*(200*(N+1)+12))+
        (N*4)*((d+d)*((d+d)*(46+12)))+10*(4*N)^2+10*N*d+10 := by omega
    _ ≤ _ := by ring_nf; omega

/-- Reused by the final numerical norm test. -/
def signedCenter (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) :
    Counted (Matrix (Fin d) (Fin d) ℂ) :=
  ⟨fun j k => (centerExpr j k).eval (input v x 0 0),
    (∑ j : Fin d,∑ k : Fin d,((centerExpr (N := N) j k).cost+8))+4*N*d+3*N+1⟩

theorem signedCenter_value (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) :
    (signedCenter v x).value=KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x := by
  ext j k
  exact centerExpr_eval v x 0 0 j k

theorem signedCenter_cost (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) :
    (signedCenter v x).cost≤100*(N+1)*(d+1)^2 := by
  simp only [signedCenter,centerExpr_cost,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring_nf
  omega

end MatrixSpencer.RealRAM.KSFullStateData
