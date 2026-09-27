import MatrixSpencer.KSEighthConvexValue
import MatrixSpencer.RealRAMOwnerSDPBlocks
import MatrixSpencer.RealRAMKSCappedSimplex

/-! Materialize the eighth direct-owner SDP inputs from the original vectors,
current coefficients and retained-owner mask. Complex entries are compiled to
real/imaginary scalar arithmetic; the only square root used for clamping is the
already verified scalar absolute-value program. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthOwnerInputSetup
open RealRAM RealRAM.JacobiIteration
variable {N d : ℕ}
abbrev Reg (N d : ℕ) := (Fin N × Fin d × Bool) ⊕ Fin N

def input (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) : Reg N d → ℝ
  | .inl (i,j,b) => if b then (v i j).im else (v i j).re
  | .inr i => x i
def vector (i : Fin N) (j : Fin d) : ComplexExpr (Reg N d) :=
  ⟨.input (.inl (i,j,false)),.input (.inl (i,j,true))⟩
def atom (i : Fin N) (j k : Fin d) := ComplexExpr.mul (vector i j) (ComplexExpr.conj (vector i k))
def center (j k : Fin d) : ComplexExpr (Reg N d) :=
  .sum (fun i : Fin N => .smul (.input (.inr i)) (atom i j k))
def lifted : Fin d ⊕ Fin d → Fin d ⊕ Fin d → ComplexExpr (Reg N d)
  | .inl j,.inl k => center j k
  | .inr j,.inr k => .smul (.constant (-1)) (center j k)
  | _,_ => .zero
def family (a : Fin N × Bool) : Fin d ⊕ Fin d → Fin d ⊕ Fin d → ComplexExpr (Reg N d)
  | .inl j,.inl k => if a.2 then atom a.1 j k else .zero
  | .inr j,.inr k => if a.2 then .zero else atom a.1 j k
  | _,_ => .zero

@[simp] theorem vector_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (i : Fin N) (j : Fin d) :
    (vector i j).eval (input v x)=v i j := by apply Complex.ext <;> rfl
@[simp] theorem atom_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (i : Fin N) (j k : Fin d) :
    (atom i j k).eval (input v x)=KSRankOne.atom (v i) j k := by
  simp [atom,KSRankOne.atom,Matrix.vecMulVec]
@[simp] theorem center_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (j k : Fin d) :
    (center j k).eval (input v x)=KSPotentialModels.center (fun i=>KSRankOne.atom (v i)) x j k := by
  simp [center,Expr.eval,input,KSPotentialModels.center,Matrix.sum_apply,Matrix.smul_apply]
theorem lifted_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (j k : Fin d ⊕ Fin d) :
    (lifted j k).eval (input v x)=
      signedLift (KSPotentialModels.center (fun i=>KSRankOne.atom (v i)) x) j k := by
  cases j <;> cases k <;> simp [lifted,signedLift,Expr.eval]
theorem family_eval (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (a : Fin N × Bool) (j k : Fin d ⊕ Fin d) :
    (family a j k).eval (input v x)=KSIndependentSource.family (fun i=>KSRankOne.atom (v i)) a j k := by
  rcases a with ⟨a,b⟩
  cases j <;> cases k <;> cases b <;>
    simp [family,KSIndependentSource.family,leftDensity,rightDensity]

theorem atom_valid (w : Reg N d → ℝ) (i : Fin N) (j k : Fin d) : (atom i j k).Valid w :=
  ComplexExpr.valid_mul ⟨trivial,trivial⟩ (ComplexExpr.valid_conj ⟨trivial,trivial⟩)
theorem center_valid (w : Reg N d → ℝ) (j k : Fin d) : (center j k).Valid w :=
  ComplexExpr.valid_sum _ _ (fun i=>ComplexExpr.valid_smul trivial (atom_valid w i j k))
theorem lifted_valid (w : Reg N d → ℝ) (j k : Fin d ⊕ Fin d) : (lifted j k).Valid w := by
  cases j <;> cases k
  · exact center_valid w _ _
  · exact ComplexExpr.valid_zero w
  · exact ComplexExpr.valid_zero w
  · exact ComplexExpr.valid_smul trivial (center_valid w _ _)
theorem family_valid (w : Reg N d → ℝ) (a : Fin N × Bool) (j k : Fin d ⊕ Fin d) :
    (family a j k).Valid w := by
  rcases a with ⟨a,b⟩
  cases j <;> cases k <;> cases b <;>
    first | exact atom_valid w _ _ _ | exact ComplexExpr.valid_zero w

theorem atom_cost (i : Fin N) (j k : Fin d) : (atom i j k).cost=18 := by
  rw [atom,ComplexExpr.cost_mul,ComplexExpr.cost_conj]
  norm_num [vector,ComplexExpr.cost,Expr.cost]
theorem center_cost (j k : Fin d) : (center (N:=N) j k).cost≤24*N+2 := by
  have h := ComplexExpr.cost_sum_le (fun i : Fin N=>ComplexExpr.smul (.input (.inr i)) (atom i j k)) 22
    (fun i=>by simp [ComplexExpr.cost_smul,atom_cost,Expr.cost])
  simpa only [Fintype.card_fin,Nat.mul_comm] using h
theorem lifted_cost (j k : Fin d ⊕ Fin d) : (lifted (N:=N) j k).cost≤24*N+6 := by
  cases j <;> cases k
  · exact (center_cost _ _).trans (by omega)
  · simp [lifted,ComplexExpr.cost_zero]
  · simp [lifted,ComplexExpr.cost_zero]
  · rename_i j k
    have h := center_cost (N:=N) j k
    simp only [lifted,ComplexExpr.cost_smul,Expr.cost]
    omega
theorem family_cost (a : Fin N × Bool) (j k : Fin d ⊕ Fin d) : (family a j k).cost≤18 := by
  rcases a with ⟨a,b⟩
  cases j <;> cases k <;> cases b <;> simp [family,atom_cost,ComplexExpr.cost_zero]

def H (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) : Counted (Matrix (Fin (d+d)) (Fin (d+d)) ℂ) :=
  let e := KSEighthNumericalValue.blockIndex d
  ⟨fun j k=>(lifted (e j) (e k)).eval (input v x),
    (∑j : Fin (d+d),∑k : Fin (d+d),((lifted (N:=N) (e j) (e k)).cost+2))+20*(N+d+1)^2⟩
def A (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) :
    Counted ((Fin N × Bool) → Matrix (Fin (d+d)) (Fin (d+d)) ℂ) :=
  let e := KSEighthNumericalValue.blockIndex d
  ⟨fun a j k=>(family a (e j) (e k)).eval (input v x),
    (∑a : Fin N × Bool,∑j : Fin (d+d),∑k : Fin (d+d),((family a (e j) (e k)).cost+2))+20*(N+d+1)^2⟩

theorem H_value (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) :
    (H v x).value=(signedLift (KSPotentialModels.center (fun i=>KSRankOne.atom (v i)) x)).submatrix
      (KSEighthNumericalValue.blockIndex d) (KSEighthNumericalValue.blockIndex d) := by
  ext j k
  exact lifted_eval v x _ _
theorem A_value (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) :
    (A v x).value=(fun a=>(KSIndependentSource.family (fun i=>KSRankOne.atom (v i)) a).submatrix
      (KSEighthNumericalValue.blockIndex d) (KSEighthNumericalValue.blockIndex d)) := by
  funext a j k
  exact family_eval v x a _ _
theorem A_isHermitian (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (a : Fin N × Bool) :
    ((A v x).value a).IsHermitian := by
  rw [A_value]
  exact (KSIndependentSource.family_isHermitian _ (fun i=>KSRankOne.atom_isHermitian (v i)) a).submatrix _

theorem H_cost (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) :
    (H v x).cost≤(d+d)^2*(24*N+8)+20*(N+d+1)^2 := by
  dsimp only [H]
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑_j : Fin (d+d),∑_k : Fin (d+d),(24*N+8) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      have h := lifted_cost (N:=N) (KSEighthNumericalValue.blockIndex d j) (KSEighthNumericalValue.blockIndex d k)
      omega
    _ = _ := by simp;ring
theorem A_cost (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) :
    (A v x).cost≤(2*N)*(d+d)^2*20+20*(N+d+1)^2 := by
  dsimp only [A]
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑_a : Fin N × Bool,∑_j : Fin (d+d),∑_k : Fin (d+d),20 := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      have h := family_cost a (KSEighthNumericalValue.blockIndex d j) (KSEighthNumericalValue.blockIndex d k)
      omega
    _ = _ := by simp;ring

def clamp (c : Fin N → ℝ) : Counted (Fin N → ℝ) :=
  ⟨fun i=>(c i+(KSCappedSimplex.absolute (c i)).value)/2,
    (∑i,((KSCappedSimplex.absolute (c i)).cost+10))+1⟩
theorem clamp_value (c : Fin N → ℝ) : (clamp c).value=KSEighthConvexValue.nonnegativeOwners c := by
  funext i
  simp only [clamp,KSCappedSimplex.absolute_value,KSEighthConvexValue.nonnegativeOwners]
  by_cases h : 0≤c i
  · rw [abs_of_nonneg h,max_eq_right h];ring
  · rw [abs_of_neg (lt_of_not_ge h),max_eq_left (le_of_lt (lt_of_not_ge h))];ring
theorem clamp_cost (c : Fin N → ℝ) : (clamp c).cost≤24*N+1 := by
  dsimp only [clamp]
  have hs : (∑i,((KSCappedSimplex.absolute (c i)).cost+10))≤24*N := by
    calc _ ≤ ∑_i : Fin N,24 := by
            apply Finset.sum_le_sum
            intro i _
            have h := KSCappedSimplex.absolute_cost (c i)
            omega
         _ = _ := by simp;omega
  omega
def C (c : Fin N → ℝ) : Counted (Matrix (Fin N × Bool) (Fin N × Bool) ℝ) :=
  let w := clamp c
  ⟨KSIndependentSource.coefficientCovariance w.value,w.cost+20*N^2+1⟩
theorem C_value (c : Fin N → ℝ) :
    (C c).value=KSIndependentSource.coefficientCovariance (KSEighthConvexValue.nonnegativeOwners c) := by
  simp only [C,clamp_value]
theorem C_posSemidef (c : Fin N → ℝ) : (C c).value.PosSemidef := by
  rw [C_value]
  exact KSIndependentSource.coefficientCovariance_posSemidef (fun i=>le_max_left _ _)
theorem C_cost (c : Fin N → ℝ) : (C c).cost≤20*N^2+24*N+2 := by
  have h := clamp_cost c
  dsimp only [C]
  omega

def costBudget (N d : ℕ) : ℕ :=
  (d+d)^2*(24*N+8)+(2*N)*(d+d)^2*20+40*(N+d+1)^2+20*N^2+24*N+2

end MatrixSpencer.KSEighthOwnerInputSetup
