import MatrixSpencer.RealRAMOwnerSDPSetup
import MatrixSpencer.MSConvexOwnerValue
import MatrixSpencer.EpochState
import MatrixSpencer.CovarianceFace

/-! Real arithmetic construction of an original square-MS center and its
stored-frame family, followed by the actual direct owner SDP compiler and
the permitted convex solver. No complex operation or spectral decomposition
is charged as a primitive. The valid-query bridge removes the proof-only
fallback branches in the total mathematical report definition. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.RealRAM.MSOwnerReport
open JacobiIteration (Counted)
variable {N k d : ℕ}
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

abbrev Registers (N k d : ℕ) :=
  ((Fin d × Fin d × Bool) ⊕ (Fin N × Fin d × Fin d × Bool)) ⊕ (Fin N ⊕ (Fin N × Fin k))

def input (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin N → ℝ) (U : Matrix (Fin N) (Fin k) ℝ) : Registers N k d → ℝ
  | .inl (.inl (i,j,b)) => if b then (H i j).im else (H i j).re
  | .inl (.inr (a,i,j,b)) => if b then (A a i j).im else (A a i j).re
  | .inr (.inl a) => x a
  | .inr (.inr (a,b)) => U a b

def offsetExpr (i j : Fin d) : ComplexExpr (Registers N k d) :=
  ⟨.input (.inl (.inl (i,j,false))),.input (.inl (.inl (i,j,true)))⟩
def atomExpr (a : Fin N) (i j : Fin d) : ComplexExpr (Registers N k d) :=
  ⟨.input (.inl (.inr (a,i,j,false))),.input (.inl (.inr (a,i,j,true)))⟩
def pointExpr (a : Fin N) : Expr (Registers N k d) := .input (.inr (.inl a))
def frameExpr (a : Fin N) (b : Fin k) : Expr (Registers N k d) := .input (.inr (.inr (a,b)))

@[simp] theorem offsetExpr_eval (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin N → ℝ) (U : Matrix (Fin N) (Fin k) ℝ) (i j : Fin d) :
    (offsetExpr i j).eval (input H A x U)=H i j := by apply Complex.ext <;> rfl
@[simp] theorem atomExpr_eval (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin N → ℝ) (U : Matrix (Fin N) (Fin k) ℝ) (a : Fin N) (i j : Fin d) :
    (atomExpr a i j).eval (input H A x U)=A a i j := by apply Complex.ext <;> rfl
@[simp] theorem pointExpr_eval (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin N → ℝ) (U : Matrix (Fin N) (Fin k) ℝ) (a : Fin N) :
    (pointExpr a).eval (input H A x U)=x a := rfl
@[simp] theorem frameExpr_eval (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin N → ℝ) (U : Matrix (Fin N) (Fin k) ℝ) (a : Fin N) (b : Fin k) :
    (frameExpr a b).eval (input H A x U)=U a b := rfl

def centerExpr (i j : Fin d) : ComplexExpr (Registers N k d) :=
  .add (offsetExpr i j) (.sum (fun a => .smul (pointExpr a) (atomExpr a i j)))

def familyExpr (b : Fin k) (i j : Fin d) : ComplexExpr (Registers N k d) :=
  .sum (fun a => .smul (frameExpr a b) (atomExpr a i j))

theorem centerExpr_eval (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin N → ℝ) (U : Matrix (Fin N) (Fin k) ℝ) (i j : Fin d) :
    (centerExpr i j).eval (input H A x U)=(H+∑a,x a • A a) i j := by
  simp [centerExpr,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply]

theorem familyExpr_eval (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin N → ℝ) (U : Matrix (Fin N) (Fin k) ℝ) (b : Fin k) (i j : Fin d) :
    (familyExpr b i j).eval (input H A x U)=mixFamily A U b i j := by
  simp [familyExpr,mixFamily,Matrix.sum_apply,Matrix.smul_apply]

theorem centerExpr_valid (u : Registers N k d → ℝ) (i j : Fin d) :
    (centerExpr i j).Valid u := by
  exact ComplexExpr.valid_add ⟨trivial,trivial⟩
    (ComplexExpr.valid_sum _ _ (fun _=>ComplexExpr.valid_smul trivial ⟨trivial,trivial⟩))

theorem familyExpr_valid (u : Registers N k d → ℝ) (b : Fin k) (i j : Fin d) :
    (familyExpr b i j).Valid u :=
  ComplexExpr.valid_sum _ _ (fun _=>ComplexExpr.valid_smul trivial ⟨trivial,trivial⟩)

theorem familyExpr_cost (b : Fin k) (i j : Fin d) : (familyExpr (N:=N) b i j).cost=8*N+2 := by
  unfold familyExpr
  rw [ComplexExpr.cost_sum]
  simp only [ComplexExpr.cost_smul,ComplexExpr.smul,frameExpr,atomExpr,ComplexExpr.cost,Expr.cost,
    Fintype.card_fin,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  omega

theorem centerExpr_cost (i j : Fin d) : (centerExpr (N:=N) (k:=k) i j).cost=8*N+6 := by
  unfold centerExpr
  rw [ComplexExpr.cost_add,ComplexExpr.cost_sum]
  simp only [ComplexExpr.cost_smul,ComplexExpr.smul,offsetExpr,pointExpr,atomExpr,ComplexExpr.cost,Expr.cost,
    Fintype.card_fin,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  omega

def center (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin N → ℝ) : Counted (Matrix (Fin d) (Fin d) ℂ) :=
  ⟨fun i j => (centerExpr (k:=0) i j).eval (input H A x 0),
    (∑i:Fin d,∑j:Fin d,((centerExpr (N:=N) (k:=0) i j).cost+2))+1⟩

def family (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (U : Matrix (Fin N) (Fin k) ℝ) :
    Counted (Fin k → Matrix (Fin d) (Fin d) ℂ) :=
  ⟨fun b i j => (familyExpr b i j).eval (input 0 A 0 U),
    (∑b:Fin k,∑i:Fin d,∑j:Fin d,((familyExpr (N:=N) b i j).cost+2))+1⟩

theorem center_value (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin N → ℝ) : (center H A x).value=H+∑a,x a • A a := by
  funext i j
  exact centerExpr_eval H A x 0 i j

theorem family_value (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (U : Matrix (Fin N) (Fin k) ℝ) :
    (family A U).value=mixFamily A U := by
  funext b i j
  exact familyExpr_eval 0 A 0 U b i j

theorem center_epoch [Nonempty (Fin d)] (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (x : EuclideanSpace ℝ (Fin N)) :
    (center H A (WithLp.ofLp x)).value=(epochCenter H A hA x : Matrix (Fin d) (Fin d) ℂ) := by
  rw [center_value,epochCenter_coe]
  rfl

theorem center_cost (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin N → ℝ) : (center H A x).cost=d*d*(8*N+8)+1 := by
  simp [center,centerExpr_cost,Nat.mul_assoc]

theorem family_cost (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (U : Matrix (Fin N) (Fin k) ℝ) :
    (family A U).cost=k*d*d*(8*N+4)+1 := by
  simp [family,familyExpr_cost,Nat.mul_assoc]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def report (P : KSPolynomialConvexSolver.PolynomialSolver)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (θ : ℝ) (hd : 0<d) (ν : ℝ) : Counted ℝ :=
  OwnerSDPSetup.ownerReport P ⟨0,hd⟩ H A hA C hC hd θ ν

theorem report_value (P : KSPolynomialConvexSolver.PolynomialSolver)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (θ : ℝ) (hd : 0<d) (ν : ℝ) :
    (report P H A hA C hC θ hd ν).value=
      @MSConvexOwnerValue.report ι _ _ d (MSConvexOwnerValue.Oracle.ofSolver P.solver) H A C θ hd ν := by
  exact (MSConvexOwnerValue.report_ofSolver P.solver H A hA C hC θ hd ν).symm

theorem report_cost (P : KSPolynomialConvexSolver.PolynomialSolver)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (θ : ℝ) (hd : 0<d) (ν : ℝ) (hν : 0<ν) {S V : ℕ}
    (hS : KSPolynomialConvexSolver.dataSize (KSFullManuscriptAffineData.dimension (⟨0,hd⟩:Fin d))
      (KSFullManuscriptAffineData.matrixSize (Fin d))≤S) (hV : ν⁻¹≤(V:ℝ)) :
    (report P H A hA C hC θ hd ν).cost≤
      OwnerSDPSetup.setupCost (Fintype.card ι) d+P.coefficient*(S+V+1)^P.degree :=
  OwnerSDPSetup.ownerReport_cost_le P ⟨0,hd⟩ H A hA C hC hd θ ν hν hS hV

end MatrixSpencer.RealRAM.MSOwnerReport
