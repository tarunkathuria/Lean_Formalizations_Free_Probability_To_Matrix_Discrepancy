import MatrixSpencer.RealRAMSDPChart
import MatrixSpencer.KSPolynomialConvexSolver

/-! The direct covariance pencil is compiled by real/imaginary arithmetic.
In particular its source is the literal double covariance sum, with no
spectral decomposition or covariance square root in this computation. -/
open scoped BigOperators Matrix
noncomputable section
namespace MatrixSpencer.RealRAM.OwnerSDPBlocks
open KSFullManuscriptSDPBlockPencil
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Registers (ι : Type*) (d : ℕ) :=
  ((ι×Fin d×Fin d×Bool) ⊕ (ι×ι)) ⊕ ((Fin d×Fin d×Bool) ⊕ Unit)

def input (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) : Registers ι d→ℝ
  | .inl (.inl (a,i,j,b)) => if b then (A a i j).im else (A a i j).re
  | .inl (.inr (i,j)) => C i j
  | .inr (.inl (i,j,b)) => if b then (H i j).im else (H i j).re
  | .inr (.inr _) => θ

def atom (a : ι) (i j : Fin d) : ComplexExpr (Registers ι d) :=
  ⟨.input (.inl (.inl (a,i,j,false))),.input (.inl (.inl (a,i,j,true)))⟩
def center (i j : Fin d) : ComplexExpr (Registers ι d) :=
  ⟨.input (.inr (.inl (i,j,false))),.input (.inr (.inl (i,j,true)))⟩
def covariance (a b : ι) : Expr (Registers ι d) := .input (.inl (.inr (a,b)))
def theta : Expr (Registers ι d) := .input (.inr (.inr ()))

@[simp] theorem atom_eval (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ) (a : ι) (i j : Fin d) :
    (atom a i j).eval (input H A C θ)=A a i j := by apply Complex.ext <;> rfl
@[simp] theorem center_eval (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ) (i j : Fin d) :
    (center i j).eval (input H A C θ)=H i j := by apply Complex.ext <;> rfl
@[simp] theorem covariance_eval (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ) (a b : ι) :
    (covariance a b).eval (input H A C θ)=C a b := rfl
@[simp] theorem theta_eval (H) (A : ι→Matrix (Fin d) (Fin d) ℂ) (C) (θ : ℝ) :
    theta.eval (input H A C θ)=θ := rfl

def source (S : Fin d→Fin d→ComplexExpr (Registers ι d)) (i j : Fin d) :=
  ComplexExpr.sum (fun a:ι=>ComplexExpr.sum (fun b:ι=>ComplexExpr.smul (covariance a b)
    (ComplexExpr.matrixMul (ComplexExpr.matrixMul (atom a) S) (atom b) i j)))

@[simp] theorem source_eval (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ)
    (S : Fin d→Fin d→ComplexExpr (Registers ι d)) (i j : Fin d) :
    (source S i j).eval (input H A C θ) = covarianceSource A C
      (Matrix.of (fun i j=>(S i j).eval (input H A C θ))) i j := by
  simp [source,ComplexExpr.matrixMul_eval,covarianceSource,Matrix.sum_apply,Matrix.mul_apply]

theorem source_valid (S : Fin d→Fin d→ComplexExpr (Registers ι d)) (v : Registers ι d→ℝ)
    (hS : ∀i j,(S i j).Valid v) (i j : Fin d) : (source S i j).Valid v := by
  apply ComplexExpr.valid_sum
  intro a
  apply ComplexExpr.valid_sum
  intro b
  apply ComplexExpr.valid_smul (by trivial)
  exact ComplexExpr.matrixMul_valid (ComplexExpr.matrixMul (atom a) S) (atom b) v
    (ComplexExpr.matrixMul_valid (atom a) S v (fun _ _=>⟨trivial,trivial⟩) hS) (fun _ _=>⟨trivial,trivial⟩) _ _

def productBound (d a b : ℕ) := d*(2*a+2*b+8)+2
def sourceBound (r d b : ℕ) := r*(r*(productBound d (productBound d 2 b) 2+6)+4)+2

theorem source_cost (S : Fin d→Fin d→ComplexExpr (Registers ι d)) (b : ℕ)
    (hS : ∀i j,(S i j).cost≤b) (i j : Fin d) :
    (source S i j).cost≤sourceBound (Fintype.card ι) d b := by
  unfold source sourceBound
  apply ComplexExpr.cost_sum_le _ (Fintype.card ι*(productBound d (productBound d 2 b) 2+6)+2)
  intro a
  apply ComplexExpr.cost_sum_le _ (productBound d (productBound d 2 b) 2+4)
  intro c
  rw [ComplexExpr.cost_smul]
  have hmul := ComplexExpr.matrixMul_cost (ComplexExpr.matrixMul (atom a) S) (atom c)
    (productBound d 2 b) 2 (fun i j=>by
      simpa [productBound] using ComplexExpr.matrixMul_cost (atom a) S 2 b (fun _ _=>le_rfl) hS i j)
    (fun _ _=>le_rfl) i j
  simp only [covariance,Expr.cost]
  simp only [Fintype.card_fin] at hmul
  dsimp [productBound] at *
  omega

section Generic
variable {ρ α β γ δ : Type*}

def blocks (A : α→β→ComplexExpr ρ) (B : α→δ→ComplexExpr ρ)
    (C : γ→β→ComplexExpr ρ) (D : γ→δ→ComplexExpr ρ) : α⊕γ→β⊕δ→ComplexExpr ρ
  | .inl i,.inl j=>A i j
  | .inl i,.inr j=>B i j
  | .inr i,.inl j=>C i j
  | .inr i,.inr j=>D i j

theorem blocks_eval (A : α→β→ComplexExpr ρ) (B : α→δ→ComplexExpr ρ)
    (C : γ→β→ComplexExpr ρ) (D : γ→δ→ComplexExpr ρ) (v : ρ→ℝ) (i j) :
    (blocks A B C D i j).eval v = Matrix.fromBlocks (Matrix.of (fun i j=>(A i j).eval v))
      (Matrix.of (fun i j=>(B i j).eval v)) (Matrix.of (fun i j=>(C i j).eval v))
      (Matrix.of (fun i j=>(D i j).eval v)) i j := by cases i <;> cases j <;> rfl

theorem blocks_valid (A : α→β→ComplexExpr ρ) (B : α→δ→ComplexExpr ρ)
    (C : γ→β→ComplexExpr ρ) (D : γ→δ→ComplexExpr ρ) (v : ρ→ℝ)
    (hA : ∀i j,(A i j).Valid v) (hB : ∀i j,(B i j).Valid v)
    (hC : ∀i j,(C i j).Valid v) (hD : ∀i j,(D i j).Valid v) (i j) :
    (blocks A B C D i j).Valid v := by
  cases i <;> cases j <;> first | exact hA _ _ | exact hB _ _ | exact hC _ _ | exact hD _ _

theorem blocks_cost (A : α→β→ComplexExpr ρ) (B : α→δ→ComplexExpr ρ)
    (C : γ→β→ComplexExpr ρ) (D : γ→δ→ComplexExpr ρ) (b : ℕ)
    (hA : ∀i j,(A i j).cost≤b) (hB : ∀i j,(B i j).cost≤b)
    (hC : ∀i j,(C i j).cost≤b) (hD : ∀i j,(D i j).cost≤b) (i j) :
    (blocks A B C D i j).cost≤b := by
  cases i <;> cases j <;> first | exact hA _ _ | exact hB _ _ | exact hC _ _ | exact hD _ _

def realify (M : α→β→ComplexExpr ρ) : α⊕α→β⊕β→Expr ρ
  | .inl i,.inl j=>(M i j).re
  | .inl i,.inr j=>.sub (.constant 0) (M i j).im
  | .inr i,.inl j=>(M i j).im
  | .inr i,.inr j=>(M i j).re

theorem realify_eval (M : α→α→ComplexExpr ρ) (v : ρ→ℝ) (i j) :
    (realify M i j).eval v = KSComplexTraceSqrt.realification (Matrix.of (fun i j=>(M i j).eval v)) i j := by
  cases i <;> cases j <;> simp [realify,KSComplexTraceSqrt.realification,ComplexExpr.eval,Expr.eval]

theorem realify_valid (M : α→β→ComplexExpr ρ) (v : ρ→ℝ) (hM : ∀i j,(M i j).Valid v) (i j) :
    (realify M i j).Valid v := by
  cases i with
  | inl i=>cases j with
    | inl j=>exact (hM i j).1
    | inr j=>exact ⟨trivial,(hM i j).2⟩
  | inr i=>cases j with
    | inl j=>exact (hM i j).2
    | inr j=>exact (hM i j).1

theorem realify_cost (M : α→β→ComplexExpr ρ) (b : ℕ) (hM : ∀i j,(M i j).cost≤b) (i j) :
    (realify M i j).cost≤b+2 := by
  cases i with
  | inl i=>cases j with
    | inl j=>have h:=hM i j;dsimp [realify,ComplexExpr.cost] at *;omega
    | inr j=>have h:=hM i j;dsimp [realify,ComplexExpr.cost,Expr.cost] at *;omega
  | inr i=>cases j with
    | inl j=>have h:=hM i j;dsimp [realify,ComplexExpr.cost] at *;omega
    | inr j=>have h:=hM i j;dsimp [realify,ComplexExpr.cost] at *;omega
end Generic

end MatrixSpencer.RealRAM.OwnerSDPBlocks
