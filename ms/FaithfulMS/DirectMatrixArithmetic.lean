import MatrixSpencer.RealRAMOwnerSDPBlocks
import FaithfulMS.SpectralArithmetic
import MatrixSpencer.CovarianceGram

/-! Scalar circuits for the direct-density report. Each complex operation is
expanded into real arithmetic. The source and Gram computations are explicit
finite sums, with polynomial counts including output stores.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.DirectMatrixArithmetic
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {d r : ℕ}
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev Registers (r d : ℕ) := Fin r × Fin d × Fin d × Bool

def input (A : Fin r → Mat d) : Registers r d → ℝ
  | (a,i,j,b) => if b then (A a i j).im else (A a i j).re

def read (a : Fin r) (i j : Fin d) : ComplexExpr (Registers r d) :=
  ⟨.input (a,i,j,false), .input (a,i,j,true)⟩

@[simp] theorem read_eval (A : Fin r → Mat d) (a : Fin r) (i j : Fin d) :
    (read a i j).eval (input A) = A a i j := by apply Complex.ext <;> rfl

theorem read_valid (a : Fin r) (v : Registers r d → ℝ) (i j : Fin d) :
    (read a i j).Valid v := ⟨trivial,trivial⟩

theorem productExpr_cost {ρ : Type*} (A B : Fin d → Fin d → ComplexExpr ρ)
    (a b : ℕ) (ha : ∀ i j, (A i j).cost ≤ a) (hb : ∀ i j, (B i j).cost ≤ b)
    (i j : Fin d) : (ComplexExpr.matrixMul A B i j).cost ≤ OwnerSDPBlocks.productBound d a b := by
  simpa only [OwnerSDPBlocks.productBound,Fintype.card_fin] using
    ComplexExpr.matrixMul_cost A B a b ha hb i j

def materialize {ρ : Type*} (v : ρ → ℝ) (E : Fin d → Fin d → ComplexExpr ρ) :
    Counted (Mat d) :=
  ⟨fun i j => (E i j).eval v, ∑ i, ∑ j, ((E i j).cost + 2)⟩

theorem materialize_cost {ρ : Type*} (v : ρ → ℝ)
    (E : Fin d → Fin d → ComplexExpr ρ) (b : ℕ)
    (h : ∀ i j, (E i j).cost ≤ b) :
    (materialize v E).cost ≤ d*d*(b+2) := by
  dsimp only [materialize]
  calc
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, (b+2) := by
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => Nat.add_le_add_right (h i j) 2))
    _ = _ := by simp; ring

theorem materialize_execution {ρ : Type*} (v : ρ → ℝ)
    (E : Fin d → Fin d → ComplexExpr ρ)
    (h : ∀ i j, (E i j).Valid v) (i j : Fin d) :
    Expr.Executes v (E i j).re ((materialize v E).value i j).re (E i j).re.cost ∧
    Expr.Executes v (E i j).im ((materialize v E).value i j).im (E i j).im.cost :=
  ComplexExpr.executes (E i j) v (h i j)

def product (A B : Mat d) : Counted (Mat d) :=
  materialize (input ![A,B]) (ComplexExpr.matrixMul (read 0) (read 1))

theorem product_value (A B : Mat d) : (product A B).value = A*B := by
  ext i j
  simp [product, materialize, ComplexExpr.matrixMul, Matrix.mul_apply]

theorem product_cost (A B : Mat d) : (product A B).cost ≤ d*d*(16*d+4) := by
  apply materialize_cost _ _ (16*d+2)
  intro i j
  simpa [Fintype.card_fin,mul_comm] using ComplexExpr.matrixMul_cost (read (0 : Fin 2)) (read 1)
    2 2 (fun _ _ => le_rfl) (fun _ _ => le_rfl) i j

theorem product_valid (A B : Mat d) (i j : Fin d) :
    (ComplexExpr.matrixMul (read (0 : Fin 2)) (read 1) i j).Valid (input ![A,B]) :=
  ComplexExpr.matrixMul_valid (read 0) (read 1) (input ![A,B])
    (read_valid 0 _) (read_valid 1 _) i j

def source {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Mat d) (C : Matrix ι ι ℝ) (S : Mat d) : Counted (Mat d) :=
  materialize (OwnerSDPBlocks.input S A C 0) (OwnerSDPBlocks.source OwnerSDPBlocks.center)

theorem source_value {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Mat d) (C : Matrix ι ι ℝ) (S : Mat d) :
    (source A C S).value = covarianceSource A C S := by
  ext i j
  simp only [source,materialize,OwnerSDPBlocks.source_eval,OwnerSDPBlocks.center_eval,Matrix.of_apply]
  rfl

theorem source_cost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Mat d) (C : Matrix ι ι ℝ) (S : Mat d) :
    (source A C S).cost ≤ d*d*(OwnerSDPBlocks.sourceBound (Fintype.card ι) d 2+2) :=
  materialize_cost _ _ _ (OwnerSDPBlocks.source_cost _ 2 (fun _ _ => le_rfl))

theorem source_valid {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Mat d) (C : Matrix ι ι ℝ) (S : Mat d) (i j : Fin d) :
    (OwnerSDPBlocks.source OwnerSDPBlocks.center i j).Valid
      (OwnerSDPBlocks.input S A C 0) :=
  OwnerSDPBlocks.source_valid OwnerSDPBlocks.center (OwnerSDPBlocks.input S A C 0)
    (fun _ _ => ⟨trivial,trivial⟩) i j

def traceExpr {ρ : Type*} (E : Fin d → Fin d → ComplexExpr ρ) : Expr ρ :=
  finiteSumExpr (fun i => (E i i).re)

theorem traceExpr_eval {ρ : Type*} (v : ρ → ℝ)
    (E : Fin d → Fin d → ComplexExpr ρ) :
    (traceExpr E).eval v = realTrace (fun i j => (E i j).eval v) := by
  simp [traceExpr, finiteSumExpr_eval, realTrace, Matrix.trace, ComplexExpr.eval]

theorem traceExpr_cost {ρ : Type*} (E : Fin d → Fin d → ComplexExpr ρ)
    (b : ℕ) (h : ∀ i j, (E i j).cost ≤ b) : (traceExpr E).cost ≤ d*(b+1)+1 := by
  have hh := finiteSumExpr_cost_le (fun i : Fin d => (E i i).re) b (by
    intro i
    have hi := h i i
    dsimp only [ComplexExpr.cost] at hi
    change (E i i).re.cost ≤ b
    omega)
  simpa only [traceExpr,Fintype.card_fin] using hh

def gramExpr : Expr (Registers 4 d) := traceExpr
  (ComplexExpr.matrixMul (ComplexExpr.matrixMul
    (ComplexExpr.matrixMul (read 0) (read 1)) (read 2)) (read 3))

theorem gramExpr_eval (S A Z B : Mat d) :
    gramExpr.eval (input ![S,A,Z,B]) = realTrace (S*A*Z*B) := by
  rw [gramExpr,traceExpr_eval]
  congr 1
  ext i j
  simp only [ComplexExpr.matrixMul_eval,read_eval,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons]
  rfl

def gramEntryBound (d : ℕ) : ℕ :=
  d*(OwnerSDPBlocks.productBound d
    (OwnerSDPBlocks.productBound d (OwnerSDPBlocks.productBound d 2 2) 2) 2+1)+1

theorem gramExpr_cost : (gramExpr (d:=d)).cost ≤ gramEntryBound d := by
  apply traceExpr_cost
  intro i j
  apply productExpr_cost _ _ _ 2
  · intro i j
    apply productExpr_cost _ _ _ 2
    · intro i j
      exact productExpr_cost (read (0 : Fin 4)) (read 1) 2 2
        (fun _ _ => le_rfl) (fun _ _ => le_rfl) i j
    · intro _ _; exact le_rfl
  · intro _ _; exact le_rfl

theorem gramExpr_valid (S A Z B : Mat d) :
    gramExpr.Valid (input ![S,A,Z,B]) := by
  unfold gramExpr traceExpr
  apply finiteSumExpr_valid
  intro i
  exact (ComplexExpr.matrixMul_valid _ _ _
    (ComplexExpr.matrixMul_valid _ _ _
      (ComplexExpr.matrixMul_valid _ _ _ (read_valid 0 _) (read_valid 1 _))
      (read_valid 2 _)) (read_valid 3 _) i i).1

def gram {ι : Type*} [Fintype ι] (A : ι → Mat d) (S Z : Mat d) :
    Counted (Matrix ι ι ℝ) :=
  ⟨fun i j => gramExpr.eval (input ![S,A i,Z,A j]),
    Fintype.card ι * Fintype.card ι * ((gramExpr (d:=d)).cost+1)⟩

theorem gram_value {ι : Type*} [Fintype ι] (A : ι → Mat d) (S Z : Mat d) :
    (gram A S Z).value = covarianceGram A S Z := by
  ext i j
  exact gramExpr_eval _ _ _ _

theorem gram_cost {ι : Type*} [Fintype ι] (A : ι → Mat d) (S Z : Mat d) :
    (gram A S Z).cost ≤ Fintype.card ι * Fintype.card ι * (gramEntryBound d+1) :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_right gramExpr_cost 1)

theorem gram_execution {ι : Type*} [Fintype ι]
    (A : ι → Mat d) (S Z : Mat d) (i j : ι) :
    Expr.Executes (input ![S,A i,Z,A j]) gramExpr
      ((gram A S Z).value i j) (gramExpr (d:=d)).cost :=
  Expr.executes_of_valid _ _ (gramExpr_valid _ _ _ _)

end FaithfulMS.DirectMatrixArithmetic
