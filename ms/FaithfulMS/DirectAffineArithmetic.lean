import FaithfulMS.DirectMatrixArithmetic

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.DirectMatrixArithmetic
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {d : ℕ}

def addition (A B : Mat d) : Counted (Mat d) :=
  materialize (input ![A,B]) (fun i j => ComplexExpr.add (read 0 i j) (read 1 i j))

theorem addition_value (A B : Mat d) : (addition A B).value = A+B := by
  ext i j
  simp [addition,materialize]

theorem addition_cost (A B : Mat d) : (addition A B).cost ≤ 8*d*d := by
  have h := materialize_cost (input ![A,B])
    (fun i j => ComplexExpr.add (read 0 i j) (read 1 i j)) 6 (by
      intro i j
      simp [read,ComplexExpr.add,ComplexExpr.cost,Expr.cost])
  simpa [addition,mul_assoc,mul_comm,mul_left_comm] using h

def complementExpr (i j : Fin d) : ComplexExpr (Registers 1 d) :=
  ⟨.sub (.constant (if i=j then 1 else 0)) (read 0 i j).re,
   .sub (.constant 0) (read 0 i j).im⟩

def complement (A : Mat d) : Counted (Mat d) :=
  let r := materialize (input ![A]) complementExpr
  ⟨r.value,r.cost+d*d⟩

theorem complement_value (A : Mat d) : (complement A).value = 1-A := by
  ext i j
  by_cases hij : i=j <;> apply Complex.ext <;>
    simp [complement,materialize,complementExpr,ComplexExpr.eval,Expr.eval,read,input,Matrix.one_apply,hij]

theorem complement_cost (A : Mat d) : (complement A).cost ≤ 9*d*d := by
  have h := materialize_cost (input ![A]) complementExpr 6 (by
    intro i j
    simp [complementExpr,ComplexExpr.cost,Expr.cost,read])
  dsimp only [complement]
  nlinarith

theorem addition_valid (A B : Mat d) (i j : Fin d) :
    (ComplexExpr.add (read 0 i j) (read 1 i j)).Valid (input ![A,B]) :=
  ComplexExpr.valid_add (read_valid 0 _ i j) (read_valid 1 _ i j)

theorem complement_valid (A : Mat d) (i j : Fin d) :
    (complementExpr i j).Valid (input ![A]) := ⟨⟨trivial,trivial⟩,⟨trivial,trivial⟩⟩

def tracePairExpr : Expr (Registers 2 d) :=
  traceExpr (ComplexExpr.matrixMul (read 0) (read 1))

def tracePair (A B : Mat d) : Counted ℝ :=
  ⟨tracePairExpr.eval (input ![A,B]),(tracePairExpr (d:=d)).cost+1⟩

theorem tracePair_value (A B : Mat d) : (tracePair A B).value = realTrace (A*B) := by
  change tracePairExpr.eval _ = _
  rw [tracePairExpr,traceExpr_eval]
  congr 1
  ext i j
  simp only [ComplexExpr.matrixMul_eval,read_eval,Matrix.cons_val_zero,Matrix.cons_val_one]
  rfl

theorem tracePair_cost (A B : Mat d) : (tracePair A B).cost ≤ d*(16*d+3)+2 := by
  have h := traceExpr_cost (ComplexExpr.matrixMul (read (0 : Fin 2)) (read 1))
    (16*d+2) (by
      intro i j
      simpa [OwnerSDPBlocks.productBound,mul_comm] using
        productExpr_cost (read (0 : Fin 2)) (read 1) 2 2
          (fun _ _ => le_rfl) (fun _ _ => le_rfl) i j)
  dsimp only [tracePair]
  change (tracePairExpr (d:=d)).cost ≤ _ at h
  nlinarith

theorem tracePair_execution (A B : Mat d) :
    Expr.Executes (input ![A,B]) tracePairExpr (tracePair A B).value
      (tracePairExpr (d:=d)).cost := by
  apply Expr.executes_of_valid
  unfold tracePairExpr traceExpr
  apply finiteSumExpr_valid
  intro i
  exact (ComplexExpr.matrixMul_valid _ _ _ (read_valid 0 _) (read_valid 1 _) i i).1

end FaithfulMS.DirectMatrixArithmetic
