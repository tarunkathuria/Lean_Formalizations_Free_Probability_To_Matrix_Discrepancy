import MatrixSpencer.RealRAMCircuit

/-!
# Executed scalar circuits for dot products and dense matrix multiplication

These operation counts apply to the specified primitive circuits, whose values
are proved equal to the mathematical linear-algebra operations. A matrix
multiplication is not treated as a unit-cost primitive.
-/

open scoped BigOperators
namespace MatrixSpencer.RealRAM

variable {ι : Type*}

def dotExpr (n : ℕ) (left right : Fin n → ι) : Expr ι :=
  Expr.sumList (List.ofFn (fun i => Expr.mul (.input (left i)) (.input (right i))))

theorem dotExpr_eval (n : ℕ) (left right : Fin n → ι) (v : ι → ℝ) :
    (dotExpr n left right).eval v = ∑ i, v (left i) * v (right i) := by
  simp [dotExpr, Expr.eval_sumList, List.map_ofFn, Expr.eval, List.sum_ofFn]

theorem dotExpr_valid (n : ℕ) (left right : Fin n → ι) (v : ι → ℝ) :
    (dotExpr n left right).Valid v := by
  apply Expr.valid_sumList
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact ⟨trivial, trivial⟩

theorem dotExpr_cost (n : ℕ) (left right : Fin n → ι) :
    (dotExpr n left right).cost = 4*n + 1 := by
  simp [dotExpr, Expr.cost_sumList, List.map_ofFn, Expr.cost, List.sum_ofFn]
  omega

theorem dotExpr_executes (n : ℕ) (left right : Fin n → ι) (v : ι → ℝ) :
    Expr.Executes v (dotExpr n left right) (∑ i, v (left i) * v (right i)) (4*n+1) := by
  simpa only [dotExpr_eval, dotExpr_cost] using
    Expr.executes_of_valid v (dotExpr n left right) (dotExpr_valid n left right v)

/-- Fixed addresses for the two input matrices; no data-dependent indexing. -/
abbrev MatrixInputs (m n p : ℕ) := (Fin m × Fin n) ⊕ (Fin n × Fin p)

def matrixInput {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) : MatrixInputs m n p → ℝ :=
  Sum.elim (fun ij => A ij.1 ij.2) (fun ij => B ij.1 ij.2)

def matrixMulCircuit (m n p : ℕ) : Circuit (MatrixInputs m n p) (Fin m × Fin p) where
  output ij := dotExpr n (fun k => Sum.inl (ij.1,k)) (fun k => Sum.inr (k,ij.2))

theorem matrixMulCircuit_eval {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) (i : Fin m) (j : Fin p) :
    (matrixMulCircuit m n p).eval (matrixInput A B) (i,j) = (A*B) i j := by
  simp [Circuit.eval, matrixMulCircuit, dotExpr_eval, matrixInput, Matrix.mul_apply]

theorem matrixMulCircuit_valid {m n p : ℕ} (v : MatrixInputs m n p → ℝ) :
    (matrixMulCircuit m n p).Valid v :=
  fun _ => dotExpr_valid n _ _ v

/-- Includes every scalar input load, multiply, add, zero constant, and output store. -/
theorem matrixMulCircuit_cost (m n p : ℕ) :
    (matrixMulCircuit m n p).cost = m*p*(4*n+2) := by
  simp [Circuit.cost, matrixMulCircuit, dotExpr_cost]

theorem matrixMulCircuit_entry_executes {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ)
    (i : Fin m) (j : Fin p) :
    Expr.Executes (matrixInput A B) ((matrixMulCircuit m n p).output (i,j))
      ((A*B) i j) (4*n+1) := by
  simpa [matrixMulCircuit, dotExpr_cost, dotExpr_eval, matrixInput, Matrix.mul_apply] using
    Expr.executes_of_valid (matrixInput A B) ((matrixMulCircuit m n p).output (i,j))
      (matrixMulCircuit_valid (matrixInput A B) (i,j))

/-- A concrete polynomial upper bound in the total matrix-side parameter. -/
theorem matrixMulCircuit_cost_polynomial (m n p : ℕ) :
    (matrixMulCircuit m n p).cost ≤ 6*(m+n+p+1)^3 := by
  rw [matrixMulCircuit_cost]
  have hm : m ≤ m+n+p+1 := by omega
  have hp : p ≤ m+n+p+1 := by omega
  have hn : 4*n+2 ≤ 6*(m+n+p+1) := by omega
  calc
    m*p*(4*n+2) ≤ (m+n+p+1)*(m+n+p+1)*(6*(m+n+p+1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul hm hp) hn
    _ = _ := by ring

end MatrixSpencer.RealRAM
