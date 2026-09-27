import RadialKS.FrameArithmetic

open Matrix
open scoped BigOperators
noncomputable section
namespace RadialKS.RuntimeMatrix
open MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open RadialBasis (Space)
variable {m n p : ℕ}

def product (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ) :
    Counted (Matrix (Fin m) (Fin p) ℝ) :=
  ⟨fun i j => (matrixMulCircuit m n p).eval (matrixInput A B) (i,j),
    (matrixMulCircuit m n p).cost + 3*m*p + m*n + n*p + 1⟩

theorem product_value (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ) :
    (product A B).value = A * B := by
  ext i j
  exact matrixMulCircuit_eval A B i j

theorem product_entry_execution (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) (i : Fin m) (j : Fin p) :
    Expr.Executes (matrixInput A B) ((matrixMulCircuit m n p).output (i,j))
      ((product A B).value i j) (4*n+1) := by
  rw [product_value]
  exact matrixMulCircuit_entry_executes A B i j

theorem product_cost (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ)
    {b : ℕ} (hb : 1 ≤ b) (hm : m ≤ b) (hn : n ≤ b) (hp : p ≤ b) :
    (product A B).cost ≤ 12*b^3 := by
  have h1 : m*p*(4*n+2) ≤ b*b*(4*b+2) := by gcongr
  have h2 : 3*m*p ≤ 3*b*b := by gcongr
  have h3 : m*n ≤ b*b := by gcongr
  have h4 : n*p ≤ b*b := by gcongr
  simp only [product, matrixMulCircuit_cost]
  nlinarith

def matvec (A : Matrix (Fin m) (Fin n) ℝ) (v : Space n) : Counted (Space m) :=
  let p := product A (fun i (_ : Fin 1) => v i)
  ⟨WithLp.toLp 2 (fun i => p.value i 0), p.cost+2*m+1⟩

theorem matvec_value (A : Matrix (Fin m) (Fin n) ℝ) (v : Space n) :
    (matvec A v).value = WithLp.toLp 2 (A *ᵥ WithLp.ofLp v) := by
  ext i
  simp only [matvec, product_value, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    PiLp.toLp_apply, PiLp.ofLp_apply]

end RadialKS.RuntimeMatrix
