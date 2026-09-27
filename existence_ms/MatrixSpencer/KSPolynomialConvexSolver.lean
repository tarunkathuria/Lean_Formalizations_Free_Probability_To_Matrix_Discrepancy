import MatrixSpencer.KSConvexValueOracle
import MatrixSpencer.RealRAMJacobiIteration



noncomputable section
namespace MatrixSpencer.KSPolynomialConvexSolver
open KSFullManuscriptAffinePSD
open RealRAM.JacobiIteration (Counted)

/-- Real array entries in an affine pencil, objective vector, and two scalars. -/
def dataSize (ℓ k : ℕ) : ℕ := (ℓ+1)*k^2+ℓ+2

structure PolynomialSolver where
  solver : KSConvexValueOracle.Solver
  work : {ℓ k : ℕ} → Data ℓ k → Space ℓ → ℝ → ℝ → ℕ
  coefficient : ℕ
  degree : ℕ
  bound : ∀ {ℓ k : ℕ} (D : Data ℓ k) (c : Space ℓ) (offset ν : ℝ),
    0 < ν → work D c offset ν ≤ coefficient*(dataSize ℓ k+⌈ν⁻¹⌉₊+1)^degree

def PolynomialSolver.run (P : PolynomialSolver) {ℓ k : ℕ}
    (D : Data ℓ k) (c : Space ℓ) (offset ν : ℝ) : Counted ℝ :=
  ⟨P.solver.report D c offset ν, P.work D c offset ν⟩

theorem PolynomialSolver.run_value (P : PolynomialSolver) {ℓ k : ℕ}
    (D : Data ℓ k) (c : Space ℓ) (offset ν : ℝ) :
    (P.run D c offset ν).value = P.solver.report D c offset ν := rfl

/-- Once the walk supplies an actual natural reciprocal-precision bound,
the only remaining exponent is the fixed exponent of the permitted solver. -/
theorem PolynomialSolver.run_cost_le (P : PolynomialSolver) {ℓ k : ℕ}
    (D : Data ℓ k) (c : Space ℓ) (offset : ℝ) {ν : ℝ} (hν : 0 < ν)
    {S V : ℕ} (hS : dataSize ℓ k ≤ S) (hV : ν⁻¹ ≤ (V : ℝ)) :
    (P.run D c offset ν).cost ≤ P.coefficient*(S+V+1)^P.degree := by
  have hv : ⌈ν⁻¹⌉₊ ≤ V := Nat.ceil_le.mpr hV
  apply (P.bound D c offset ν hν).trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

end MatrixSpencer.KSPolynomialConvexSolver
