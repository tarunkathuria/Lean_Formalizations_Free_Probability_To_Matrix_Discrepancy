import MatrixSpencer.RealRAMComplexArithmetic
import MatrixSpencer.RealRAMJacobiIteration
import MatrixSpencer.TransportVariational
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus

/-! Exact Hermitian spectral calculus with scalar reconstruction.

The sole spectral instruction returns an eigendecomposition. Applying scalar
square roots or reciprocal square roots and reconstructing the matrix are
separate operations. In particular this interface supplies no covariance
derivative, support, transport, or optimization result as a primitive.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.SpectralArithmetic
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
local instance {d : ℕ} : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
variable {d : ℕ}

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev Registers (d : ℕ) := (Fin d × Fin d × Bool) ⊕ Fin d

/-- The explicitly allowed exact spectral instruction. Its deterministic
choice at repeated eigenvalues is fixed by the spectral theorem's basis. -/
inductive EVDExecutes (A : Mat d) (hA : A.IsHermitian) :
    (Fin d → ℝ) → Mat d → ℕ → Prop
  | evd : EVDExecutes A hA hA.eigenvalues hA.eigenvectorUnitary 1

def input (U : Mat d) (z : Fin d → ℝ) : Registers d → ℝ
  | .inl (i,j,b) => if b then (U i j).im else (U i j).re
  | .inr i => z i

def entry (i j : Fin d) : ComplexExpr (Registers d) :=
  ⟨.input (.inl (i,j,false)), .input (.inl (i,j,true))⟩

theorem entry_eval (U : Mat d) (z : Fin d → ℝ) (i j : Fin d) :
    (entry i j).eval (input U z) = U i j := by
  apply Complex.ext <;> rfl

def reconstruct (i j : Fin d) : ComplexExpr (Registers d) :=
  ComplexExpr.sum (fun k : Fin d => ComplexExpr.mul
    (ComplexExpr.smul (.input (.inr k)) (entry i k))
    (ComplexExpr.conj (entry j k)))

theorem reconstruct_eval (U : Mat d) (z : Fin d → ℝ) (i j : Fin d) :
    (reconstruct i j).eval (input U z) =
      (U * Matrix.diagonal (fun k => (z k : ℂ)) * Uᴴ) i j := by
  simp only [reconstruct, ComplexExpr.eval_sum, ComplexExpr.eval_mul,
    ComplexExpr.eval_smul, ComplexExpr.eval_conj, entry_eval, Expr.eval, input,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp [Algebra.smul_def, Matrix.diagonal, mul_comm]

theorem reconstruct_valid (U : Mat d) (z : Fin d → ℝ) (i j : Fin d) :
    (reconstruct i j).Valid (input U z) := by
  apply ComplexExpr.valid_sum
  intro k
  apply ComplexExpr.valid_mul
  · exact ComplexExpr.valid_smul trivial ⟨trivial,trivial⟩
  · exact ComplexExpr.valid_conj ⟨trivial,trivial⟩

theorem reconstruct_cost (i j : Fin d) :
    (reconstruct i j).cost ≤ 28*d+2 := by
  have h := ComplexExpr.cost_sum_le
    (fun k : Fin d => ComplexExpr.mul
      (ComplexExpr.smul (.input (.inr k)) (entry i k))
      (ComplexExpr.conj (entry j k))) 26 (by
        intro k
        simp [ComplexExpr.mul, ComplexExpr.smul, ComplexExpr.conj,
          entry, ComplexExpr.cost, Expr.cost])
  simpa [reconstruct, Fintype.card_fin, mul_comm] using h

/-- Each reconstructed complex entry is executed as two real circuits. -/
theorem reconstruct_execution (U : Mat d) (z : Fin d → ℝ) (i j : Fin d) :
    Expr.Executes (input U z) (reconstruct i j).re
      ((U * Matrix.diagonal (fun k => (z k : ℂ)) * Uᴴ) i j).re
      (reconstruct i j).re.cost ∧
    Expr.Executes (input U z) (reconstruct i j).im
      ((U * Matrix.diagonal (fun k => (z k : ℂ)) * Uᴴ) i j).im
      (reconstruct i j).im.cost := by
  simpa only [reconstruct_eval] using
    ComplexExpr.executes (reconstruct i j) (input U z) (reconstruct_valid U z i j)

def assembly (U : Mat d) (z : Fin d → ℝ) : Counted (Mat d) :=
  ⟨fun i j => (reconstruct i j).eval (input U z),
    ∑ i : Fin d, ∑ j : Fin d, ((reconstruct i j).cost + 2)⟩

theorem assembly_value (U : Mat d) (z : Fin d → ℝ) :
    (assembly U z).value = U * Matrix.diagonal (fun k => (z k : ℂ)) * Uᴴ := by
  ext i j
  exact reconstruct_eval U z i j

theorem assembly_cost (U : Mat d) (z : Fin d → ℝ) :
    (assembly U z).cost ≤ d*d*(28*d+4) := by
  dsimp only [assembly]
  calc
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, (28*d+4) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have h := reconstruct_cost i j
      omega
    _ = _ := by simp; ring

/-- Scalar zero is handled before reciprocal square root is requested. -/
def inverseRootScalar (x : ℝ) : ℝ := if x = 0 then 0 else (Real.sqrt x)⁻¹

def rootExpr : Expr Unit := .sqrt (.input ())
def inverseRootExpr : Expr Unit := .div (.constant 1) rootExpr

theorem root_scalar_execution (x : ℝ) (hx : 0 ≤ x) :
    Expr.Executes (fun _ : Unit => x) rootExpr (Real.sqrt x) 2 :=
  .sqrt (.input ()) hx

theorem inverseRoot_scalar_execution (x : ℝ) (hx : 0 < x) :
    Expr.Executes (fun _ : Unit => x) inverseRootExpr ((Real.sqrt x)⁻¹) 4 := by
  simpa only [inverseRootExpr, Rat.cast_one, one_div] using
    Expr.Executes.div (.constant 1) (root_scalar_execution x hx.le)
      (Real.sqrt_pos.mpr hx).ne'

def spectralRoot (A : Mat d) (hA : A.IsHermitian) : Counted (Mat d) :=
  let r := assembly (hA.eigenvectorUnitary : Mat d) (fun i => Real.sqrt (hA.eigenvalues i))
  ⟨r.value, 1+3*d+r.cost⟩

def spectralInverseRoot (A : Mat d) (hA : A.IsHermitian) : Counted (Mat d) :=
  let r := assembly (hA.eigenvectorUnitary : Mat d) (fun i => inverseRootScalar (hA.eigenvalues i))
  ⟨r.value, 1+8*d+r.cost⟩

theorem spectralRoot_value (A : Mat d) (hA : A.IsHermitian) :
    (spectralRoot A hA).value = cfc Real.sqrt A := by
  rw [hA.cfc_eq]
  exact assembly_value _ _

theorem spectralRoot_psd_value (A : Mat d) (hA : A.PosSemidef) :
    (spectralRoot A hA.isHermitian).value = CFC.sqrt A := by
  rw [spectralRoot_value, CFC.sqrt_eq_real_sqrt A hA.nonneg,
    cfcₙ_eq_cfc (hf0 := Real.sqrt_zero)]

theorem spectralInverseRoot_value (A : Mat d) (hA : A.IsHermitian) :
    (spectralInverseRoot A hA).value = cfc inverseRootScalar A := by
  rw [hA.cfc_eq]
  exact assembly_value _ _

theorem spectralRoot_cost (A : Mat d) (hA : A.IsHermitian) :
    (spectralRoot A hA).cost ≤ 40*(d+1)^3 := by
  have h := assembly_cost (hA.eigenvectorUnitary : Mat d)
    (fun i => Real.sqrt (hA.eigenvalues i))
  dsimp only [spectralRoot]
  nlinarith

theorem spectralInverseRoot_cost (A : Mat d) (hA : A.IsHermitian) :
    (spectralInverseRoot A hA).cost ≤ 40*(d+1)^3 := by
  have h := assembly_cost (hA.eigenvectorUnitary : Mat d)
    (fun i => inverseRootScalar (hA.eigenvalues i))
  dsimp only [spectralInverseRoot]
  nlinarith

end FaithfulMS.SpectralArithmetic
