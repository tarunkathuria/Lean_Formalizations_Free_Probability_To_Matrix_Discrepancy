import FaithfulMS.DirectGammaArithmetic
import FaithfulMS.RectangularDirectConcreteAcceptance

/-! Audit facts for the concrete direct-density arithmetic. The only spectral
instruction is exact Hermitian EVD. Every square root and division used by
transport satisfies the domain hypotheses of the scalar execution relation.
Matrix products, source formation, Gram formation and trace pairing use the
explicit real circuits certified in the imported modules. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.DirectArithmeticAudit
open MatrixSpencer MatrixSpencer.RealRAM SpectralArithmetic
variable {d : ℕ}

/-- PSD inputs make all scalar square roots in the EVD reconstruction legal. -/
theorem root_instructions (A : SpectralArithmetic.Mat d) (hA : A.PosSemidef) :
    EVDExecutes A hA.isHermitian hA.isHermitian.eigenvalues hA.isHermitian.eigenvectorUnitary 1 ∧
      ∀ i, Expr.Executes (fun _ : Unit => hA.isHermitian.eigenvalues i)
        rootExpr (Real.sqrt (hA.isHermitian.eigenvalues i)) 2 := by
  exact ⟨.evd,fun i => root_scalar_execution _ (hA.eigenvalues_nonneg i)⟩

/-- Strict positivity, already proved for both completed transport inputs,
ensures that the inverse-square-root scalar routine never divides by zero. -/
theorem inverse_root_instructions (A : SpectralArithmetic.Mat d) (hA : A.PosDef) :
    EVDExecutes A hA.isHermitian hA.isHermitian.eigenvalues hA.isHermitian.eigenvectorUnitary 1 ∧
      ∀ i, Expr.Executes (fun _ : Unit => hA.isHermitian.eigenvalues i)
        inverseRootExpr (inverseRootScalar (hA.isHermitian.eigenvalues i)) 4 := by
  refine ⟨.evd,fun i => ?_⟩
  rw [inverseRootScalar,if_neg (hA.eigenvalues_pos i).ne']
  exact inverseRoot_scalar_execution _ (hA.eigenvalues_pos i)

/-- The ordinary transport output equals the variational optimizer and its
charged work is independent of spectral gaps and condition numbers. -/
theorem transport_certified (S M : SpectralArithmetic.Mat d)
    (hS : S.PosDef) (hM : M.PosDef) :
    (DirectGammaArithmetic.transport S M hS hM).value = transportOptimizer S M ∧
      (DirectGammaArithmetic.transport S M hS hM).cost ≤ DirectGammaArithmetic.transportBudget d :=
  ⟨DirectGammaArithmetic.transport_value S M hS hM,
    DirectGammaArithmetic.transport_cost S M hS hM⟩

end FaithfulMS.DirectArithmeticAudit
