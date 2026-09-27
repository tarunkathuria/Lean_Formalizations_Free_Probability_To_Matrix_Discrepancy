import FaithfulMS.SquareDirectCountedPreparation
import MatrixSpencer.MSManuscriptPolynomialQueryCleanup

/-! The cleanup iteration bound is inherited unchanged. The only report
premise here is a local cost bound, to be supplied by the direct SDP compiler. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.SquareDirectCountedBounds
open MatrixSpencer MSManuscriptSupportedGamma MSManuscriptSupportedOwner
variable [SquareDirectOracle.Oracle] {m N d : ℕ}

theorem bounds (P : Parameters m d) (hP : P.Valid) (hm : m ≤ N)
    (hδ : P.floor=1/8192) (E : SquareDirectCountedPreparation.Evaluator P) (R : ℕ)
    (hR : ∀ O, MSManuscriptSupportedPreparation.State P O → (E.response O).cost≤R) :
    SquareDirectCountedPreparation.Bounds P E
      (MSManuscriptPolynomialQueryCleanup.cleanupJacobi N) 0 R := by
  constructor
  · intro O hO
    rw [hδ]
    apply MSManuscriptPolynomialQueryCleanup.ceiling_input_le O (hO.2.2.trans hm)
      (by simpa only [hδ] using hO.1) hO.2.1
  · exact hR

end FaithfulMS.SquareDirectCountedBounds
