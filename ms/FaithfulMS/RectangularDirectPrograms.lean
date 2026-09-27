import FaithfulMS.RectangularDirectEpochAcceptanceData
import MatrixSpencer.NatPolynomialBound
import MatrixSpencer.RealRAMJacobiIteration

/-! Local implementation obligations for composing the direct algorithm.
This record is an intermediate compiler interface. It is instantiated from
primal SDP extraction and scalar/EVD circuits before the final runtime theorem;
it is not an additional permitted computational primitive. -/
open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularDirectPrograms
open RealRAM.JacobiIteration (Counted)
open RectangularRidgePreparationData MSManuscriptSupportedOwner
open RectangularRidgeEpochInput RectangularDirectEpochRun

structure Programs (S : FaithfulMS.DirectSDP.PolynomialService) where
  response : ∀ {N d : ℕ} [Nonempty (Fin d)] (a : Fin d) (P : Parameters N d)
    (hP : P.Valid) (O : Owner N), Counted (Matrix (Fin O.dim) (Fin O.dim) ℝ)
  response_value : ∀ {N d : ℕ} [Nonempty (Fin d)] (a : Fin d) (P : Parameters N d)
    (hP : P.Valid) (O : Owner N), State O →
      (response a P hP O).value = RectangularDirectSolver.value S.service a P hP O
  responseBudget : ℕ → ℕ → ℕ
  response_cost : ∀ {N d : ℕ} [Nonempty (Fin d)] (a : Fin d) (P : Parameters N d)
    (hP : P.Valid) (O : Owner N), State O → (response a P hP O).cost ≤ responseBudget N d
  response_polynomial : NatPolynomialBound.Bounded (fun N d _ => responseBudget N d)
  accepts : ∀ {N d : ℕ} [Nonempty (Fin d)] (a : Fin d) (c : Config N d)
    (s : Certified c), Counted Bool
  accepts_value : ∀ {N d : ℕ} [Nonempty (Fin d)] (a : Fin d) (c : Config N d)
    (s : Certified c), (accepts a c s).value = RectangularDirectEpochAcceptanceData.accepts S.service a c s
  acceptanceBudget : ℕ → ℕ → ℕ
  accepts_cost : ∀ {N d : ℕ} [Nonempty (Fin d)] (a : Fin d) (c : Config N d)
    (s : Certified c), (accepts a c s).cost ≤ acceptanceBudget N d
  acceptance_polynomial : NatPolynomialBound.Bounded (fun N d _ => acceptanceBudget N d)

end MatrixSpencer.RectangularDirectPrograms
