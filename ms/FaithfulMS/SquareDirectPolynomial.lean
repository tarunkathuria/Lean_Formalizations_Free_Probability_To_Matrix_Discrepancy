import FaithfulMS.SquareDirectRuntime
import FaithfulMS.RectangularDirectPolynomialMajorant

/-! Uniform polynomial majorants for the direct-primal square algorithm.
The solver fixes one coefficient and degree before any input dimension or
retry count is chosen. Every local implementation has already been counted. -/
noncomputable section
namespace FaithfulMS.SquareDirectPolynomial
open MatrixSpencer NatPolynomialBound
set_option maxRecDepth 24000
set_option maxHeartbeats 4000000

theorem operations_bounded (P : DirectSDP.PolynomialService) :
    Bounded (fun N D r => SquareDirectRuntime.operations P N D r) := by
  dsimp only [SquareDirectRuntime.operations, SquareDirectProcess.operations,
    SquareDirectProcess.phaseCost, SquareDirectOriginalPhases.phaseCost,
    SquareDirectOriginalPhases.epochCost, SquareDirectProcess.configCost,
    SquareDirectProcess.restoreCost, SquareDirectOriginalEpoch.operations,
    SquareDirectAcceptanceArithmetic.work, SquareDirectAcceptanceArithmetic.reportWork,
    SquareDirectCompiledEpoch.stepWork, SquareDirectCountedEpoch.stepWork,
    SquareDirectCountedCompiledPreparation.work, SquareDirectCountedPreparation.roundBudget,
    SquareDirectCountedResponse.work, DirectSDPArithmetic.squareCost,
    DirectSDPArithmetic.squareSize, RealRAM.MSEpochFactorySetup.configCost,
    RealRAM.MSPhaseSetup.setupCost, RealRAM.MSEpochLoops.costBound,
    RealRAM.MSEpochScalarSetup.costBound, RealRAM.MSLoopCapSetup.movementCap,
    RealRAM.MSLoopCapSetup.movementUniform,
    MSManuscriptPolynomialQueryCleanup.cleanupJacobi,
    KSJacobiPolynomialBounds.jacobi,
    MSManuscriptPolynomialQueryParameters.preparation,
    MSManuscriptPolynomialQueryParameters.paidInv,
    MSManuscriptPolynomialQueryParameters.thresholdInv,
    MSManuscriptPolynomialQueryParameters.cleanupInv,
    MSManuscriptPolynomialQueryCurvature.curvature,
    MSManuscriptPolynomialQueryCurvature.second,
    MSManuscriptPolynomialQueryCurvature.joint,
    MSManuscriptPolynomialQueryCurvature.value,
    MSManuscriptPolynomialQueryCurvature.denominator,
    MSManuscriptPolynomialQueryCurvature.center]
  direct_ridge_polynomial_bound

theorem draws_bounded :
    Bounded (fun N D r => SquareDirectRuntime.draws N D r) := by
  dsimp only [SquareDirectRuntime.draws, SquareDirectProcess.draws,
    SquareDirectOriginalEpoch.draws, RealRAM.MSLoopCapSetup.movementCap,
    RealRAM.MSLoopCapSetup.movementUniform,
    MSManuscriptPolynomialQueryCurvature.joint,
    MSManuscriptPolynomialQueryCurvature.value,
    MSManuscriptPolynomialQueryCurvature.denominator,
    MSManuscriptPolynomialQueryCurvature.center]
  direct_ridge_polynomial_bound

theorem uniform_majorant (P : DirectSDP.PolynomialService) :
    ∃ C e : ℕ, 0<C ∧ ∀ N D r,
      SquareDirectRuntime.operations P N D r ≤ C*(N+D+r+2)^e ∧
      SquareDirectRuntime.draws N D r ≤ C*(N+D+r+2)^e := by
  obtain ⟨C,e,h⟩ := NatPolynomialBound.add (operations_bounded P) draws_bounded
  refine ⟨C+1,e,by omega,?_⟩
  intro N D r
  have hh := h N D r
  dsimp only at hh
  have hc := Nat.mul_le_mul_right ((N+D+r+2)^e) (show C≤C+1 by omega)
  constructor <;> omega

def confidenceRetries (N k : ℕ) : ℕ :=
  (N+1)*MSManuscriptNumericalHalfPhase.epochCalls+k+1

theorem confidence_majorant (P : DirectSDP.PolynomialService) :
    ∃ C e : ℕ, 0<C ∧ ∀ N D k,
      SquareDirectRuntime.operations P N D (confidenceRetries N k) ≤ C*(N+D+k+2)^e ∧
      SquareDirectRuntime.draws N D (confidenceRetries N k) ≤ C*(N+D+k+2)^e := by
  obtain ⟨C,e,hC,h⟩ := uniform_majorant P
  let E := MSManuscriptNumericalHalfPhase.epochCalls
  refine ⟨C*(E+3)^e,e,by positivity,?_⟩
  intro N D k
  have hs : N+D+confidenceRetries N k+2 ≤ (E+3)*(N+D+k+2) := by
    dsimp [confidenceRetries,E]
    nlinarith
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hs e)
  rw [mul_pow,←mul_assoc] at hp
  exact ⟨(h N D (confidenceRetries N k)).1.trans hp,
    (h N D (confidenceRetries N k)).2.trans hp⟩
end FaithfulMS.SquareDirectPolynomial
