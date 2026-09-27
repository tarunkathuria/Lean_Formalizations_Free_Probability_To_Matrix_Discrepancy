import MatrixSpencer.MSSquarePolynomialRuntime
import MatrixSpencer.KSRuntimePolynomialRepresentation

/-! The complete square-MS operation and random-draw counts, including the
constant-success retry choice, are natural multivariate polynomials in the
original input dimensions. The allowed solver's coefficient and degree are
fixed parameters; no walk-specific cost assumption remains. -/
noncomputable section
namespace MatrixSpencer.MSSquareRuntimePolynomialCertificate
open KSRuntimePolynomialRepresentation
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

theorem operations_polynomial (P : KSPolynomialConvexSolver.PolynomialSolver) :
    Represented (MSSquarePolynomialRuntime.operations P) := by
  unfold MSSquarePolynomialRuntime.operations MSCountedSquareProcess.operations MSCountedSquareProcess.phaseCost
    MSCountedSquareProcess.configCost MSCountedSquareProcess.restoreCost MSCountedOriginalPhases.phaseCost
    MSCountedOriginalPhases.epochCost MSCountedAcceptedEpoch.operations RealRAM.MSEpochFactorySetup.configCost
    RealRAM.MSPhaseSetup.setupCost MSManuscriptNumericalHalfPhase.epochCalls MSCountedOriginalEpoch.operations
    RealRAM.MSEpochLoops.costBound RealRAM.MSEpochScalarSetup.costBound RealRAM.MSLoopCapSetup.movementCap
    RealRAM.MSLoopCapSetup.movementUniform MSCountedCompiledEpoch.stepWork MSCountedCompiledPreparation.work
    MSCountedPreparation.roundBudget MSCountedCompiledPreparation.responseBudget
    MSCountedPreparationBounds.responseBudget MSCountedResponse.queryBudget
    MSCountedPreparationBounds.programSize MSManuscriptPolynomialQueryMagnitude.responseJacobi
    MSManuscriptPolynomialQueryMagnitude.responseEntry MSManuscriptPolynomialQueryMagnitude.potentialCap
    MSManuscriptPolynomialQueryCleanup.cleanupJacobi KSJacobiPolynomialBounds.jacobi
    MSManuscriptPolynomialQueryParameters.preparation MSManuscriptPolynomialQueryParameters.paidInv
    MSManuscriptPolynomialQueryParameters.valueInv MSManuscriptPolynomialQueryParameters.slopeStepInv
    MSManuscriptPolynomialQueryParameters.precisionInv MSManuscriptPolynomialQueryParameters.thresholdInv
    MSManuscriptPolynomialQueryParameters.cleanupInv MSManuscriptPolynomialQueryCurvature.curvature
    MSManuscriptPolynomialQueryCurvature.second MSManuscriptPolynomialQueryCurvature.joint
    MSManuscriptPolynomialQueryCurvature.value MSManuscriptPolynomialQueryCurvature.denominator
    MSManuscriptPolynomialQueryCurvature.center RealRAM.MSRawOwnerReport.setupCost
    RealRAM.OwnerSDPSetup.blockBound RealRAM.OwnerSDPSetup.objectiveBound RealRAM.OwnerSDPBlocks.sourceBound
    RealRAM.OwnerSDPBlocks.productBound MSConvexAcceptancePolynomial.acceptanceCost
    RealRAM.MSAcceptanceData.epochCost RealRAM.MSConvexAcceptance.queryBudget
    MSConvexAcceptancePolynomial.programSize MSConvexAcceptancePolynomial.precisionCap
    MSConvexPolynomialTangentParameters.precisionInv MSManuscriptPolynomialQueryParameters.acceptanceRadius
  unfold RealRAM.MSRawOwnerReport.setupCost RealRAM.OwnerSDPSetup.blockBound
    RealRAM.OwnerSDPSetup.objectiveBound RealRAM.OwnerSDPBlocks.sourceBound
    RealRAM.OwnerSDPBlocks.productBound
  ks_poly_cert

theorem draws_polynomial :
    Represented MSSquarePolynomialRuntime.draws := by
  unfold MSSquarePolynomialRuntime.draws MSCountedSquareProcess.draws MSManuscriptNumericalHalfPhase.epochCalls
    MSCountedOriginalEpoch.draws RealRAM.MSLoopCapSetup.movementCap
    RealRAM.MSLoopCapSetup.movementUniform MSManuscriptPolynomialQueryCurvature.joint
    MSManuscriptPolynomialQueryCurvature.value MSManuscriptPolynomialQueryCurvature.denominator
    MSManuscriptPolynomialQueryCurvature.center
  ks_poly_cert

theorem constant_success_operations_polynomial (P : KSPolynomialConvexSolver.PolynomialSolver) :
    Represented (fun N D _r => MSSquarePolynomialRuntime.operations P N D (MSSquarePolynomialRuntime.retries N)) := by
  unfold MSSquarePolynomialRuntime.retries MSManuscriptRetryBudget.retries MSSquarePolynomialRuntime.operations
    MSCountedSquareProcess.operations MSCountedSquareProcess.phaseCost MSCountedSquareProcess.configCost
    MSCountedSquareProcess.restoreCost MSCountedOriginalPhases.phaseCost MSCountedOriginalPhases.epochCost
    MSCountedAcceptedEpoch.operations RealRAM.MSEpochFactorySetup.configCost RealRAM.MSPhaseSetup.setupCost
    MSManuscriptNumericalHalfPhase.epochCalls MSCountedOriginalEpoch.operations RealRAM.MSEpochLoops.costBound
    RealRAM.MSEpochScalarSetup.costBound RealRAM.MSLoopCapSetup.movementCap
    RealRAM.MSLoopCapSetup.movementUniform MSCountedCompiledEpoch.stepWork MSCountedCompiledPreparation.work
    MSCountedPreparation.roundBudget MSCountedCompiledPreparation.responseBudget
    MSCountedPreparationBounds.responseBudget MSCountedResponse.queryBudget
    MSCountedPreparationBounds.programSize MSManuscriptPolynomialQueryMagnitude.responseJacobi
    MSManuscriptPolynomialQueryMagnitude.responseEntry MSManuscriptPolynomialQueryMagnitude.potentialCap
    MSManuscriptPolynomialQueryCleanup.cleanupJacobi KSJacobiPolynomialBounds.jacobi
    MSManuscriptPolynomialQueryParameters.preparation MSManuscriptPolynomialQueryParameters.paidInv
    MSManuscriptPolynomialQueryParameters.valueInv MSManuscriptPolynomialQueryParameters.slopeStepInv
    MSManuscriptPolynomialQueryParameters.precisionInv MSManuscriptPolynomialQueryParameters.thresholdInv
    MSManuscriptPolynomialQueryParameters.cleanupInv MSManuscriptPolynomialQueryCurvature.curvature
    MSManuscriptPolynomialQueryCurvature.second MSManuscriptPolynomialQueryCurvature.joint
    MSManuscriptPolynomialQueryCurvature.value MSManuscriptPolynomialQueryCurvature.denominator
    MSManuscriptPolynomialQueryCurvature.center RealRAM.MSRawOwnerReport.setupCost
    RealRAM.OwnerSDPSetup.blockBound RealRAM.OwnerSDPSetup.objectiveBound RealRAM.OwnerSDPBlocks.sourceBound
    RealRAM.OwnerSDPBlocks.productBound MSConvexAcceptancePolynomial.acceptanceCost
    RealRAM.MSAcceptanceData.epochCost RealRAM.MSConvexAcceptance.queryBudget
    MSConvexAcceptancePolynomial.programSize MSConvexAcceptancePolynomial.precisionCap
    MSConvexPolynomialTangentParameters.precisionInv MSManuscriptPolynomialQueryParameters.acceptanceRadius
  unfold RealRAM.MSRawOwnerReport.setupCost RealRAM.OwnerSDPSetup.blockBound
    RealRAM.OwnerSDPSetup.objectiveBound RealRAM.OwnerSDPBlocks.sourceBound
    RealRAM.OwnerSDPBlocks.productBound
  ks_poly_cert

theorem constant_success_draws_polynomial :
    Represented (fun N D _r => MSSquarePolynomialRuntime.draws N D (MSSquarePolynomialRuntime.retries N)) := by
  unfold MSSquarePolynomialRuntime.retries MSManuscriptRetryBudget.retries MSSquarePolynomialRuntime.draws
    MSCountedSquareProcess.draws MSManuscriptNumericalHalfPhase.epochCalls MSCountedOriginalEpoch.draws
    RealRAM.MSLoopCapSetup.movementCap
    RealRAM.MSLoopCapSetup.movementUniform MSManuscriptPolynomialQueryCurvature.joint
    MSManuscriptPolynomialQueryCurvature.value MSManuscriptPolynomialQueryCurvature.denominator
    MSManuscriptPolynomialQueryCurvature.center
  ks_poly_cert

end MatrixSpencer.MSSquareRuntimePolynomialCertificate
