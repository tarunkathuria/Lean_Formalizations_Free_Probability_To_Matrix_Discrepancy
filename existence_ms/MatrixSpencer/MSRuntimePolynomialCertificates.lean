import MatrixSpencer.KSRuntimePolynomialRepresentation
import MatrixSpencer.MSCountedOriginalEpoch

/-! The displayed operation/draw bounds are actual natural multivariate
polynomials. Monotonicity permits replacing restricted cardinalities by the
original input size. Solver coefficient and degree are fixed parameters. -/
noncomputable section
namespace MatrixSpencer.MSRuntimePolynomialCertificates
open KSRuntimePolynomialRepresentation
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000

theorem trial_polynomial (P : KSPolynomialConvexSolver.PolynomialSolver) :
    Represented (fun N d _r=>MSCountedOriginalEpoch.operations P N d) := by
  unfold MSCountedOriginalEpoch.operations RealRAM.MSEpochLoops.costBound
    RealRAM.MSEpochScalarSetup.costBound RealRAM.MSLoopCapSetup.movementCap
    RealRAM.MSLoopCapSetup.movementUniform MSCountedCompiledEpoch.stepWork
    MSCountedCompiledPreparation.work MSCountedPreparation.roundBudget
    MSCountedCompiledPreparation.responseBudget MSCountedPreparationBounds.responseBudget
    MSCountedResponse.queryBudget MSCountedPreparationBounds.programSize
    MSManuscriptPolynomialQueryMagnitude.responseJacobi
    MSManuscriptPolynomialQueryMagnitude.responseEntry
    MSManuscriptPolynomialQueryMagnitude.potentialCap
    MSManuscriptPolynomialQueryCleanup.cleanupJacobi KSJacobiPolynomialBounds.jacobi
    MSManuscriptPolynomialQueryParameters.preparation MSManuscriptPolynomialQueryParameters.paidInv
    MSManuscriptPolynomialQueryParameters.valueInv MSManuscriptPolynomialQueryParameters.slopeStepInv
    MSManuscriptPolynomialQueryParameters.precisionInv MSManuscriptPolynomialQueryParameters.thresholdInv
    MSManuscriptPolynomialQueryParameters.cleanupInv
    MSManuscriptPolynomialQueryCurvature.curvature MSManuscriptPolynomialQueryCurvature.second
    MSManuscriptPolynomialQueryCurvature.joint MSManuscriptPolynomialQueryCurvature.value
    MSManuscriptPolynomialQueryCurvature.denominator MSManuscriptPolynomialQueryCurvature.center
    RealRAM.MSRawOwnerReport.setupCost RealRAM.OwnerSDPSetup.blockBound
    RealRAM.OwnerSDPSetup.objectiveBound RealRAM.OwnerSDPBlocks.sourceBound
    RealRAM.OwnerSDPBlocks.productBound
  ks_poly_cert

theorem trial_monotone (P : KSPolynomialConvexSolver.PolynomialSolver) {N M d D : ℕ} (hN : N≤M) (hd : d≤D) :
    MSCountedOriginalEpoch.operations P N d≤MSCountedOriginalEpoch.operations P M D := by
  unfold MSCountedOriginalEpoch.operations RealRAM.MSEpochLoops.costBound
    RealRAM.MSEpochScalarSetup.costBound RealRAM.MSLoopCapSetup.movementCap
    RealRAM.MSLoopCapSetup.movementUniform MSCountedCompiledEpoch.stepWork
    MSCountedCompiledPreparation.work MSCountedPreparation.roundBudget
    MSCountedCompiledPreparation.responseBudget MSCountedPreparationBounds.responseBudget
    MSCountedResponse.queryBudget MSCountedPreparationBounds.programSize
    MSManuscriptPolynomialQueryMagnitude.responseJacobi
    MSManuscriptPolynomialQueryMagnitude.responseEntry
    MSManuscriptPolynomialQueryMagnitude.potentialCap
    MSManuscriptPolynomialQueryCleanup.cleanupJacobi KSJacobiPolynomialBounds.jacobi
    MSManuscriptPolynomialQueryParameters.preparation MSManuscriptPolynomialQueryParameters.paidInv
    MSManuscriptPolynomialQueryParameters.valueInv MSManuscriptPolynomialQueryParameters.slopeStepInv
    MSManuscriptPolynomialQueryParameters.precisionInv MSManuscriptPolynomialQueryParameters.thresholdInv
    MSManuscriptPolynomialQueryParameters.cleanupInv
    MSManuscriptPolynomialQueryCurvature.curvature MSManuscriptPolynomialQueryCurvature.second
    MSManuscriptPolynomialQueryCurvature.joint MSManuscriptPolynomialQueryCurvature.value
    MSManuscriptPolynomialQueryCurvature.denominator MSManuscriptPolynomialQueryCurvature.center
    RealRAM.MSRawOwnerReport.setupCost RealRAM.OwnerSDPSetup.blockBound
    RealRAM.OwnerSDPSetup.objectiveBound RealRAM.OwnerSDPBlocks.sourceBound
    RealRAM.OwnerSDPBlocks.productBound
  gcongr

theorem acceptance_polynomial (P : KSPolynomialConvexSolver.PolynomialSolver) :
    Represented (fun N d _r=>MSConvexAcceptancePolynomial.acceptanceCost P N d) := by
  unfold MSConvexAcceptancePolynomial.acceptanceCost RealRAM.MSAcceptanceData.epochCost
    RealRAM.MSConvexAcceptance.queryBudget MSConvexAcceptancePolynomial.programSize
    MSConvexAcceptancePolynomial.precisionCap MSConvexPolynomialTangentParameters.precisionInv
    MSManuscriptPolynomialQueryParameters.acceptanceRadius
    RealRAM.MSRawOwnerReport.setupCost RealRAM.OwnerSDPSetup.blockBound
    RealRAM.OwnerSDPSetup.objectiveBound RealRAM.OwnerSDPBlocks.sourceBound
    RealRAM.OwnerSDPBlocks.productBound
  ks_poly_cert

theorem acceptance_monotone (P : KSPolynomialConvexSolver.PolynomialSolver) {N M d D : ℕ} (hN : N≤M) (hd : d≤D) :
    MSConvexAcceptancePolynomial.acceptanceCost P N d≤MSConvexAcceptancePolynomial.acceptanceCost P M D := by
  unfold MSConvexAcceptancePolynomial.acceptanceCost RealRAM.MSAcceptanceData.epochCost
    RealRAM.MSConvexAcceptance.queryBudget MSConvexAcceptancePolynomial.programSize
    MSConvexAcceptancePolynomial.precisionCap MSConvexPolynomialTangentParameters.precisionInv
    MSManuscriptPolynomialQueryParameters.acceptanceRadius
    RealRAM.MSRawOwnerReport.setupCost RealRAM.OwnerSDPSetup.blockBound
    RealRAM.OwnerSDPSetup.objectiveBound RealRAM.OwnerSDPBlocks.sourceBound
    RealRAM.OwnerSDPBlocks.productBound
  gcongr

theorem draws_polynomial :
    Represented (fun N d _r=>MSCountedOriginalEpoch.draws N d) := by
  unfold MSCountedOriginalEpoch.draws RealRAM.MSLoopCapSetup.movementCap
    RealRAM.MSLoopCapSetup.movementUniform MSManuscriptPolynomialQueryCurvature.joint
    MSManuscriptPolynomialQueryCurvature.value MSManuscriptPolynomialQueryCurvature.denominator
    MSManuscriptPolynomialQueryCurvature.center
  ks_poly_cert

theorem draws_monotone {N M d D : ℕ} (hN : N≤M) (hd : d≤D) :
    MSCountedOriginalEpoch.draws N d≤MSCountedOriginalEpoch.draws M D := by
  unfold MSCountedOriginalEpoch.draws RealRAM.MSLoopCapSetup.movementCap
    RealRAM.MSLoopCapSetup.movementUniform MSManuscriptPolynomialQueryCurvature.joint
    MSManuscriptPolynomialQueryCurvature.value MSManuscriptPolynomialQueryCurvature.denominator
    MSManuscriptPolynomialQueryCurvature.center
  gcongr

end MatrixSpencer.MSRuntimePolynomialCertificates
