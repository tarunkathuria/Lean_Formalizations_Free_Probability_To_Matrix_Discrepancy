import MatrixSpencer.KSRuntimePolynomialRepresentation
import MatrixSpencer.KSFullPolynomialExplicit

noncomputable section
namespace MatrixSpencer.KSFullRuntimePolynomialCertificate
open KSRuntimePolynomialRepresentation
set_option maxRecDepth 16384
set_option maxHeartbeats 3200000
/-- The complete all-dimensional full-cube runtime bound is an actual
multivariate polynomial, with no asymptotic regularity assumption. -/
theorem totalCost_polynomial (P : KSPolynomialConvexSolver.PolynomialSolver) :
    ∃ p : MvPolynomial (Fin 3) ℕ, ∀ N d r,
      MvPolynomial.eval ![N,d,r] p=KSFullPolynomialExplicit.totalCost P N d r := by
  change Represented (KSFullPolynomialExplicit.totalCost P)
  unfold KSFullPolynomialExplicit.totalCost KSFullPolynomialAlgorithmRuntime.totalCost
    KSFullPolynomialAlgorithmRuntime.trialCost KSFullPolynomialWalkRuntime.initialCost
    KSFullPolynomialWalkRuntime.walkCost KSFullPolynomialWalkRuntime.stepCost
    KSFullPolynomialWalkRuntime.acceptanceCost KSFullPolynomialOracleReport.queryCost
    RealRAM.KSNormReport.normCap RealRAM.OwnerSDPSetup.setupCost
    RealRAM.OwnerSDPSetup.blockBound RealRAM.OwnerSDPSetup.objectiveBound
    RealRAM.OwnerSDPBlocks.sourceBound RealRAM.OwnerSDPBlocks.productBound
    KSConvexQueryBudgets.solverWork KSConvexQueryBudgets.programSize
    KSConvexQueryBudgets.valuePrecision KSConvexQueryBudgets.fullValue
    KSConvexQueryBudgets.eighthValue KSConvexQueryBudgets.fullHorizon
    KSJacobiPolynomialBounds.fullJacobi KSJacobiPolynomialBounds.jacobi
    KSJacobiPolynomialBounds.fullEntry KSJacobiPolynomialBounds.fullKappa
    KSJacobiPolynomialBounds.fullQuery KSJacobiPolynomialBounds.eighthQuery
    KSJacobiPolynomialBounds.taylor KSJacobiPolynomialBounds.base
  ks_poly_cert


end MatrixSpencer.KSFullRuntimePolynomialCertificate
