import MatrixSpencer.KSRuntimePolynomialRepresentation
import MatrixSpencer.KSEighthPolynomialExplicit

noncomputable section
namespace MatrixSpencer.KSEighthRuntimePolynomialCertificate
open KSRuntimePolynomialRepresentation
set_option maxRecDepth 16384
set_option maxHeartbeats 3200000

/-- The complete all-dimensional eighth-cube runtime bound is an actual
multivariate polynomial, with the solver coefficient and degree fixed. -/
theorem totalCost_polynomial (P : KSPolynomialConvexSolver.PolynomialSolver) :
    ∃ p : MvPolynomial (Fin 3) ℕ, ∀ N d r,
      MvPolynomial.eval ![N,d,r] p=KSEighthPolynomialExplicit.totalCost P N d r := by
  change Represented (KSEighthPolynomialExplicit.totalCost P)
  unfold KSEighthPolynomialExplicit.totalCost KSEighthPolynomialRuntime.totalBudget
    KSEighthPolynomialRuntime.setupBudget KSEighthPolynomialRuntime.walkBudget
    KSEighthCompiledRun.initialBudget KSEighthCompiledQueries.queryCost
    KSEighthOwnerInputSetup.costBudget KSEighthConvexRuntime.pathBudget
    KSEighthConvexRuntime.covarianceBudget KSEighthCountedCovariance.costBudget
    KSEighthCountedRun.childBudget KSEighthCountedMovement.costBudget
    RealRAM.OwnerSDPSetup.setupCost RealRAM.OwnerSDPSetup.blockBound
    RealRAM.OwnerSDPSetup.objectiveBound RealRAM.OwnerSDPBlocks.sourceBound
    RealRAM.OwnerSDPBlocks.productBound KSConvexQueryBudgets.solverWork
    KSConvexQueryBudgets.programSize KSConvexQueryBudgets.valuePrecision
    KSConvexQueryBudgets.fullValue KSConvexQueryBudgets.eighthValue
    KSConvexQueryBudgets.eighthHorizon KSJacobiPolynomialBounds.eighthJacobi
    KSJacobiPolynomialBounds.jacobi KSJacobiPolynomialBounds.eighthScaledEntry
    KSJacobiPolynomialBounds.eighthEntry KSJacobiPolynomialBounds.eighthBeta
    KSJacobiPolynomialBounds.fullQuery KSJacobiPolynomialBounds.eighthQuery
    KSJacobiPolynomialBounds.taylor KSJacobiPolynomialBounds.base
  ks_poly_cert

end MatrixSpencer.KSEighthRuntimePolynomialCertificate
