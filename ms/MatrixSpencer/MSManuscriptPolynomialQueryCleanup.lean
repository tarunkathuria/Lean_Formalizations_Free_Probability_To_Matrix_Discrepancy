import MatrixSpencer.MSManuscriptPolynomialQueryParameters
import MatrixSpencer.KSJacobiPolynomialBounds

/-! Polynomial Jacobi cutoff for the literal stored-owner cleanup matrix.
Only the already proved owner floor, frame isometry and covariance upper
bound are used; no entry or eigenvalue magnitude is assumed.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptPolynomialQueryCleanup
open MSManuscriptSupportedOwner MSManuscriptPolynomialQueryParameters
local instance {m : Type*} [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}
set_option maxHeartbeats 1000000

def cleanupJacobi (N : ℕ) : ℕ := KSJacobiPolynomialBounds.jacobi N 1 (cleanupInv N)

theorem stored_entry_le_one {m : ℕ} (O : Owner m)
    (hO : O.Valid (1/8192)) (hO1 : O.physical ≤ 1)
    (i j : Fin O.dim) : |O.matrix i j| ≤ 1 := by
  have hnorm := MSManuscriptComplexSourceNorm.real_coefficient_norm_le_one
    (hO.matrix_posSemidef O (by norm_num))
    (MSManuscriptFrameFamily.stored_matrix_le_one O hO hO1)
  have he := (KSObjectiveValueBound.entry_norm_le (realMatrixEmbedding O.matrix) i j).trans hnorm
  simpa only [realMatrixEmbedding_apply, Complex.norm_real, Real.norm_eq_abs] using he

theorem iterationCount_le {m N : ℕ} (O : Owner m) (hm : O.dim ≤ N)
    (hO : O.Valid (1/8192)) (hO1 : O.physical ≤ 1) :
    KSJacobiIteration.iterationCount O.matrix
      (MSManuscriptCleanupParameters.tolerance O.dim (1/8192)) ≤ cleanupJacobi N :=
  KSJacobiPolynomialBounds.iterationCount_le _ hm (by simpa using stored_entry_le_one O hO hO1)
    (MSManuscriptCleanupParameters.tolerance_pos _ (by norm_num : (0:ℝ)<1/8192)).le
    (cleanupTolerance_inverse_le hm)

/-- Bounds the real argument consumed by the explicit finite ceiling loop. -/
theorem ceiling_input_le {m N : ℕ} (O : Owner m) (hm : O.dim ≤ N)
    (hO : O.Valid (1/8192)) (hO1 : O.physical ≤ 1) :
    KSJacobiIteration.denominator O.dim * KSJacobiStep.offDiagonalEnergy O.matrix /
      (MSManuscriptCleanupParameters.tolerance O.dim (1/8192))^2 ≤ (cleanupJacobi N : ℝ) :=
  KSJacobiPolynomialBounds.ceiling_input_le _ hm (by simpa using stored_entry_le_one O hO hO1)
    (MSManuscriptCleanupParameters.tolerance_pos _ (by norm_num : (0:ℝ)<1/8192)).le
    (cleanupTolerance_inverse_le hm)

end MatrixSpencer.MSManuscriptPolynomialQueryCleanup
