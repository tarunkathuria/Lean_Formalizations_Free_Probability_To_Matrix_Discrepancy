import MatrixSpencer.KSDebitPreparedCurvature
import MatrixSpencer.KSDebitMovement
import MatrixSpencer.KSJacobiRayleigh
import MatrixSpencer.KSInexactIteration
import MatrixSpencer.KSObjectiveCurvature
import MatrixSpencer.KSProjectedContraction

/-!
Numerical-walk components, not a completed KS algorithm theorem.

This checkpoint connects accurate numerical preparation to the actual
state potential's curvature, proves geometric legality and progress of the
full-cube proposal, and constructs the approximate minimum-Rayleigh vector
by a proved finite comparison-and-Jacobi run. The finite value oracle,
uniform Taylor estimates, and final algorithmic success theorem remain open.
-/
