import MatrixSpencer.RectangularRidgeCompiledEpoch
import MatrixSpencer.RectangularRidgeEndpointWork
import MatrixSpencer.MSCountedRetry


noncomputable section
namespace MatrixSpencer.RectangularRidgeCountedAcceptedEpoch
open MSManuscriptAdaptive MSCountedSampler RectangularRidgeEpochInput
variable {N d : ℕ} [Nonempty (Fin d)]
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def output (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) (r : ℕ) :=
  MSManuscriptAcceptanceRetry.output (RectangularRidgeEpochRun.output S.solver a c)
    (RectangularRidgeEpochAcceptanceData.accepts S.solver a c) r

theorem retry_eq (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) (r : ℕ) :
    MSManuscriptAcceptanceRetry.output (RectangularRidgeEpochRun.output S.solver a c)
      (fun s => (RectangularRidgeEndpointWork.accepts S a c s).value) r = output S a c r := by
  have he : (fun s => (RectangularRidgeEndpointWork.accepts S a c s).value) =
      RectangularRidgeEpochAcceptanceData.accepts S.solver a c := by
    funext s
    exact RectangularRidgeEndpointWork.accepts_value S a c s
  rw [he]
  rfl

def implementation (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) (r : ℕ) : Implementation (output S a c r) :=
  congr (retry_eq S a c r)
    (MSCountedRetry.implementation (RectangularRidgeCompiledEpoch.implementation S a c)
      (RectangularRidgeEndpointWork.accepts S a c) r)

def operations (S : RectangularRidgeConvexValue.PolynomialSolver) (N d r : ℕ) : ℕ :=
  r * (RectangularRidgeCompiledEpoch.budget S N d + RectangularRidgeEndpointWork.budget S N d + 3) + 1

def randomDraws (N d r : ℕ) : ℕ := r * (2 ^ 1080 * (d + N + 2) ^ 208 + 1)

/-- All paths, including every rejected trial, obey the same polynomial.
Later prospective draws are not executed after an acceptance. -/
theorem implementation_bounded (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) (r : ℕ) :
    Bounded (implementation S a c r) (operations S N d r) (randomDraws N d r) := by
  apply congr_bounded
  exact MSCountedRetry.implementation_bounded (RectangularRidgeCompiledEpoch.implementation S a c)
    (RectangularRidgeEndpointWork.accepts S a c) (RectangularRidgeCompiledEpoch.implementation_bounded S a c)
    (RectangularRidgeEndpointWork.accepts_cost S a c) r

theorem execution_bounded (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) (r : ℕ) (z : (output S a c r).Draws) :
    ∃ cost draws, (implementation S a c r).Executes z ((output S a c r).value z) cost draws ∧
      cost ≤ operations S N d r ∧ draws ≤ randomDraws N d r :=
  MSCountedSampler.execution_bounded (implementation S a c r) (implementation_bounded S a c r) z

end MatrixSpencer.RectangularRidgeCountedAcceptedEpoch
