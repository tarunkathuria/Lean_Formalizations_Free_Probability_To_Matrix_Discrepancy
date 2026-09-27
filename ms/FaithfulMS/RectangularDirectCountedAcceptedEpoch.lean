import FaithfulMS.RectangularDirectPrograms
import FaithfulMS.RectangularDirectCompiledEpoch
import FaithfulMS.RectangularDirectEpochAcceptanceData
import MatrixSpencer.MSCountedRetry

/-! Short-circuit retries with the counted direct-density trial and
acceptance routines. Rejected trials are charged; prospective unused inputs
after acceptance do not contribute to the execution cost. -/
noncomputable section
namespace MatrixSpencer.RectangularDirectCountedAcceptedEpoch
open MSManuscriptAdaptive MSCountedSampler RectangularRidgeEpochInput
variable {N d : ℕ} [Nonempty (Fin d)]
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def output (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (c : Config N d) (r : ℕ) :=
  MSManuscriptAcceptanceRetry.output (RectangularDirectEpochRun.output S.service a c)
    (RectangularDirectEpochAcceptanceData.accepts S.service a c) r

theorem retry_eq (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (c : Config N d) (r : ℕ) :
    MSManuscriptAcceptanceRetry.output (RectangularDirectEpochRun.output S.service a c)
      (fun s => (W.accepts a c s).value) r = output S W a c r := by
  have he : (fun s => (W.accepts a c s).value) =
      RectangularDirectEpochAcceptanceData.accepts S.service a c := by
    funext s
    exact W.accepts_value a c s
  rw [he]
  rfl

def implementation (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (c : Config N d) (r : ℕ) : Implementation (output S W a c r) :=
  congr (retry_eq S W a c r)
    (MSCountedRetry.implementation (RectangularDirectCompiledEpoch.implementation S W a c)
      (W.accepts a c) r)

def operations (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (N d r : ℕ) : ℕ :=
  r * (RectangularDirectCompiledEpoch.budget S W N d + W.acceptanceBudget N d + 3) + 1

def randomDraws (N d r : ℕ) : ℕ := r * (2 ^ 1080 * (d + N + 2) ^ 208 + 1)

/-- All paths, including every rejected trial, obey the same polynomial.
Later prospective draws are not executed after an acceptance. -/
theorem implementation_bounded (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (c : Config N d) (r : ℕ) :
    Bounded (implementation S W a c r) (operations S W N d r) (randomDraws N d r) := by
  apply congr_bounded
  exact MSCountedRetry.implementation_bounded (RectangularDirectCompiledEpoch.implementation S W a c)
    (W.accepts a c) (RectangularDirectCompiledEpoch.implementation_bounded S W a c)
    (W.accepts_cost a c) r

theorem execution_bounded (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (c : Config N d) (r : ℕ) (z : (output S W a c r).Draws) :
    ∃ cost draws, (implementation S W a c r).Executes z ((output S W a c r).value z) cost draws ∧
      cost ≤ operations S W N d r ∧ draws ≤ randomDraws N d r :=
  MSCountedSampler.execution_bounded (implementation S W a c r) (implementation_bounded S W a c r) z

end MatrixSpencer.RectangularDirectCountedAcceptedEpoch
