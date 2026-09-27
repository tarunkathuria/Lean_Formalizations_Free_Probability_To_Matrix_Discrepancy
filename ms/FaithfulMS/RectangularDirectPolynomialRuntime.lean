import FaithfulMS.RectangularDirectCountedEpochFactory
import FaithfulMS.RectangularDirectPrograms
import FaithfulMS.RectangularDirectPolynomialAlgorithm

/-! Counted full-walk composition of the direct-density routines.
The intermediate Programs record is instantiated by concrete primal SDP and
matrix arithmetic routines in the final endpoint. Rejected retries, outer
scans, nearest-sign completion and scalar setup are charged. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularDirectPolynomialRuntime
open RectangularDirectPolynomialAlgorithm
open RectangularRidgePhaseProgress (epochCalls)
open RectangularRidgeRetryParameters (retries selected)
open MSCountedSampler (Implementation Bounded)
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgePolynomialRuntimeCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run

def epochBudget (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (N d k : ℕ) : ℕ :=
  RectangularDirectCountedAcceptedEpoch.operations S W N d (retries N d k) + 10

def budget (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (N d k : ℕ) : ℕ :=
  selected N d * (epochBudget S W N d k + 83 * N + 79) +
    (8 * selected N d + 10 * d + N + 309)

def randomDraws (N d k : ℕ) : ℕ :=
  selected N d * RectangularDirectCountedAcceptedEpoch.randomDraws N d (retries N d k)

def implementation (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (hN : 1 ≤ N) (hND : N ≤ d) (k : ℕ) :
    Implementation (output S.service a A hA hAn hN hND k) :=
  MSCountedSampler.overhead
    (RectangularRidgeCountedFull.output (RectangularRidgeTuning.depth N d hN)
      (RectangularRidgePrimitiveParameters.weight N d hN) (1 / (d : ℝ)) 0 A hA hAn
      (RectangularDirectEpochFactory.factory S.service a A hA hAn hN hND (retries N d k))
      (RectangularDirectCountedEpochFactory.implementation S W a A hA hAn hN hND (retries N d k))
      (half_pos (RectangularRidgeUniformResponse.duration_positive hN hND))
      (by norm_num) (by positivity) (epochCalls N d hN)
      (RectangularRidgePhaseProgress.epochCalls_sufficient hN hND) (initial hN))
    ((RectangularRidgePhaseSetup.setup N d).cost + RectangularRidgePhaseSetup.retryExpr.cost + N + 5)

/-- The explicit budget is a fixed composition of dimension polynomials,
the confidence integer and the permitted solver's polynomial cost bound. -/
theorem implementation_bounded (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (hN : 1 ≤ N) (hND : N ≤ d) (k : ℕ) :
    Bounded (implementation S W a A hA hAn hN hND k) (budget S W N d k) (randomDraws N d k) := by
  have he := RectangularRidgeCountedFull.output_bounded (RectangularRidgeTuning.depth N d hN)
    (RectangularRidgePrimitiveParameters.weight N d hN) (1 / (d : ℝ)) 0 A hA hAn
    (RectangularDirectEpochFactory.factory S.service a A hA hAn hN hND (retries N d k))
    (RectangularDirectCountedEpochFactory.implementation S W a A hA hAn hN hND (retries N d k))
    (half_pos (RectangularRidgeUniformResponse.duration_positive hN hND))
    (by norm_num) (by positivity) (epochCalls N d hN)
    (RectangularRidgePhaseProgress.epochCalls_sufficient hN hND) (initial hN)
    (RectangularDirectCountedEpochFactory.implementation_bounded S W a A hA hAn hN hND (retries N d k))
  have hh := MSCountedSampler.overhead_bounded _
    ((RectangularRidgePhaseSetup.setup N d).cost + RectangularRidgePhaseSetup.retryExpr.cost + N + 5) he
  have hb := RectangularRidgeCountedFullBudget.operations_le hN hND (epochBudget S W N d k)
  have hr := RectangularRidgeCountedFullBudget.draws_le hN hND
    (RectangularDirectCountedAcceptedEpoch.randomDraws N d (retries N d k))
  have hs := RectangularRidgePhaseSetup.setup_cost (D := d) hN
  have ht := RectangularRidgePhaseSetup.retryExpr_cost
  intro z out cost draws hx
  have hp := hh z out cost draws hx
  change cost ≤ budget S W N d k ∧ draws ≤ randomDraws N d k
  change cost ≤ RectangularRidgeCountedFull.operations N (epochCalls N d hN) (epochBudget S W N d k) +
    ((RectangularRidgePhaseSetup.setup N d).cost + RectangularRidgePhaseSetup.retryExpr.cost + N + 5) ∧
      draws ≤ (N + 1) * (epochCalls N d hN * RectangularDirectCountedAcceptedEpoch.randomDraws N d (retries N d k)) at hp
  unfold budget randomDraws
  constructor <;> omega

/-- A counted execution exists on every prospective random input and obeys
the same bound, independently of whether that input returns a signing. -/
theorem execution_bounded (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (hN : 1 ≤ N) (hND : N ≤ d) (k : ℕ)
    (z : (output S.service a A hA hAn hN hND k).Draws) :
    ∃ cost draws, (implementation S W a A hA hAn hN hND k).Executes z
      ((output S.service a A hA hAn hN hND k).value z) cost draws ∧
        cost ≤ budget S W N d k ∧ draws ≤ randomDraws N d k :=
  MSCountedSampler.execution_bounded (implementation S W a A hA hAn hN hND k)
    (implementation_bounded S W a A hA hAn hN hND k) z

end MatrixSpencer.RectangularDirectPolynomialRuntime
