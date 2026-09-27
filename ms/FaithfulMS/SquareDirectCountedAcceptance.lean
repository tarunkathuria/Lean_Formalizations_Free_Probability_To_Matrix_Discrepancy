import FaithfulMS.SquareDirectAcceptedEpoch
import MatrixSpencer.MSCountedRetry

/-! Sequential first-accepted retries of the actual direct-density epoch.
The local evaluation record is instantiated by the scalar/SDP compiler; it
supplies no success or walk premise. Each executed rejected trial is charged. -/
open Matrix
noncomputable section
namespace FaithfulMS.SquareDirectCountedAcceptance
open MatrixSpencer MSManuscriptAdaptive MSCountedSampler MSManuscriptNumericalConfig
open RealRAM.JacobiIteration (Counted)
variable [SquareDirectOracle.Oracle]
variable {m d : ℕ} [Nonempty (Fin d)]
set_option maxHeartbeats 1400000
set_option maxRecDepth 4000

abbrev Trial (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d) :=
  SquareDirectEpochRun.output (ofEpochConfig cfg hd)

structure Evaluation (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d) where
  compute : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd) → Counted Bool
  correct : ∀ s, (compute s).value = SquareDirectAcceptedEpoch.accepts cfg hd s

theorem retry_eq (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d)
    (A : Evaluation cfg hd) (r : ℕ) :
    MSManuscriptAcceptanceRetry.output (Trial cfg hd) (fun s => (A.compute s).value) r =
      SquareDirectAcceptedEpoch.output cfg hd r := by
  rw [show (fun s => (A.compute s).value) = SquareDirectAcceptedEpoch.accepts cfg hd
    from funext A.correct]
  rfl

def implementation (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d)
    (E : Implementation (Trial cfg hd)) (A : Evaluation cfg hd) (r : ℕ) :
    Implementation (SquareDirectAcceptedEpoch.output cfg hd r) :=
  MSCountedSampler.congr (retry_eq cfg hd A r)
    (MSCountedRetry.implementation E A.compute r)

theorem implementation_bounded (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d)
    (E : Implementation (Trial cfg hd)) (A : Evaluation cfg hd)
    {B R C : ℕ} (hE : Bounded E B R) (hA : ∀ s, (A.compute s).cost ≤ C) (r : ℕ) :
    Bounded (implementation cfg hd E A r) (r*(B+C+3)+1) (r*R) := by
  apply MSCountedSampler.congr_bounded
  exact MSCountedRetry.implementation_bounded E A.compute hE hA r

theorem execution_bounded (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d)
    (E : Implementation (Trial cfg hd)) (A : Evaluation cfg hd)
    {B R C : ℕ} (hE : Bounded E B R) (hA : ∀ s, (A.compute s).cost ≤ C) (r : ℕ)
    (z : (SquareDirectAcceptedEpoch.output cfg hd r).Draws) :
    ∃ cost draws, (implementation cfg hd E A r).Executes z
      ((SquareDirectAcceptedEpoch.output cfg hd r).value z) cost draws ∧
      cost ≤ r*(B+C+3)+1 ∧ draws ≤ r*R :=
  MSCountedSampler.execution_bounded _ (implementation_bounded cfg hd E A hE hA r) z

theorem executed_sound (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d)
    (E : Implementation (Trial cfg hd)) (A : Evaluation cfg hd) (r : ℕ)
    (z : (SquareDirectAcceptedEpoch.output cfg hd r).Draws)
    (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) (cost draws : ℕ)
    (he : (implementation cfg hd E A r).Executes z (some s) cost draws) :
    MSManuscriptAcceptedEpoch.GoodEndpoint cfg hd s :=
  SquareDirectAcceptedEpoch.output_sound cfg hd r z s
    ((implementation cfg hd E A r).result z (some s) cost draws he).symm

end FaithfulMS.SquareDirectCountedAcceptance
