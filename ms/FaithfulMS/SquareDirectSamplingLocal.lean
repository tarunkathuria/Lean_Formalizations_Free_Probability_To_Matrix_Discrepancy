import FaithfulMS.SquareDirectCompiledEpoch
import FaithfulMS.SquareDirectCountedAcceptance
import MatrixSpencer.MSCountedSamplingComposition
import MatrixSpencer.MSCountedUniformEvents

/-! Conditional uniform-input semantics of the direct-density local square
walk and its accepted-epoch retries. Every random leaf is the existing
implemented uniform signed projection sampler. -/
noncomputable section
namespace FaithfulMS.SquareDirectSamplingLocal
open MatrixSpencer MSCountedSampler
open MSManuscriptNumericalEpochRun (Config Certified Stopped)
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 6000
set_option maxHeartbeats 1600000

section Generic
variable [SquareDirectOracle.Oracle] {N d : ℕ}

def next (c : Config N d) (R : SquareDirectCountedEpochStep.Routines c)
    (hR : ∀ s hf hn, Refinement (R.movement s hf hn)) (s : Certified c) :
    Refinement (SquareDirectCountedEpochStep.next c R s) := by
  unfold SquareDirectCountedEpochStep.next
  split_ifs with hs hp
  · exact .congr _ (.overhead (.pure s 0) _)
  · exact .congr _ (.overhead (.pure _ 0) _)
  · exact .congr _ (.overhead (hR _ _ _) _)

def run (c : Config N d) (R : SquareDirectCountedEpochStep.Routines c)
    (hR : ∀ s hf hn, Refinement (R.movement s hf hn)) (k : ℕ) (s : Certified c) :
    Refinement (SquareDirectCountedEpochStep.run c R k s) :=
  .congr _ (.iterate (next c R hR) k s)

def output (c : Config N d) (R : SquareDirectCountedEpochStep.Routines c)
    (hR : ∀ s hf hn, Refinement (R.movement s hf hn)) :
    Refinement (SquareDirectCountedEpochStep.output c R) :=
  .overhead (run c R hR _ _) _

end Generic

def compiled (P : DirectSDP.PolynomialService) {m N d : ℕ}
    (c : Config m d) (hm : m ≤ N) (hδ : c.floor=1/8192) :
    Refinement (SquareDirectCompiledEpoch.output P c hm hδ) := by
  letI : SquareDirectOracle.Oracle := ⟨P.service⟩
  exact output c _ (fun s hf hn => .uniformMovement c s hf hn)

section Acceptance
variable [SquareDirectOracle.Oracle] {m d : ℕ} [Nonempty (Fin d)]
def accepted (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d)
    (E : Implementation (SquareDirectCountedAcceptance.Trial cfg hd))
    (code : Refinement E) (A : SquareDirectCountedAcceptance.Evaluation cfg hd) (r : ℕ) :
    Refinement (SquareDirectCountedAcceptance.implementation cfg hd E A r) :=
  .congr _ (.retry code A.compute r)
end Acceptance
end FaithfulMS.SquareDirectSamplingLocal
