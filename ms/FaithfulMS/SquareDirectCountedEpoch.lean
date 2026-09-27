import FaithfulMS.SquareDirectCountedCompiledPreparation
import MatrixSpencer.MSCountedEpochMovement

/-! The complete counted local epoch using direct primal-density responses.
The movement is the existing implemented uniform signed projection sampler. -/
noncomputable section
namespace FaithfulMS.SquareDirectCountedEpoch
open MatrixSpencer MSCountedSampler
open MSManuscriptNumericalEpochRun (Config Certified count params)
open MSManuscriptPolynomialQueryCurvature (center)
variable [SquareDirectOracle.Oracle] {m N d : ℕ}
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

variable (c : Config m d) (hm : m ≤ N) (hθ : c.regularizer=1) (hδ : c.floor=1/8192)
  (ht : c.threshold=4096/Real.sqrt (m:ℝ))
  (hR : MSManuscriptEpochInput.centerCap c.offset (N:=m) ≤ center N d)
  (R : ℕ) (E : ∀ s : Certified c, SquareDirectCountedPreparation.Evaluator (params c s.val))
  (hE : ∀ s O, MSManuscriptSupportedPreparation.State (params c s.val) O →
    ((E s).response O).cost ≤ R)

def routines : SquareDirectCountedEpochStep.Routines c :=
  ⟨SquareDirectCountedCompiledPreparation.compute c hm hδ R E hE,
   SquareDirectCountedCompiledPreparation.compute_value c hm hδ R E hE,
   MSCountedEpochMovement.implementation c⟩

def output : Implementation (SquareDirectEpochRun.output c) :=
  SquareDirectCountedEpochStep.output c (routines c hm hδ R E hE)

def stepWork (R N d : ℕ) : ℕ :=
  SquareDirectCountedCompiledPreparation.work R N d +
    200000*(N+1)^5+1000*(N+1)^2+2

include hm hθ hδ ht hR in
theorem output_bounded :
    Bounded (output c hm hδ R E hE)
      ((count c)*stepWork R N d+20*(N+1)^2+3) (count c) := by
  have h := SquareDirectCountedEpochStep.output_bounded c (routines c hm hδ R E hE)
    (SquareDirectCountedCompiledPreparation.work R N d) (200000*(m+1)^5)
    (SquareDirectCountedCompiledPreparation.compute_cost c hm hθ hδ ht hR R E hE)
    (MSCountedEpochMovement.implementation_bounded c)
  intro z out cost draws he
  have hb := h z out cost draws he
  refine ⟨hb.1.trans ?_, hb.2⟩
  unfold stepWork SquareDirectCountedEpochStep.stepBudget
  gcongr

include hm hθ hδ ht hR in
theorem output_with_cap (K : ℕ) (hK : count c ≤ K) :
    Bounded (output c hm hδ R E hE)
      (K*stepWork R N d+20*(N+1)^2+3) K := by
  intro z out cost draws he
  have h := output_bounded c hm hθ hδ ht hR R E hE z out cost draws he
  exact ⟨h.1.trans (by gcongr), h.2.trans hK⟩

end FaithfulMS.SquareDirectCountedEpoch
