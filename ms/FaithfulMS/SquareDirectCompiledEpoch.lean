import FaithfulMS.SquareDirectCountedEpoch
import FaithfulMS.SquareDirectCountedResponse

/-! Concrete local epoch compiler. No report implementation or local cost
premise remains: both are supplied by the primal-density SDP and transport
programs. The outer dimension bounds only discharge scalar tuning budgets. -/
noncomputable section
namespace FaithfulMS.SquareDirectCompiledEpoch
open MatrixSpencer MSCountedSampler
open MSManuscriptNumericalEpochRun (Config Certified count params)
open MSManuscriptPolynomialQueryCurvature (center)
variable {m N d : ℕ}
set_option maxHeartbeats 1800000
set_option maxRecDepth 6000
variable (P : DirectSDP.PolynomialService) (c : Config m d) (hm : m ≤ N)
  (hθ : c.regularizer=1) (hδ : c.floor=1/8192)
  (ht : c.threshold=4096/Real.sqrt (m:ℝ))
  (hR : MSManuscriptEpochInput.centerCap c.offset (N:=m) ≤ center N d)

def output : Implementation (@SquareDirectEpochRun.output ⟨P.service⟩ m d c) := by
  letI : SquareDirectOracle.Oracle := ⟨P.service⟩
  exact SquareDirectCountedEpoch.output c hm hδ (SquareDirectCountedResponse.work P N d)
    (fun s => SquareDirectCountedResponse.evaluator P (params c s.val))
    (fun s O hO => (SquareDirectCountedResponse.evaluator_cost P (params c s.val) O hO).trans
      (SquareDirectCountedResponse.work_mono P hm))

def stepWork (P : DirectSDP.PolynomialService) (N d : ℕ) : ℕ :=
  SquareDirectCountedEpoch.stepWork (SquareDirectCountedResponse.work P N d) N d

include hθ ht hR in
theorem output_bounded : Bounded (output P c hm hδ)
    ((count c)*stepWork P N d+20*(N+1)^2+3) (count c) := by
  letI : SquareDirectOracle.Oracle := ⟨P.service⟩
  exact SquareDirectCountedEpoch.output_bounded c hm hθ hδ ht hR
    (SquareDirectCountedResponse.work P N d)
    (fun s => SquareDirectCountedResponse.evaluator P (params c s.val))
    (fun s O hO => (SquareDirectCountedResponse.evaluator_cost P (params c s.val) O hO).trans
      (SquareDirectCountedResponse.work_mono P hm))

include hθ ht hR in
theorem output_with_cap (K : ℕ) (hK : count c ≤ K) : Bounded (output P c hm hδ)
    (K*stepWork P N d+20*(N+1)^2+3) K := by
  letI : SquareDirectOracle.Oracle := ⟨P.service⟩
  exact SquareDirectCountedEpoch.output_with_cap c hm hθ hδ ht hR
    (SquareDirectCountedResponse.work P N d)
    (fun s => SquareDirectCountedResponse.evaluator P (params c s.val))
    (fun s O hO => (SquareDirectCountedResponse.evaluator_cost P (params c s.val) O hO).trans
      (SquareDirectCountedResponse.work_mono P hm)) K hK

end FaithfulMS.SquareDirectCompiledEpoch
