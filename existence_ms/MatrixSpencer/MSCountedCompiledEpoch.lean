import MatrixSpencer.MSCountedCompiledPreparation
import MatrixSpencer.MSCountedEpochMovement
import MatrixSpencer.RealRAMMSFixedScalarChecks
import MatrixSpencer.RealRAMMSLedgerChecks

/-! Concrete numerical step and epoch implementation: compiled convex response,
finite Jacobi/Schur preparation, explicit LDL categorical draw, sticky movement,
and all state updates. The independent epoch scalar/counter setup is charged
by the original-input wrapper. -/
noncomputable section
namespace MatrixSpencer.MSCountedCompiledEpoch
open RealRAM
open MSCountedSampler
open MSManuscriptNumericalEpochRun (Config Certified count)
open MSManuscriptPolynomialQueryCurvature (center)
variable {m N d : ℕ}
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

variable (S : KSPolynomialConvexSolver.PolynomialSolver)
  (c : Config m d) (hm : m ≤ N) (hθ : c.regularizer=1) (hδ : c.floor=1/8192)
  (ht : c.threshold=4096/Real.sqrt (m:ℝ))
  (hR : MSManuscriptEpochInput.centerCap c.offset (N:=m) ≤ center N d)

def routines : @MSCountedEpochStep.Routines (MSRawOwnerReport.oracle S) m d c := by
  letI:=MSRawOwnerReport.oracle S
  exact ⟨MSCountedCompiledPreparation.compute S c hm hθ hδ ht hR,
    MSCountedCompiledPreparation.compute_value S c hm hθ hδ ht hR,
    MSCountedEpochMovement.implementation c⟩

def output : Implementation
    (@MSConvexNumericalEpochRun.output (MSRawOwnerReport.oracle S) m d c) := by
  letI:=MSRawOwnerReport.oracle S
  exact MSCountedEpochStep.output c (routines S c hm hθ hδ ht hR)

def stepWork (S : KSPolynomialConvexSolver.PolynomialSolver) (N d : ℕ) : ℕ :=
  MSCountedCompiledPreparation.work S N d+200000*(N+1)^5+1000*(N+1)^2+2

include hm hθ hδ ht hR in
theorem output_bounded :
    Bounded (output S c hm hθ hδ ht hR)
      ((count c)*stepWork S N d+20*(N+1)^2+3) (count c) := by
  letI:=MSRawOwnerReport.oracle S
  have h:=MSCountedEpochStep.output_bounded c (routines S c hm hθ hδ ht hR)
    (MSCountedCompiledPreparation.work S N d) (200000*(m+1)^5)
    (MSCountedCompiledPreparation.compute_cost S c hm hθ hδ ht hR)
    (MSCountedEpochMovement.implementation_bounded c)
  intro z out cost draws he
  have hb:=h z out cost draws he
  refine ⟨hb.1.trans ?_,hb.2⟩
  unfold stepWork MSCountedEpochStep.stepBudget
  gcongr

include hm hθ hδ ht hR in
theorem output_with_cap (K : ℕ) (hK : count c ≤ K) :
    Bounded (output S c hm hθ hδ ht hR)
      (K*stepWork S N d+20*(N+1)^2+3) K := by
  intro z out cost draws he
  have h:=output_bounded S c hm hθ hδ ht hR z out cost draws he
  exact ⟨h.1.trans (by gcongr),h.2.trans hK⟩

end MatrixSpencer.MSCountedCompiledEpoch
