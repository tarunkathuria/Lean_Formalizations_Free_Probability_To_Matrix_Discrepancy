import MatrixSpencer.MSCountedSamplingLaw
import MatrixSpencer.MSCountedUniformEvents
import MatrixSpencer.MSCountedCompiledEpoch
import MatrixSpencer.MSCountedOriginalOutput


noncomputable section
namespace MatrixSpencer.MSCountedNumericalSampling
open MSCountedSampler
open MSManuscriptNumericalEpochRun (Config Certified Stopped)
open RealRAM
variable {m N d D : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

def movement (c : Config N d) (s : Certified c)
    (hf : s.val.owner.Valid (2*c.floor)) (hn : ¬Stopped c s.val) :
    Refinement (MSCountedEpochMovement.implementation c s hf hn) :=
  .uniformMovement c s hf hn

section Generic
variable [MSConvexOwnerValue.Oracle]

def next (c : Config N d) (R : MSCountedEpochStep.Routines c)
    (hR : ∀s hf hn,Refinement (R.movement s hf hn)) (s : Certified c) :
    Refinement (MSCountedEpochStep.next c R s) := by
  unfold MSCountedEpochStep.next
  split_ifs with hs hp
  · exact .congr _ (.overhead (.pure s 0) _)
  · exact .congr _ (.overhead (.pure (MSConvexNumericalEpochRun.prepare c s) 0) _)
  · exact .congr _ (.overhead (hR _ _ _) _)

def run (c : Config N d) (R : MSCountedEpochStep.Routines c)
    (hR : ∀s hf hn,Refinement (R.movement s hf hn)) (k : ℕ) (s : Certified c) :
    Refinement (MSCountedEpochStep.run c R k s) :=
  .congr (MSCountedEpochStep.iterate_eq c k s) (Refinement.iterate (next c R hR) k s)

def output (c : Config N d) (R : MSCountedEpochStep.Routines c)
    (hR : ∀s hf hn,Refinement (R.movement s hf hn)) :
    Refinement (MSCountedEpochStep.output c R) :=
  .overhead (run c R hR (MSManuscriptNumericalEpochRun.count c)
    (MSManuscriptNumericalEpochRun.initial c)) _

end Generic

def compiled (S : KSPolynomialConvexSolver.PolynomialSolver)
    (c : Config m d) (hm : m ≤ N) (hθ : c.regularizer=1) (hδ : c.floor=1/8192)
    (ht : c.threshold=4096/Real.sqrt (m:ℝ))
    (hR : MSManuscriptEpochInput.centerCap c.offset (N:=m) ≤
      MSManuscriptPolynomialQueryCurvature.center N d) :
    Refinement (MSCountedCompiledEpoch.output S c hm hθ hδ ht hR) := by
  letI:=MSRawOwnerReport.oracle S
  exact output c (MSCountedCompiledEpoch.routines S c hm hθ hδ ht hR) (movement c)

def positive (P : KSPolynomialConvexSolver.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i) ≤ 1) (r : ℕ) (hd : 0<D)
    (E : Implementation (MSCountedOriginalOutput.pointSampler P A hA hN r hd))
    (code : Refinement E) : Refinement (MSCountedOriginalOutput.positive P A hA hN r hd E) :=
  .congr (MSCountedOriginalOutput.map_eq P A hA hN r hd)
    (.overhead (.map code MSCountedOriginalOutput.extract) _)

def original (P : KSPolynomialConvexSolver.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i) ≤ 1) (r : ℕ)
    (E : ∀hd : 0<D,Implementation (MSCountedOriginalOutput.pointSampler P A hA hN r hd))
    (code : ∀hd,Refinement (E hd)) :
    Refinement (MSCountedOriginalOutput.implementation P A hA hN r E) := by
  cases D with
  | zero=>exact .pure (some (fun _=>1)) (2*N+2)
  | succ d=>exact positive P A hA hN r _ _ (code _)

end MatrixSpencer.MSCountedNumericalSampling
