import MatrixSpencer.MSCountedSamplingLaw
import MatrixSpencer.MSCountedNumericalFullSigning
import MatrixSpencer.MSCountedEpochFactory

/-! Stochastic refinement of the actual retry, absorbing process, half-phase,
and full-phase combinators. Every proof constructs the indexed stochastic
syntax from the same branches as its counted implementation. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer
open MSManuscriptAdaptive MSCountedSampler
open RealRAM.JacobiIteration (Counted)
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run

namespace MSCountedBoundedProcess
attribute [local instance] Classical.propDecidable
variable {State : Type}

def raw_refinement (P : MSManuscriptBoundedProcess.Config State)
    (test : State → Counted Bool) (htest : ∀ s, (test s).value=decide (P.terminal s))
    (E : ∀ s, Implementation (P.step s))
    (code : ∀ s, Refinement (E s)) (s : State) : Refinement (raw P test htest E s) := by
  unfold raw
  split
  · exact .congr _ (.overhead (.pure (some s) 0) _)
  · exact .congr _ (.overhead (code s) _)

def stage_refinement (P : MSManuscriptBoundedProcess.Config State)
    (test : State → Counted Bool) (htest : ∀ s, (test s).value=decide (P.terminal s))
    (E : ∀ s, Implementation (P.step s)) (code : ∀ s, Refinement (E s)) (k : ℕ)
    (s : MSManuscriptBoundedProcess.Stage P k) : Refinement (stage P test htest E k s) :=
  .certify (raw_refinement P test htest E code s.val) _ _

def run_refinement (P : MSManuscriptBoundedProcess.Config State)
    (test : State → Counted Bool) (htest : ∀ s, (test s).value=decide (P.terminal s))
    (E : ∀ s, Implementation (P.step s)) (code : ∀ s, Refinement (E s)) (K : ℕ) :
    Refinement (run P test htest E K) := by
  unfold run MSManuscriptBoundedProcess.run
  exact .adaptiveRun (stage_refinement P test htest E code) _ K

def output_refinement (P : MSManuscriptBoundedProcess.Config State)
    (test : State → Counted Bool) (htest : ∀ s, (test s).value=decide (P.terminal s))
    (E : ∀ s, Implementation (P.step s)) (code : ∀ s, Refinement (E s)) (K : ℕ) :
    Refinement (output P test htest E K) :=
  .map (run_refinement P test htest E code K) _
end MSCountedBoundedProcess

namespace MSCountedFullProcess
attribute [local instance] Classical.propDecidable
variable {State : Type} {live : State→ℕ} {potential : State→ℝ} {B p : ℝ}
def raw_refinement (F : MSManuscriptFullProcess.Factory live potential B p)
    (test : State → Counted Bool) (htest : ∀x,(test x).value=decide (live x=0))
    (E : ∀x hx,Implementation (F.sample x hx))
    (code : ∀x hx,Refinement (E x hx)) (x : State) : Refinement (raw F test htest E x) := by
  unfold raw
  split
  · exact .congr _ (.overhead (.pure (some x) 0) _)
  · exact .congr _ (.overhead (code x _) _)

def output_refinement (F : MSManuscriptFullProcess.Factory live potential B p)
    (test : State → Counted Bool) (htest : ∀x,(test x).value=decide (live x=0))
    (E : ∀x hx,Implementation (F.sample x hx)) (code : ∀x hx,Refinement (E x hx))
    (hB : 0≤B) (hp : 0≤p) (N : ℕ) (hlive : ∀x,live x≤N) (start : State) :
    Refinement (output F test htest E hB hp N hlive start) :=
  MSCountedBoundedProcess.output_refinement _ _ _ _ (raw_refinement F test htest E code) _
end MSCountedFullProcess

namespace MSCountedHalfPhase
attribute [local instance] Classical.propDecidable
open MSManuscriptPhase MSManuscriptNumericalHalfPhase
open RealRAM.MSPoint (Table)
variable {ι n : Type} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
variable {potential : EuclideanSpace ℝ ι → ℝ} {ε τ B p : ℝ}

def rawStep_refinement (L : Table ι) (F : Factory potential ε τ B p)
    (E : ∀ x hx, Implementation (F.sample x hx)) (code : ∀x hx,Refinement (E x hx))
    (x : Point (ι:=ι) ε) : Refinement (rawStep L F E x) := by
  unfold rawStep
  split
  · exact .congr _ (.overhead (.pure (some x) 0) _)
  · exact .congr _ (.overhead (.map (code x _) _) _)

def terminal_refinement (L : Table ι) (F : Factory potential ε τ B p)
    (E : ∀ x hx, Implementation (F.sample x hx)) (code : ∀x hx,Refinement (E x hx))
    (hτ : 0<τ) (hk : 0<Fintype.card ι) (hB : 0≤B) (hp : 0≤p)
    (start : Point (ι:=ι) ε) (K : ℕ) : Refinement (terminal L F E hτ hk hB hp start K) :=
  MSCountedBoundedProcess.output_refinement _ _ _ _ (rawStep_refinement L F E code) K

def output_refinement (offset : selfAdjoint (Matrix n n ℂ)) (A : ι→Matrix n n ℂ)
    (hA : ∀i,(A i).IsHermitian) (L : Table ι) (F : EpochFactory offset A hA ε p)
    (E : ∀ x hx, Implementation (F.sample x hx)) (code : ∀x hx,Refinement (E x hx))
    (hp : 0≤p) (hk : 0<Fintype.card ι) (start : Point (ι:=ι) ε) :
    Refinement (output offset A hA L F E hp hk start) := by
  unfold output
  exact .congr _ (.map (terminal_refinement L F E code epochTime_pos hk epochCost_nonneg hp start epochCalls) _)
end MSCountedHalfPhase

namespace MSCountedEpochFactory
def addSetup_refinement {α : Type} {S : Sampler α} {E : Implementation S}
    (code : Refinement E) (setup : ℕ) : Refinement (addSetup E setup) :=
  .setup code setup

end MSCountedEpochFactory

namespace MSCountedAcceptedEpoch
variable {m d : ℕ} [Nonempty (Fin d)]
def implementation_refinement (P : KSPolynomialConvexSolver.PolynomialSolver)
    (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d)
    (E : Implementation (trial P cfg hd)) (code : Refinement E) (r : ℕ) :
    Refinement (implementation P cfg hd E r) :=
  .congr _ (.retry code _ r)
end MSCountedAcceptedEpoch

namespace MSCountedEpochFactory
open MSManuscriptPhase PhaseRestriction
variable {ι : Type} [Fintype ι] [LinearOrder ι] {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
def implementation_refinement (P : KSPolynomialConvexSolver.PolynomialSolver)
    (offset : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) (A : ι→Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1) (ε : ℝ) (hε : 0<ε)
    (hsmall : (Fintype.card ι:ℝ)*ε≤1/1000) (hd : 0<d)
    (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val))
    (C : Routines offset A hA hN ε hε hsmall hd x hl)
    (E : Implementation (MSCountedAcceptedEpoch.trial P
      (configuration offset A hA hN ε hε hsmall x hl) hd)) (code : Refinement E) (r : ℕ) :
    Refinement (implementation P offset A hA hN ε hε hsmall hd x hl C E r) :=
  addSetup_refinement (.congr _ (.map
    (MSCountedAcceptedEpoch.implementation_refinement P _ hd E code r) _)) _
end MSCountedEpochFactory

namespace MSCountedNumericalFullSigning
open MSManuscriptPhase PhaseRestriction
open RealRAM.MSPoint (Table)
variable {ι : Type} [Fintype ι] [LinearOrder ι] {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
variable (H : selfAdjoint (Matrix n n ℂ)) (A : ι→Matrix n n ℂ)
  (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1) (ε p : ℝ)
  (P : MSManuscriptNumericalFullSigning.EpochProvider H A hA ε p) (hp : 0≤p)

def sample_refinement (L : Table ι)
    (E : ∀x hx,Implementation (phaseSampler H A hA ε p P hp x hx))
    (code : ∀x hx,Refinement (E x hx)) (setup : Point (ι:=ι) ε → ℕ)
    (x : Point (ι:=ι) ε) (hx : 0<Fintype.card (Live x.val)) :
    Refinement (sample H A hA ε p P hp L E setup x hx) :=
  .congr _ (.overhead (.map (code x hx) _) _)

def output_refinement (L : Table ι)
    (E : ∀x hx,Implementation (phaseSampler H A hA ε p P hp x hx))
    (code : ∀x hx,Refinement (E x hx)) (setup : Point (ι:=ι) ε → ℕ)
    (start : Point (ι:=ι) ε) : Refinement (output H A hA hN ε p P hp L E setup start) :=
  MSCountedFullProcess.output_refinement _ _ _ _
    (sample_refinement H A hA ε p P hp L E code setup) _ _ _ _ _
end MSCountedNumericalFullSigning

end MatrixSpencer
