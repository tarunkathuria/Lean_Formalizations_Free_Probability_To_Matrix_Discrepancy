import FaithfulMS.RectangularSampling
import MatrixSpencer.RectangularRidgeOriginalAlgorithm

/-! Stochastic refinement is propagated through the literal rectangular
preparation/movement branches, accepted-epoch retries, retained live labels,
half phases, full signing, and original-input preprocessing. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.RectangularSampling
open MatrixSpencer MSManuscriptAdaptive MSCountedSampler
open RealRAM.JacobiIteration (Counted)
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run
namespace BoundedProcess
open MSCountedBoundedProcess
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
  unfold MSCountedBoundedProcess.run MSManuscriptBoundedProcess.run
  exact .adaptiveRun (stage_refinement P test htest E code) _ K

def output_refinement (P : MSManuscriptBoundedProcess.Config State)
    (test : State → Counted Bool) (htest : ∀ s, (test s).value=decide (P.terminal s))
    (E : ∀ s, Implementation (P.step s)) (code : ∀ s, Refinement (E s)) (K : ℕ) :
    Refinement (output P test htest E K) :=
  .map (run_refinement P test htest E code K) _
end BoundedProcess

namespace FullProcess
open MSCountedFullProcess
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
  BoundedProcess.output_refinement _ _ _ _ (raw_refinement F test htest E code) _
end FullProcess



namespace EpochWork
open RectangularRidgeEpochInput RectangularRidgeEpochRun RectangularRidgeEpochWork
variable {N d : ℕ} [Nonempty (Fin d)]
attribute [local instance] Classical.propDecidable

def next_refinement (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (R : Routines solver a c)
    (code : ∀ s hfloor hnt, Refinement (R.movement s hfloor hnt)) (s : Certified c) :
    Refinement (next solver a c R s) := by
  unfold RectangularRidgeEpochWork.next
  split
  · exact .congr _ (.overhead (.pure s 0) _)
  · split
    · exact .congr _ (.overhead (.pure _ 0) _)
    · exact .congr _ (.overhead (code _ _ _) _)

def run_refinement (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (R : Routines solver a c)
    (code : ∀ s hfloor hnt, Refinement (R.movement s hfloor hnt))
    (k : ℕ) (s : Certified c) : Refinement (RectangularRidgeEpochWork.run solver a c R k s) :=
  .congr _ (.iterate (next_refinement solver a c R code) k s)

def output_refinement (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (R : Routines solver a c)
    (code : ∀ s hfloor hnt, Refinement (R.movement s hfloor hnt)) :
    Refinement (RectangularRidgeEpochWork.output solver a c R) :=
  .overhead (run_refinement solver a c R code _ _) _
end EpochWork

namespace CompiledEpoch
open RectangularRidgeEpochInput RectangularRidgeCompiledEpoch
variable {N d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}

def implementation_refinement (S : RectangularRidgeConvexValue.PolynomialSolver)
    (a : Fin d) (c : Config N d) : Refinement (implementation S a c) :=
  .overhead (EpochWork.output_refinement S.solver a c (routines S a c)
    (fun s hfloor hnt => .uniformMovement c s hfloor hnt)) _
end CompiledEpoch

namespace AcceptedEpoch
open RectangularRidgeEpochInput RectangularRidgeCountedAcceptedEpoch
variable {N d : ℕ} [Nonempty (Fin d)]

def implementation_refinement (S : RectangularRidgeConvexValue.PolynomialSolver)
    (a : Fin d) (c : Config N d) (r : ℕ) : Refinement (implementation S a c r) :=
  .congr _ (.retry (CompiledEpoch.implementation_refinement S a c) _ r)
end AcceptedEpoch

namespace EpochFactory
open RectangularRidgeEpochInput RectangularRidgeCountedEpochFactory
variable {N d : ℕ} [Nonempty (Fin d)]

def sample_refinement (S : RectangularRidgeConvexValue.PolynomialSolver)
    (a : Fin d) (c : Config N d) (r : ℕ) : Refinement (sample S a c r) :=
  .congr _ (.map (AcceptedEpoch.implementation_refinement S a c r) _)

def implementation_refinement (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (hN : 1 ≤ N) (hND : N ≤ d) (r : ℕ)
    (x : RectangularRidgePhaseAssembly.Point (N := N) (margin N))
    (hx : 32 ≤ RectangularRidgeRemainingPotential.liveCount x.val) :
    Refinement (implementation S a A hA hAn hN hND r x hx) :=
  .overhead (sample_refinement S a _ r) _
end EpochFactory

namespace Phase
open RectangularRidgePhaseAssembly RectangularRidgeCountedPhase
open RectangularRidgeRemainingPotential
variable {N : ℕ} {f : EuclideanSpace ℝ (Fin N) → ℝ} {ε τ K p : ℝ}
attribute [local instance] Classical.propDecidable

def raw_refinement (F : EpochFactory f ε τ K p)
    (E : ∀ x hx, Implementation (F.sample x hx)) (code : ∀ x hx, Refinement (E x hx))
    (start : Point (N := N) ε) (x : PhasePoint start) : Refinement (raw F E start x) := by
  unfold raw
  split
  · exact .congr _ (.overhead (.pure (some x) 0) _)
  · exact .congr _ (.overhead (.retain F start x _ (code _ _)) _)

def output_refinement (F : EpochFactory f ε τ K p)
    (E : ∀ x hx, Implementation (F.sample x hx)) (code : ∀ x hx, Refinement (E x hx))
    (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p) (start : Point (N := N) ε)
    (hs : 0 < liveCount start.val) (calls : ℕ) :
    Refinement (RectangularRidgeCountedPhase.output F E hτ hK hp start hs calls) :=
  BoundedProcess.output_refinement _ _ _ _ (raw_refinement F E code start) calls
end Phase

namespace Full
open RectangularRidgeCountedFull RectangularRidgeFullAssembly RectangularRidgePhaseAssembly
open RectangularRidgeRemainingPotential
variable {N : ℕ} {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
variable (m : ℕ) (θ κ : ℝ) (offset : selfAdjoint (Matrix n n ℂ))
  (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hAn : ∀ i, ‖A i‖ ≤ 1)
  {ε τ K p : ℝ}

def phase_refinement (F : Input m θ κ offset A hA (ε := ε) (τ := τ) (K := K) (p := p))
    (E : ∀ x hx, Implementation (F.sample x hx)) (code : ∀ x hx, Refinement (E x hx))
    (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p) (start : Point (N := N) ε)
    (hs : 0 < liveCount start.val) (calls : ℕ) :
    Refinement (phase m θ κ offset A hA F E hτ hK hp start hs calls) :=
  .congr _ (.map (Phase.output_refinement F E code hτ hK hp start hs calls) _)

def output_refinement (F : Input m θ κ offset A hA (ε := ε) (τ := τ) (K := K) (p := p))
    (E : ∀ x hx, Implementation (F.sample x hx)) (code : ∀ x hx, Refinement (E x hx))
    (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p) (calls : ℕ)
    (hcalls : 32 / τ + 128 < (calls : ℝ)) (start : Point (N := N) ε) :
    Refinement (RectangularRidgeCountedFull.output m θ κ offset A hA hAn F E hτ hK hp calls hcalls start) :=
  FullProcess.output_refinement _ _ _ _
    (fun x hx => phase_refinement m θ κ offset A hA F E code hτ hK hp x hx calls) _ _ _ _ _
end Full

namespace PolynomialRuntime
open RectangularRidgePolynomialRuntime RectangularRidgePolynomialAlgorithm
open RectangularRidgeRetryParameters (retries)
variable {N d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}

def implementation_refinement (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (hN : 1 ≤ N) (hND : N ≤ d) (k : ℕ) :
    Refinement (implementation S a A hA hAn hN hND k) :=
  .overhead (Full.output_refinement _ _ _ _ _ _ _ _ _
    (EpochFactory.implementation_refinement S a A hA hAn hN hND (retries N d k)) _ _ _ _ _ _) _
end PolynomialRuntime

namespace OriginalAlgorithm
open RectangularRidgeOriginalAlgorithm RectangularRidgeFlatSigning
variable {N D : ℕ}

def implementation_refinement (hN : 1 ≤ N) (hND : N ≤ D)
    (S : RectangularRidgeConvexValue.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, spectralNorm (A i) ≤ 1) (k : ℕ) :
    Refinement (implementation hN hND S A hA hAn k) := by
  letI : NeZero D := ⟨by omega⟩
  letI : NeZero (D + D) := ⟨by omega⟩
  exact .overhead (PolynomialRuntime.implementation_refinement S ⟨0, by omega⟩
    (flat A) (flat_hermitian A hA) (flat_contraction A hA hAn) hN (by omega) k) _
end OriginalAlgorithm
end FaithfulMS.RectangularSampling
