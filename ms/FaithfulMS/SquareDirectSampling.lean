import FaithfulMS.SquareDirectSamplingFactory
import FaithfulMS.SquareDirectProcess
import FaithfulMS.SquareDirectRuntime

/-! Compositional probability-law refinement of the full direct-density square
walk through accepted epochs and nested half phases. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.SquareDirectSampling
open MatrixSpencer MSCountedSampler RealRAM PhaseRestriction MSManuscriptPhase
section Original
variable {ι n : Type} [Fintype ι] [LinearOrder ι] [Fintype n] [DecidableEq n] [Nonempty n]
  {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run
variable (P : DirectSDP.PolynomialService)
  (e : Fin d≃n) (hd : 0<d) (A : ι→Matrix n n ℂ)
  (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1)

namespace Phases
open SquareDirectOriginalPhases

def epoch (x : EuclideanSpace ℝ ι) (r : ℕ)
    (y : Point (ι:=Live x) (signingEpsilon ι)) (hy : ¬FiniteHalfPhase.Terminal y.val)
    (C : Routines e hd A hA hN x y (live_large y hy)) :
    Refinement (SquareDirectOriginalPhases.epoch P e hd A hA hN x r y hy C) := by
  letI : SquareDirectOracle.Oracle := ⟨P.service⟩
  exact SquareDirectSamplingFactory.restored (innerH e A hA x) (innerA e A x)
    (innerHermitian e A hA x) (innerContractions e A hN x)
    (signingEpsilon ι) signingEpsilon_pos (margin_small x) hd y (live_large y hy) C r _
    (SquareDirectSamplingLocal.accepted _ hd _
      (SquareDirectSamplingFactory.original P e A hA hN x y (live_large y hy) hd)
      (SquareDirectAcceptanceArithmetic.evaluation P _ hd) r)

def phase (x : Point (ι:=ι) (signingEpsilon ι)) (hx : 0<Fintype.card (Live x.val))
    (L : MSPoint.Table (Live x.val))
    (C : ∀y hy,Routines e hd A hA hN x.val y (live_large y hy)) (r : ℕ) :
    Refinement (SquareDirectOriginalPhases.phase P e hd A hA hN x hx L C r) :=
  MSCountedHalfPhase.output_refinement (restrictedOffset 0 A hA x.val) (restrictedFamily A x.val)
    (restrictedFamily_hermitian A hA x.val) L (factory P e hd A hA hN x.val r)
    (fun y hy => SquareDirectOriginalPhases.epoch P e hd A hA hN x.val r y hy (C y hy))
    (fun y hy => epoch P e hd A hA hN x.val r y hy (C y hy))
    (by change 0≤(301/800:ℝ)^r; positivity) hx ⟨restrictPoint x.val,restrictPoint_regular x.property⟩
end Phases

namespace Process
open SquareDirectProcess
variable (L : MSPoint.Table ι) (hL : MSLabelTable.Ordered L)

def phase (x : Point (ι:=ι) (signingEpsilon ι))
    (hx : 0<Fintype.card (Live x.val)) (r : ℕ) :
    Refinement (SquareDirectProcess.phase P L hL e hd A hA hN x hx r) :=
  Phases.phase P e hd A hA hN x hx
    (MSEpochFactorySetup.liveTable L x.val).value
    (fun y hy => routines L hL e hd A hA hN x.val y (SquareDirectOriginalPhases.live_large y hy)) r

def implementation (r : ℕ) (start : Point (ι:=ι) (signingEpsilon ι)) :
    Refinement (SquareDirectProcess.implementation P L hL e hd A hA hN r start) :=
  MSCountedNumericalFullSigning.output_refinement 0 A hA hN (signingEpsilon ι)
    (MSManuscriptNumericalHalfPhase.epochFailure r) (provider P e hd A hA hN r)
    (by change 0≤(301/800:ℝ)^r; positivity) L
    (fun x hx => SquareDirectProcess.phase P L hL e hd A hA hN x hx r)
    (fun x hx => phase P e hd A hA hN L hL x hx r)
    (fun x => (MSPhaseSetup.setup L e A hA x.val).cost+1) start
end Process
end Original
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
namespace Runtime
variable {N D : ℕ}
local instance : CStarAlgebra (Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ) := {}
variable (P : DirectSDP.PolynomialService)
  (A : Fin N→CMatrix D) (hA : ∀i,(A i).IsHermitian) (hN : ∀i,spectralNorm (A i)≤1)

def point (r : ℕ) (hd : 0<D) :
    Refinement (SquareDirectRuntime.pointImplementation P A hA hN r hd) := by
  letI : NeZero D := ⟨hd.ne'⟩
  letI : Nonempty (Fin (D+D)) := Fin.pos_iff_nonempty.mp (by omega)
  exact Process.implementation P finSumFinEquiv.symm (by omega)
    (fun i=>signedLift (A i)) (fun i=>signedLift_isHermitian (hA i))
    (MSManuscriptNumericalComposition.lifted_contractions A hA hN)
    (MSPoint.finTable N) (MSLabelTable.fin_ordered N) r ⟨0,signing_zero_regular⟩

def implementation (r : ℕ) : Refinement (SquareDirectRuntime.implementation P A hA hN r) := by
  cases D with
  | zero => exact .pure (some (fun _=>1)) (2*N+2)
  | succ d =>
    exact .congr _ (.overhead (.map (point P A hA hN r (by omega))
      SquareDirectOriginalOutput.extract) _)
end Runtime
end FaithfulMS.SquareDirectSampling
