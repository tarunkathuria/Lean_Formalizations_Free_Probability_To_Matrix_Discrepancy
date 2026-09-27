import MatrixSpencer.MSCountedNumericalSampling
import MatrixSpencer.MSCountedSamplingComposition
import MatrixSpencer.MSCountedOriginalPhases

/-! Closed stochastic-code derivations at the original nested matrix input.
No law or accuracy hypothesis is supplied by the caller. Every random leaf
is the counted uniform movement, and every outer constructor is the actual
adaptive walk/retry/phase code. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer
open MSCountedSampler RealRAM PhaseRestriction MSManuscriptPhase
variable {ι n : Type} [Fintype ι] [LinearOrder ι] [Fintype n] [DecidableEq n]
  {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run

namespace MSCountedOriginalEpoch
def compiled_refinement (P : KSPolynomialConvexSolver.PolynomialSolver)
    (e : Fin d≃n) (A : ι→Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1)
    (x : EuclideanSpace ℝ ι) (y : Point (ι:=Live x) (signingEpsilon ι))
    (hl : 32≤Fintype.card (Live y.val)) (hd : 0<d) :
    Refinement (compiled P e A hA hN x y hl hd) :=
  MSCountedNumericalSampling.compiled P (config e A hA hN x y hl hd)
    (MSManuscriptFactoryPolynomialMovementBounds.live_le_original x y)
    rfl rfl rfl (center_le e A hA hN x y hl hd)

def implementation_refinement (P : KSPolynomialConvexSolver.PolynomialSolver)
    (e : Fin d≃n) (A : ι→Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1)
    (x : EuclideanSpace ℝ ι) (y : Point (ι:=Live x) (signingEpsilon ι))
    (hl : 32≤Fintype.card (Live y.val)) (hd : 0<d) :
    Refinement (implementation P e A hA hN x y hl hd) :=
  .setup (compiled_refinement P e A hA hN x y hl hd) _
end MSCountedOriginalEpoch

namespace MSCountedOriginalPhases
variable [Nonempty n]
variable (P : KSPolynomialConvexSolver.PolynomialSolver)
  (e : Fin d≃n) (hd : 0<d) (A : ι→Matrix n n ℂ)
  (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1)

def epoch_refinement (x : EuclideanSpace ℝ ι) (r : ℕ)
    (y : Point (ι:=Live x) (signingEpsilon ι)) (hy : ¬FiniteHalfPhase.Terminal y.val)
    (C : Routines e hd A hA hN x y (live_large y hy)) :
    Refinement (epoch P e hd A hA hN x r y hy C) :=
  MSCountedEpochFactory.implementation_refinement P (innerH e A hA x)
    (innerA e A x) (innerHermitian e A hA x) (innerContractions e A hN x)
    (signingEpsilon ι) signingEpsilon_pos (margin_small x) hd y (live_large y hy) C
    (MSCountedOriginalEpoch.implementation P e A hA hN x y (live_large y hy) hd)
    (MSCountedOriginalEpoch.implementation_refinement P e A hA hN x y (live_large y hy) hd) r

def phase_refinement (x : Point (ι:=ι) (signingEpsilon ι)) (hx : 0<Fintype.card (Live x.val))
    (L : MSPoint.Table (Live x.val))
    (C : ∀y hy,Routines e hd A hA hN x.val y (live_large y hy)) (r : ℕ) :
    Refinement (phase P e hd A hA hN x hx L C r) :=
  MSCountedHalfPhase.output_refinement (restrictedOffset 0 A hA x.val) (restrictedFamily A x.val)
    (restrictedFamily_hermitian A hA x.val) L (factory P e hd A hA hN x.val r)
    (fun y hy => epoch P e hd A hA hN x.val r y hy (C y hy))
    (fun y hy => epoch_refinement P e hd A hA hN x.val r y hy (C y hy))
    (by change 0≤(301/800:ℝ)^r; positivity) hx ⟨restrictPoint x.val,restrictPoint_regular x.property⟩
end MSCountedOriginalPhases

end MatrixSpencer
