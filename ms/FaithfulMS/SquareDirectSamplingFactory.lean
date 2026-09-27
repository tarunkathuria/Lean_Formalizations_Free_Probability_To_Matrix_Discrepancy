import FaithfulMS.SquareDirectSamplingLocal
import FaithfulMS.SquareDirectOriginalEpoch

/-! Refinement through setup and restoration of the original live labels. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.SquareDirectSamplingFactory
open MatrixSpencer MSCountedSampler MSManuscriptAdaptive
open MSManuscriptPhase PhaseRestriction
set_option maxRecDepth 8000
set_option maxHeartbeats 1600000

section Factory
variable [SquareDirectOracle.Oracle]
variable {ι : Type} [Fintype ι] [LinearOrder ι] {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
variable (offset : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) (A : ι→Matrix (Fin d) (Fin d) ℂ)
  (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1) (ε : ℝ) (hε : 0<ε)
  (hsmall : (Fintype.card ι:ℝ)*ε≤1/1000) (hd : 0<d)

def restored (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val))
    (C : SquareDirectCountedFactory.Routines offset A hA hN ε hε hsmall hd x hl) (r : ℕ)
    (E : Implementation (SquareDirectAcceptedEpoch.output
      (SquareDirectCountedFactory.configuration offset A hA hN ε hε hsmall x hl) hd r))
    (code : Refinement E) :
    Refinement (SquareDirectCountedFactory.implementation offset A hA hN ε hε hsmall hd x hl C r E) :=
  .setup (.congr _ (.map code _)) _
end Factory

section Original
variable {ι n : Type} [Fintype ι] [LinearOrder ι] [Fintype n] [DecidableEq n]
  {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
variable (P : DirectSDP.PolynomialService)
  (e : Fin d≃n) (A : ι→Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1)
  (x : EuclideanSpace ℝ ι) (y : Point (ι:=Live x) (signingEpsilon ι))
  (hl : 32≤Fintype.card (Live y.val)) (hd : 0<d)

def original_compiled : Refinement (SquareDirectOriginalEpoch.compiled P e A hA hN x y hl hd) :=
  SquareDirectSamplingLocal.compiled P (SquareDirectOriginalEpoch.config e A hA hN x y hl hd)
    (MSManuscriptFactoryPolynomialMovementBounds.live_le_original x y) rfl

def original : Refinement (SquareDirectOriginalEpoch.implementation P e A hA hN x y hl hd) :=
  .setup (original_compiled P e A hA hN x y hl hd) _
end Original
end FaithfulMS.SquareDirectSamplingFactory
