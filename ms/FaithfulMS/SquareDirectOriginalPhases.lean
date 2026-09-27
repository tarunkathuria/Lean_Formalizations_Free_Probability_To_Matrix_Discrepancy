import FaithfulMS.SquareDirectOriginalEpoch
import FaithfulMS.SquareDirectAcceptanceArithmetic
import MatrixSpencer.MSCountedHalfPhase
import FaithfulMS.SquareDirectProvider

/-! The concrete compiled trial is inserted into the actual nested numerical
half-phase. Only construction and label-restoration routines remain arguments
here; the following input assembly instantiates those finite routines. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.SquareDirectOriginalPhases
open MatrixSpencer
open PhaseRestriction MSManuscriptMatrixReindex MSManuscriptPhase MSCountedSampler
open MSManuscriptNumericalHalfPhase
open RealRAM.MSPoint (Table)
variable {ι n : Type*} [Fintype ι] [LinearOrder ι] [Fintype n] [DecidableEq n] [Nonempty n]
  {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1600000
set_option maxRecDepth 12000
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run
variable (P : DirectSDP.PolynomialService)
  (e : Fin d≃n) (hd : 0<d) (A : ι→Matrix n n ℂ)
  (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1)

abbrev innerH (x : EuclideanSpace ℝ ι) := selfAdjointReindex e (restrictedOffset 0 A hA x)
abbrev innerA (x : EuclideanSpace ℝ ι) := fun i : Live x => (A i).submatrix e e
abbrev innerHermitian (x : EuclideanSpace ℝ ι) := fun i : Live x => (hA i).submatrix e
abbrev innerContractions (x : EuclideanSpace ℝ ι) := fun i : Live x => reindex_contraction e (hN i)

theorem margin_small (x : EuclideanSpace ℝ ι) :
    (Fintype.card (Live x):ℝ)*signingEpsilon ι≤1/1000 :=
  (mul_le_mul_of_nonneg_right (show (Fintype.card (Live x):ℝ)≤Fintype.card ι by
    exact_mod_cast Fintype.card_subtype_le (fun i=>i∉frozenCoordinates x)) signingEpsilon_pos.le).trans
      signingEpsilon_count_small

abbrev Routines (x : EuclideanSpace ℝ ι) (y : Point (ι:=Live x) (signingEpsilon ι))
    (hl : 32≤Fintype.card (Live y.val)) :=
  SquareDirectCountedFactory.Routines (innerH e A hA x) (innerA e A x) (innerHermitian e A hA x)
    (innerContractions e A hN x) (signingEpsilon ι) signingEpsilon_pos (margin_small x) hd y hl

lemma live_large {κ : Type*} [Fintype κ] [DecidableEq κ] {ε : ℝ} (y : Point (ι:=κ) ε)
    (hy : ¬FiniteHalfPhase.Terminal y.val) : 32≤Fintype.card (Live y.val) := by
  classical
  simpa only [live_card,FiniteHalfPhase.liveCount] using FiniteHalfPhase.liveCount_large_of_nonterminal hy

def factory (x : EuclideanSpace ℝ ι) (r : ℕ) :=
  letI : SquareDirectOracle.Oracle := ⟨P.service⟩
  SquareDirectProvider.factory e hd (restrictedOffset 0 A hA x) (restrictedFamily A x)
    (restrictedFamily_hermitian A hA x) (restrictedFamily_contractions A hN x)
    (signingEpsilon ι) signingEpsilon_pos (margin_small x) r

def epoch (x : EuclideanSpace ℝ ι) (r : ℕ)
    (y : Point (ι:=Live x) (signingEpsilon ι)) (hy : ¬FiniteHalfPhase.Terminal y.val)
    (C : Routines e hd A hA hN x y (live_large y hy)) :
    Implementation ((factory P e hd A hA hN x r).sample y hy) := by
  letI : SquareDirectOracle.Oracle := ⟨P.service⟩
  let E := SquareDirectOriginalEpoch.implementation P e A hA hN x y (live_large y hy) hd
  let cfg := MSManuscriptFactoryPolynomialMovementBounds.cfg e A hA hN x y (live_large y hy)
  let T := SquareDirectCountedAcceptance.implementation cfg hd E
    (SquareDirectAcceptanceArithmetic.evaluation P cfg hd) r
  exact SquareDirectCountedFactory.implementation (innerH e A hA x) (innerA e A x)
    (innerHermitian e A hA x) (innerContractions e A hN x)
    (signingEpsilon ι) signingEpsilon_pos (margin_small x) hd y (live_large y hy) C r T

def epochCost (P : DirectSDP.PolynomialService) (N d r J K : ℕ) : ℕ :=
  J+(r*(SquareDirectOriginalEpoch.operations P N d+SquareDirectAcceptanceArithmetic.work P N d+3)+1)+K+4

theorem epoch_bounded (x : EuclideanSpace ℝ ι) (r : ℕ)
    (y : Point (ι:=Live x) (signingEpsilon ι)) (hy : ¬FiniteHalfPhase.Terminal y.val)
    (C : Routines e hd A hA hN x y (live_large y hy)) {J K : ℕ}
    (hJ : C.config.cost≤J) (hK : ∀s,(C.restore s).cost≤K) :
    Bounded (epoch P e hd A hA hN x r y hy C) (epochCost P (Fintype.card ι) d r J K)
      (r*SquareDirectOriginalEpoch.draws (Fintype.card ι) d) := by
  letI : SquareDirectOracle.Oracle := ⟨P.service⟩
  let cfg := MSManuscriptFactoryPolynomialMovementBounds.cfg e A hA hN x y (live_large y hy)
  have hT := SquareDirectCountedAcceptance.implementation_bounded cfg hd
    (SquareDirectOriginalEpoch.implementation P e A hA hN x y (live_large y hy) hd)
    (SquareDirectAcceptanceArithmetic.evaluation P cfg hd)
    (SquareDirectOriginalEpoch.implementation_bounded P e A hA hN x y (live_large y hy) hd)
    (fun s => (SquareDirectAcceptanceArithmetic.accepts_cost P cfg hd s).trans
      (SquareDirectAcceptanceArithmetic.work_mono P
        (MSManuscriptFactoryPolynomialMovementBounds.live_le_original x y))) r
  exact SquareDirectCountedFactory.implementation_bounded (innerH e A hA x) (innerA e A x)
    (innerHermitian e A hA x) (innerContractions e A hN x)
    (signingEpsilon ι) signingEpsilon_pos (margin_small x) hd y (live_large y hy) C r _ hT hJ hK

def phaseSampler (x : Point (ι:=ι) (signingEpsilon ι)) (hx : 0<Fintype.card (Live x.val)) (r : ℕ) :=
  MSManuscriptNumericalHalfPhase.output (restrictedOffset 0 A hA x.val) (restrictedFamily A x.val)
    (restrictedFamily_hermitian A hA x.val) (signingEpsilon ι) (epochFailure r)
    (factory P e hd A hA hN x.val r) (by change 0≤(301/800:ℝ)^r; positivity) hx
    ⟨restrictPoint x.val,restrictPoint_regular x.property⟩

def phase (x : Point (ι:=ι) (signingEpsilon ι)) (hx : 0<Fintype.card (Live x.val))
    (L : Table (Live x.val))
    (C : ∀y hy,Routines e hd A hA hN x.val y (live_large y hy)) (r : ℕ) :
    Implementation (phaseSampler P e hd A hA hN x hx r) :=
  MSCountedHalfPhase.output (restrictedOffset 0 A hA x.val) (restrictedFamily A x.val)
    (restrictedFamily_hermitian A hA x.val) L (factory P e hd A hA hN x.val r)
    (fun y hy => epoch P e hd A hA hN x.val r y hy (C y hy))
    (by change 0≤(301/800:ℝ)^r; positivity) hx ⟨restrictPoint x.val,restrictPoint_regular x.property⟩

def phaseCost (P : DirectSDP.PolynomialService) (N d r J K : ℕ) : ℕ :=
  epochCalls*(epochCost P N d r J K+24*N+29)+17*N+15

private theorem weaken {α : Type*} {S : MSManuscriptAdaptive.Sampler α} (E : Implementation S) {B C R T : ℕ}
    (h : Bounded E B R) (hb : B≤C) (hr : R≤T) : Bounded E C T := by
  intro z out cost draws he
  have h':=h z out cost draws he
  exact ⟨h'.1.trans hb,h'.2.trans hr⟩

theorem phase_bounded (x : Point (ι:=ι) (signingEpsilon ι)) (hx : 0<Fintype.card (Live x.val))
    (L : Table (Live x.val))
    (C : ∀y hy,Routines e hd A hA hN x.val y (live_large y hy)) (r : ℕ) {J K : ℕ}
    (hJ : ∀y hy,(C y hy).config.cost≤J) (hK : ∀y hy s,((C y hy).restore s).cost≤K) :
    Bounded (phase P e hd A hA hN x hx L C r) (phaseCost P (Fintype.card ι) d r J K)
      (epochCalls*(r*SquareDirectOriginalEpoch.draws (Fintype.card ι) d)) := by
  have he := MSCountedHalfPhase.output_bounded (restrictedOffset 0 A hA x.val) (restrictedFamily A x.val)
    (restrictedFamily_hermitian A hA x.val) L (factory P e hd A hA hN x.val r)
    (fun y hy => epoch P e hd A hA hN x.val r y hy (C y hy))
    (by change 0≤(301/800:ℝ)^r; positivity) hx ⟨restrictPoint x.val,restrictPoint_regular x.property⟩
    (fun y hy => epoch_bounded P e hd A hA hN x.val r y hy (C y hy) (hJ y hy) (hK y hy))
  apply weaken _ he
  · have hl : Fintype.card (Live x.val)≤Fintype.card ι := Fintype.card_subtype_le _
    unfold phaseCost
    gcongr
  · exact le_rfl

end FaithfulMS.SquareDirectOriginalPhases
