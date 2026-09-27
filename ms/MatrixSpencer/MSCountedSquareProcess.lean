import MatrixSpencer.MSCountedOriginalPhases
import MatrixSpencer.MSCountedNumericalFullSigning
import MatrixSpencer.RealRAMMSPhaseSetup
import MatrixSpencer.RealRAMMSEpochFactorySetup

/-! Complete phase composition from original Hermitian contractions. All
configuration, restoration, epoch, and outer-phase routines are instantiated
by their concrete counted implementations. The final input wrapper supplies
the original signed lift and its explicit physical-coordinate table. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSCountedSquareProcess
open MSManuscriptAdaptive MSCountedSampler MSManuscriptPhase PhaseRestriction
open MSManuscriptNumericalHalfPhase
open RealRAM
open RealRAM.MSPoint (Table)
open RealRAM.MSLabelTable (Ordered)
variable {ι n : Type*} [Fintype ι] [LinearOrder ι] [Fintype n] [DecidableEq n] [Nonempty n]
  {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run
variable (P : KSPolynomialConvexSolver.PolynomialSolver)
  (L : Table ι) (hL : Ordered L) (e : Fin d≃n) (hd : 0<d)
  (A : ι→Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1)

abbrev routines (x : EuclideanSpace ℝ ι) (y : Point (ι:=Live x) (signingEpsilon ι))
    (hl : 32≤Fintype.card (Live y.val)) : MSCountedOriginalPhases.Routines e hd A hA hN x y hl :=
  MSEpochFactorySetup.routines (MSEpochFactorySetup.liveTable L x).value (MSEpochFactorySetup.liveTable_ordered L hL x)
    (MSCountedOriginalPhases.innerH e A hA x) (MSCountedOriginalPhases.innerA e A x)
    (MSCountedOriginalPhases.innerHermitian e A hA x) (MSCountedOriginalPhases.innerContractions e A hN x)
    (signingEpsilon ι) signingEpsilon_pos (MSCountedOriginalPhases.margin_small x) hd y hl

def configCost (N d : ℕ) : ℕ := MSEpochFactorySetup.configCost N d
def restoreCost (N : ℕ) : ℕ := 30*(N+1)^2+3

theorem routines_config_cost (x : EuclideanSpace ℝ ι) (y : Point (ι:=Live x) (signingEpsilon ι))
    (hl : 32≤Fintype.card (Live y.val)) :
    (routines L hL e hd A hA hN x y hl).config.cost≤configCost (Fintype.card ι) d := by
  have h:=MSEpochFactorySetup.config_cost (MSEpochFactorySetup.liveTable L x).value
    (MSEpochFactorySetup.liveTable_ordered L hL x) (MSCountedOriginalPhases.innerH e A hA x)
    (MSCountedOriginalPhases.innerA e A x) (MSCountedOriginalPhases.innerHermitian e A hA x)
    (MSCountedOriginalPhases.innerContractions e A hN x) (signingEpsilon ι) signingEpsilon_pos
    (MSCountedOriginalPhases.margin_small x) y hl
  apply h.trans
  have hc : Fintype.card (Live x)≤Fintype.card ι := Fintype.card_subtype_le _
  unfold configCost MSEpochFactorySetup.configCost
  gcongr

theorem routines_restore_cost (x : EuclideanSpace ℝ ι) (y : Point (ι:=Live x) (signingEpsilon ι))
    (hl : 32≤Fintype.card (Live y.val)) (s) :
    ((routines L hL e hd A hA hN x y hl).restore s).cost≤restoreCost (Fintype.card ι) := by
  have h:=MSEpochFactorySetup.restore_cost (MSEpochFactorySetup.liveTable L x).value
    (MSEpochFactorySetup.liveTable_ordered L hL x) (MSCountedOriginalPhases.innerH e A hA x)
    (MSCountedOriginalPhases.innerA e A x) (MSCountedOriginalPhases.innerHermitian e A hA x)
    (MSCountedOriginalPhases.innerContractions e A hN x) (signingEpsilon ι) signingEpsilon_pos
    (MSCountedOriginalPhases.margin_small x) hd y hl s
  apply h.trans
  have hc : Fintype.card (Live x)≤Fintype.card ι := Fintype.card_subtype_le _
  unfold restoreCost
  gcongr

def phase (x : Point (ι:=ι) (signingEpsilon ι)) (hx : 0<Fintype.card (Live x.val)) (r : ℕ) :
    Implementation (MSCountedOriginalPhases.phaseSampler P e hd A hA hN x hx r) :=
  MSCountedOriginalPhases.phase P e hd A hA hN x hx (MSEpochFactorySetup.liveTable L x.val).value
    (fun y hy => routines L hL e hd A hA hN x.val y (MSCountedOriginalPhases.live_large y hy)) r

def phaseCost (P : KSPolynomialConvexSolver.PolynomialSolver) (N d r : ℕ) : ℕ :=
  MSCountedOriginalPhases.phaseCost P N d r (configCost N d) (restoreCost N)

theorem phase_bounded (x : Point (ι:=ι) (signingEpsilon ι)) (hx : 0<Fintype.card (Live x.val)) (r : ℕ) :
    Bounded (phase P L hL e hd A hA hN x hx r) (phaseCost P (Fintype.card ι) d r)
      (epochCalls*(r*MSCountedOriginalEpoch.draws (Fintype.card ι) d)) :=
  MSCountedOriginalPhases.phase_bounded P e hd A hA hN x hx (MSEpochFactorySetup.liveTable L x.val).value
    (fun y hy => routines L hL e hd A hA hN x.val y (MSCountedOriginalPhases.live_large y hy)) r
    (fun y hy => routines_config_cost L hL e hd A hA hN x.val y _)
    (fun y hy s => routines_restore_cost L hL e hd A hA hN x.val y _ s)

def provider (r : ℕ) :=
  letI:=MSRawOwnerReport.oracle P
  MSConvexValueProvider.provider e hd 0 A hA hN (signingEpsilon ι) signingEpsilon_pos signingEpsilon_count_small r

def sampler (r : ℕ) (start : Point (ι:=ι) (signingEpsilon ι)) :=
  MSManuscriptNumericalFullSigning.output 0 A hA hN (signingEpsilon ι) (epochFailure r)
    (provider P e hd A hA hN r) (by change 0≤(301/800:ℝ)^r; positivity) start

def implementation (r : ℕ) (start : Point (ι:=ι) (signingEpsilon ι)) :
    Implementation (sampler P e hd A hA hN r start) :=
  MSCountedNumericalFullSigning.output 0 A hA hN (signingEpsilon ι) (epochFailure r)
    (provider P e hd A hA hN r) (by change 0≤(301/800:ℝ)^r; positivity) L
    (fun x hx => phase P L hL e hd A hA hN x hx r)
    (fun x => (MSPhaseSetup.setup L e A hA x.val).cost+1) start

def operations (P : KSPolynomialConvexSolver.PolynomialSolver) (N d r : ℕ) : ℕ :=
  (N+1)*(phaseCost P N d r+(MSPhaseSetup.setupCost N d+1)+32*N+26)+4

def draws (N d r : ℕ) : ℕ := (N+1)*(epochCalls*(r*MSCountedOriginalEpoch.draws N d))

theorem implementation_bounded (r : ℕ) (start : Point (ι:=ι) (signingEpsilon ι)) :
    Bounded (implementation P L hL e hd A hA hN r start) (operations P (Fintype.card ι) d r)
      (draws (Fintype.card ι) d r) :=
  MSCountedNumericalFullSigning.output_bounded 0 A hA hN (signingEpsilon ι) (epochFailure r)
    (provider P e hd A hA hN r) (by change 0≤(301/800:ℝ)^r; positivity) L
    (fun x hx => phase P L hL e hd A hA hN x hx r)
    (fun x => (MSPhaseSetup.setup L e A hA x.val).cost+1) start
    (fun x hx => phase_bounded P L hL e hd A hA hN x hx r)
    (fun x => Nat.add_le_add_right (MSPhaseSetup.setup_cost L e A hA x.val) 1)

end MatrixSpencer.MSCountedSquareProcess
