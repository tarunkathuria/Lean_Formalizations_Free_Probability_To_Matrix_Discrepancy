import FaithfulMS.SquareDirectCompiledEpoch
import FaithfulMS.SquareDirectCountedFactory
import MatrixSpencer.RealRAMMSEpochLoops

/-! The actual direct-density trial at the nested original-family input.
All scalar tuning and finite horizons are computed and charged before the
walk. Original input bounds discharge every local analytic restriction. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.SquareDirectOriginalEpoch
open MatrixSpencer RealRAM MSCountedSampler
open PhaseRestriction MSManuscriptFactoryPolynomialMovementBounds
variable {ι n : Type*} [Fintype ι] [LinearOrder ι] [Fintype n] [DecidableEq n]
  {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000
variable (P : DirectSDP.PolynomialService)
  (e : Fin d ≃ n) (A : ι→Matrix n n ℂ)
  (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1)
  (x : EuclideanSpace ℝ ι)
  (y : MSManuscriptPhase.Point (ι:=Live x) (signingEpsilon ι))
  (hl : 32≤Fintype.card (Live y.val)) (hd : 0<d)

abbrev config := MSManuscriptPolynomialQueryFactory.config e A hA hN x y hl hd

theorem center_le : MSManuscriptEpochInput.centerCap (config e A hA hN x y hl hd).offset
    (N:=Fintype.card (Live y.val))≤MSManuscriptPolynomialQueryCurvature.center (Fintype.card ι) d :=
  MSManuscriptPolynomialQueryFactory.centerCap_le e A hA hN x y hl hd
    (MSManuscriptNumericalEpochRun.initial (config e A hA hN x y hl hd)).val

def compiled : Implementation
    (@SquareDirectEpochRun.output ⟨P.service⟩
      (Fintype.card (Live y.val)) d (config e A hA hN x y hl hd)) :=
  SquareDirectCompiledEpoch.output P (config e A hA hN x y hl hd) (live_le_original x y) rfl

def implementation : Implementation
    (@SquareDirectEpochRun.output ⟨P.service⟩
      (Fintype.card (Live y.val)) d (config e A hA hN x y hl hd)) :=
  SquareDirectCountedFactory.addSetup (compiled P e A hA hN x y hl hd)
    (MSEpochLoops.original e A hA hN x y hl hd).cost

def operations (P : DirectSDP.PolynomialService) (N d : ℕ) : ℕ :=
  MSEpochLoops.costBound N N d+
    MSLoopCapSetup.movementCap N d*SquareDirectCompiledEpoch.stepWork P N d+
    20*(N+1)^2+4

def draws (N d : ℕ) : ℕ := MSLoopCapSetup.movementCap N d

theorem implementation_bounded :
    Bounded (implementation P e A hA hN x y hl hd)
      (operations P (Fintype.card ι) d) (draws (Fintype.card ι) d) := by
  have he:=SquareDirectCompiledEpoch.output_with_cap P (config e A hA hN x y hl hd)
    (live_le_original x y) rfl rfl rfl (center_le e A hA hN x y hl hd)
    (MSLoopCapSetup.movementCap (Fintype.card ι) d)
    (MSEpochLoops.original_movement_le e A hA hN x y hl hd)
  have hs:=SquareDirectCountedFactory.addSetup_bounded
    (compiled P e A hA hN x y hl hd) (MSEpochLoops.original e A hA hN x y hl hd).cost he
  have hc:=MSEpochLoops.original_cost e A hA hN x y hl hd
  intro z out cost rand h
  have hb:=hs z out cost rand h
  unfold operations draws
  constructor <;> omega

end FaithfulMS.SquareDirectOriginalEpoch
