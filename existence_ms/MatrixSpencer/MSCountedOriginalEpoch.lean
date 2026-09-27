import MatrixSpencer.MSCountedCompiledEpoch
import MatrixSpencer.RealRAMMSEpochLoops
import MatrixSpencer.MSCountedEpochFactory

/-! The complete compiled square-MS trial at the actual nested factory input.
All scalar tuning and both iteration counts are computed and charged before
the walk. The local dimensions, derivative budgets, precisions, and horizons
are discharged by the original-family polynomial bounds. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSCountedOriginalEpoch
open RealRAM MSCountedSampler
open PhaseRestriction MSManuscriptFactoryPolynomialMovementBounds
variable {ι n : Type*} [Fintype ι] [LinearOrder ι] [Fintype n] [DecidableEq n]
  {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1600000
set_option maxRecDepth 5000
variable (P : KSPolynomialConvexSolver.PolynomialSolver)
  (e : Fin d ≃ n) (A : ι→Matrix n n ℂ)
  (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1)
  (x : EuclideanSpace ℝ ι)
  (y : MSManuscriptPhase.Point (ι:=Live x) (signingEpsilon ι))
  (hl : 32≤Fintype.card (Live y.val)) (hd : 0<d)

abbrev config := MSManuscriptPolynomialQueryFactory.config e A hA hN x y hl hd

theorem center_le : MSManuscriptEpochInput.centerCap (config e A hA hN x y hl hd).offset
    (N:=Fintype.card (Live y.val))≤MSManuscriptPolynomialQueryCurvature.center (Fintype.card ι) d := by
  exact MSManuscriptPolynomialQueryFactory.centerCap_le e A hA hN x y hl hd
    (MSManuscriptNumericalEpochRun.initial (config e A hA hN x y hl hd)).val

def compiled : Implementation
    (@MSConvexNumericalEpochRun.output (MSRawOwnerReport.oracle P)
      (Fintype.card (Live y.val)) d (config e A hA hN x y hl hd)) :=
  MSCountedCompiledEpoch.output P (config e A hA hN x y hl hd) (live_le_original x y)
    rfl rfl rfl (center_le e A hA hN x y hl hd)

def implementation : Implementation
    (MSCountedAcceptedEpoch.trial P (cfg e A hA hN x y hl) hd) :=
  MSCountedEpochFactory.addSetup (compiled P e A hA hN x y hl hd)
    (MSEpochLoops.original e A hA hN x y hl hd).cost

def operations (P : KSPolynomialConvexSolver.PolynomialSolver) (N d : ℕ) : ℕ :=
  MSEpochLoops.costBound N N d+
    MSLoopCapSetup.movementCap N d*MSCountedCompiledEpoch.stepWork P N d+
    20*(N+1)^2+4

def draws (N d : ℕ) : ℕ := MSLoopCapSetup.movementCap N d

theorem implementation_bounded :
    Bounded (implementation P e A hA hN x y hl hd)
      (operations P (Fintype.card ι) d) (draws (Fintype.card ι) d) := by
  have he:=MSCountedCompiledEpoch.output_with_cap P (config e A hA hN x y hl hd)
    (live_le_original x y) rfl rfl rfl (center_le e A hA hN x y hl hd)
    (MSLoopCapSetup.movementCap (Fintype.card ι) d)
    (MSEpochLoops.original_movement_le e A hA hN x y hl hd)
  have hs:=MSCountedEpochFactory.addSetup_bounded
    (compiled P e A hA hN x y hl hd) (MSEpochLoops.original e A hA hN x y hl hd).cost he
  have hc:=MSEpochLoops.original_cost e A hA hN x y hl hd
  intro z out cost rand h
  have hb:=hs z out cost rand h
  unfold operations draws
  constructor <;> omega

theorem execution_bounded
    (z : (MSCountedAcceptedEpoch.trial P (cfg e A hA hN x y hl) hd).Draws) :
    ∃cost rand,(implementation P e A hA hN x y hl hd).Executes z
      ((MSCountedAcceptedEpoch.trial P (cfg e A hA hN x y hl) hd).value z) cost rand ∧
      cost≤operations P (Fintype.card ι) d ∧ rand≤draws (Fintype.card ι) d :=
  MSCountedSampler.execution_bounded (implementation P e A hA hN x y hl hd)
    (implementation_bounded P e A hA hN x y hl hd) z

end MatrixSpencer.MSCountedOriginalEpoch
