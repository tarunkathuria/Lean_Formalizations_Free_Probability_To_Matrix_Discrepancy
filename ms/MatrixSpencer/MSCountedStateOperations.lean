import MatrixSpencer.MSCountedMovement
import MatrixSpencer.MSManuscriptNumericalEpochRun

/-! Scalar bookkeeping and actual stopping decisions surrounding each square
walk step. Paid size and movement mesh are stored scalar parameters whose
separate input-only computations are charged by the setup implementation. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSCountedStateOperations
open RealRAM
open RealRAM.JacobiIteration (Counted Mat)
open MSManuscriptNumericalEpochLedger
open MSManuscriptSupportedOwner (Owner)
open MSManuscriptSupportedGamma (Parameters)
attribute [local instance] Classical.propDecidable
variable {N d : ℕ}
set_option maxRecDepth 4096

def afterPrepare (P : Parameters N d) (s : State N) (y : Owner N×ℕ) : Counted (State N) :=
  let a:=MSGammaTop.physical s.owner
  let b:=MSGammaTop.physical y.1
  let ta:=MSSampling.traceExpr.eval (JacobiIteration.entries a.value)
  let tb:=MSSampling.traceExpr.eval (JacobiIteration.entries b.value)
  let debit:=MSManuscriptSupportedPaid.paidSize P*(y.2:ℝ)
  ⟨{s with owner:=y.1,paid:=s.paid+debit,dust:=s.dust+(ta-tb-debit)},
    a.cost+b.cost+2*(MSSampling.traceExpr (k:=N)).cost+20*(N+s.owner.dim+y.1.dim+1)^2+20⟩

theorem afterPrepare_value (P : Parameters N d) (s : State N) (y : Owner N×ℕ) :
    (afterPrepare P s y).value=MSManuscriptNumericalEpochLedger.afterPrepare P s y := by
  simp only [afterPrepare,MSGammaTop.physical_value,MSSampling.trace_eval,
    MSManuscriptNumericalEpochLedger.afterPrepare]

theorem afterPrepare_cost (P : Parameters N d) (s : State N) (y : Owner N×ℕ) :
    (afterPrepare P s y).cost≤500*(N+s.owner.dim+y.1.dim+1)^3 := by
  have ha:=MSGammaTop.physical_cost s.owner
  have hb:=MSGammaTop.physical_cost y.1
  have ha' : (N+s.owner.dim+1)^3≤(N+s.owner.dim+y.1.dim+1)^3 := Nat.pow_le_pow_left (by omega) _
  have hb' : (N+y.1.dim+1)^3≤(N+s.owner.dim+y.1.dim+1)^3 := Nat.pow_le_pow_left (by omega) _
  have hp2 : (N+s.owner.dim+y.1.dim+1)^2≤(N+s.owner.dim+y.1.dim+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hp1 : N+s.owner.dim+y.1.dim+1≤(N+s.owner.dim+y.1.dim+1)^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (n:=N+s.owner.dim+y.1.dim+1) (by omega) (show 1≤3 by omega)
  dsimp only [afterPrepare]
  rw [MSSampling.trace_cost]
  omega

/-- Frozen status is tested by two exact real equalities per coordinate. -/
def stopped (h : ℝ) (s : State N) : Counted Bool :=
  let f:=MSCovariance.frozen s.point (List.finRange N)
  ⟨decide (timeLimit≤s.time ∨ (N:ℝ)/64≤f.value.length ∨
      (N:ℝ)/64<s.paid+s.dust ∨ timeLimit<s.time+h^2),
    f.cost+30*N+40⟩

theorem frozen_length (s : State N) :
    (MSCovariance.frozen s.point (List.finRange N)).value.length=(frozenCoordinates s.point).card := by
  rw [MSCovariance.frozen_value]
  exact MSManuscriptNumericalEpochShort.length_frozenLabels _

theorem stopped_value (c : MSManuscriptNumericalEpochRun.Config N d) (s : State N) :
    (stopped (MSManuscriptNumericalEpochRun.mesh c) s).value=
      decide (MSManuscriptNumericalEpochRun.Stopped c s) := by
  simp only [stopped,frozen_length,MSManuscriptNumericalEpochRun.Stopped,Terminal,or_assoc]

theorem stopped_cost (h : ℝ) (s : State N) : (stopped h s).cost≤42*N+41 := by
  dsimp only [stopped]
  rw [MSCovariance.frozen_cost,List.length_finRange]
  omega

/-- The initial owner matrix/frame are coordinate identities, and all ledger
scalars and centered coordinates are literal zeros. -/
def initial (x : EuclideanSpace ℝ (Fin N)) : Counted (State N) :=
  ⟨MSManuscriptNumericalEpochLedger.initial x,20*(N+1)^2⟩

theorem initial_value (x : EuclideanSpace ℝ (Fin N)) :
    (initial x).value=MSManuscriptNumericalEpochLedger.initial x := rfl

end MatrixSpencer.MSCountedStateOperations
