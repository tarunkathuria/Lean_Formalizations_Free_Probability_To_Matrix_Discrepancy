import MatrixSpencer.RectangularRidgeMovementWork

/-! Primitive label scans and state bookkeeping for the fixed-universe walk.
Fresh live frames are built from ordered coordinate lookups. Stopping counts
only coordinates newly frozen since this epoch began. The numerical parameters
are stored outputs of the separate primitive setup circuits. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RectangularRidgeStateWork
open RealRAM
open RealRAM.JacobiIteration (Counted Mat)
open MSManuscriptNumericalEpochLedger (State)
open MSManuscriptSupportedOwner (Owner)
open RectangularRidgeEpochInput
variable {N d : ℕ} [Nonempty (Fin d)]
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

/-- Two sign comparisons per coordinate and an ordered retained-label list. -/
def liveLabels (x : EuclideanSpace ℝ (Fin N)) : List (Fin N) → Counted (List (Fin N))
  | []=>⟨[],1⟩
  | i::is=>let t:=liveLabels x is
           ⟨if IsSign (x i) then t.value else i::t.value,t.cost+12⟩

theorem liveLabels_value (x : EuclideanSpace ℝ (Fin N)) (is : List (Fin N)) :
    (liveLabels x is).value=is.filter (fun i=>decide (i∉frozenCoordinates x)) := by
  induction is with
  | nil=>rfl
  | cons i is ih=>
    simp only [liveLabels,ih,List.filter_cons,decide_eq_true_eq,mem_frozenCoordinates]
    split_ifs <;> simp_all

theorem liveLabels_cost (x : EuclideanSpace ℝ (Fin N)) (is : List (Fin N)) :
    (liveLabels x is).cost=12*is.length+1 := by
  induction is with
  | nil=>rfl
  | cons i is ih=>simp only [liveLabels,ih,List.length_cons];omega

def coordinateOwner (is : List (Fin N)) : Owner N where
  dim:=is.length
  frame:=(1 : Matrix (Fin N) (Fin N) ℝ).submatrix id (fun j=>is.get j)
  matrix:=1

theorem coordinateOwner_eq (F : Finset (Fin N)) :
    coordinateOwner (RectangularRidgeLiveOwner.labels F)=RectangularRidgeLiveOwner.owner F := rfl

/-- Even linear-time list lookup at every matrix entry is covered by the
cubic charge. Entries themselves are only coordinate comparisons and 0/1. -/
def owner (x : EuclideanSpace ℝ (Fin N)) : Counted (Owner N) :=
  let L:=liveLabels x (List.finRange N)
  ⟨coordinateOwner L.value,L.cost+8*(N+L.value.length+1)^3⟩

theorem owner_value (x : EuclideanSpace ℝ (Fin N)) :
    (owner x).value=RectangularRidgeLiveOwner.owner (frozenCoordinates x) := by
  simp only [owner,liveLabels_value]
  exact coordinateOwner_eq _

theorem owner_cost (x : EuclideanSpace ℝ (Fin N)) : (owner x).cost≤100*(N+1)^3 := by
  have hl : (liveLabels x (List.finRange N)).value.length≤N := by
    rw [liveLabels_value]
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange)
  have hn : N+1≤(N+1)^3 := by simpa using Nat.pow_le_pow_right (n:=N+1) (by omega) (show 1≤3 by omega)
  have hp : (N+(liveLabels x (List.finRange N)).value.length+1)^3≤8*(N+1)^3 := by
    calc _≤(2*(N+1))^3 := Nat.pow_le_pow_left (by omega) _
      _=_ := by ring
  simp only [owner,liveLabels_cost,List.length_finRange]
  omega

def initial (x : EuclideanSpace ℝ (Fin N)) : Counted (MSManuscriptNumericalEpochLedger.State N) :=
  let o:=owner x
  ⟨{point:=x,owner:=o.value,time:=0,variance:=0,paid:=0,dust:=0,rounding:=0,centered:=0},
    o.cost+20*(N+1)^2⟩

theorem initial_value (x : EuclideanSpace ℝ (Fin N)) :
    (initial x).value=RectangularRidgeLiveOwner.initial x := by
  simp only [initial,owner_value]
  rfl

theorem initial_cost (x : EuclideanSpace ℝ (Fin N)) : (initial x).cost≤120*(N+1)^3 := by
  have ho:=owner_cost x
  have hp : (N+1)^2≤(N+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  dsimp only [initial]
  omega

def newlyFrozen (x₀ x : EuclideanSpace ℝ (Fin N)) : List (Fin N) → Counted (List (Fin N))
  | []=>⟨[],1⟩
  | i::is=>let t:=newlyFrozen x₀ x is
           ⟨if IsSign (x i) ∧ ¬IsSign (x₀ i) then i::t.value else t.value,t.cost+24⟩

theorem newlyFrozen_value (x₀ x : EuclideanSpace ℝ (Fin N)) (is : List (Fin N)) :
    (newlyFrozen x₀ x is).value=is.filter (fun i=>decide (i∈frozenCoordinates x\frozenCoordinates x₀)) := by
  induction is with
  | nil=>rfl
  | cons i is ih=>simp only [newlyFrozen,ih,List.filter_cons,decide_eq_true_eq,
      Finset.mem_sdiff,mem_frozenCoordinates]

theorem newlyFrozen_length (x₀ x : EuclideanSpace ℝ (Fin N)) :
    (newlyFrozen x₀ x (List.finRange N)).value.length=(frozenCoordinates x\frozenCoordinates x₀).card := by
  rw [newlyFrozen_value]
  exact MSManuscriptNumericalEpochShort.length_frozenLabels _

theorem newlyFrozen_cost (x₀ x : EuclideanSpace ℝ (Fin N)) (is : List (Fin N)) :
    (newlyFrozen x₀ x is).cost=24*is.length+1 := by
  induction is with
  | nil=>rfl
  | cons i is ih=>simp only [newlyFrozen,ih,List.length_cons];omega

def stopped (c : Config N d) (s : MSManuscriptNumericalEpochLedger.State N) : Counted Bool :=
  let f:=newlyFrozen c.start s.point (List.finRange N)
  ⟨decide (duration c≤s.time ∨ (live c : ℝ)/64≤f.value.length ∨
      (live c : ℝ)/64<s.paid+s.dust ∨ duration c<s.time+mesh c^2),
    f.cost+30*N+50⟩

theorem stopped_value (c : Config N d) (s : MSManuscriptNumericalEpochLedger.State N) :
    (stopped c s).value=decide (RectangularRidgeEpochRun.Stopped c s) := by
  simp only [stopped,newlyFrozen_length,RectangularRidgeEpochRun.Stopped,
    RectangularRidgeLiveEpochLedger.Terminal,oldFrozen,or_assoc]

theorem stopped_cost (c : Config N d) (s : MSManuscriptNumericalEpochLedger.State N) : (stopped c s).cost≤54*N+51 := by
  simp only [stopped,newlyFrozen_cost,List.length_finRange]
  omega

def afterPrepare (P : RectangularRidgePreparationData.Parameters N d)
    (s : MSManuscriptNumericalEpochLedger.State N) (y : Owner N×ℕ) : Counted (MSManuscriptNumericalEpochLedger.State N) :=
  let a:=MSGammaTop.physical s.owner
  let b:=MSGammaTop.physical y.1
  let ta:=MSSampling.traceExpr.eval (JacobiIteration.entries a.value)
  let tb:=MSSampling.traceExpr.eval (JacobiIteration.entries b.value)
  let debit:=RectangularRidgePreparationData.paidSize P*(y.2 : ℝ)
  ⟨{s with owner:=y.1,paid:=s.paid+debit,dust:=s.dust+(ta-tb-debit)},
    a.cost+b.cost+2*(MSSampling.traceExpr (k:=N)).cost+20*(N+s.owner.dim+y.1.dim+1)^2+20⟩

theorem afterPrepare_value (P : RectangularRidgePreparationData.Parameters N d)
    (s : MSManuscriptNumericalEpochLedger.State N) (y : Owner N×ℕ) :
    (afterPrepare P s y).value=RectangularRidgeEpochLedger.afterPrepare P s y := by
  simp only [afterPrepare,MSGammaTop.physical_value,MSSampling.trace_eval,
    RectangularRidgeEpochLedger.afterPrepare]

theorem afterPrepare_cost (P : RectangularRidgePreparationData.Parameters N d)
    (s : MSManuscriptNumericalEpochLedger.State N) (y : Owner N×ℕ) :
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

end MatrixSpencer.RectangularRidgeStateWork
