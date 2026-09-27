import MatrixSpencer.MSCountedEpochPreparation
import MatrixSpencer.MSCountedAdaptive

/-! Literal stopping/preparation/movement control flow for the numerical square
walk. The records below assemble counted concrete routines; they are not
unit-cost computational primitives. Primitive implementations and uniform
bounds are supplied by the adjoining numerical modules. -/
noncomputable section
namespace MatrixSpencer.MSCountedEpochStep
open MSManuscriptAdaptive
open MSCountedSampler
open RealRAM.JacobiIteration (Counted)
open MSManuscriptNumericalEpochRun (Config Certified Stopped mesh movement initial count)
variable [MSConvexOwnerValue.Oracle]
variable {N d : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

structure Routines (c : Config N d) where
  prepare : Certified c → Counted (Certified c)
  prepare_value : ∀s,(prepare s).value=MSConvexNumericalEpochRun.prepare c s
  movement : ∀(s : Certified c) (hfloor : s.val.owner.Valid (2*c.floor))
    (hnt : ¬Stopped c s.val),Implementation (MSManuscriptNumericalEpochRun.movement c s hfloor hnt)

def overheadCost (c : Config N d) (R : Routines c) (s : Certified c) : ℕ :=
  (MSCountedStateOperations.stopped (mesh c) s.val).cost+(R.prepare s).cost+
    (MSCountedStateOperations.stopped (mesh c) (MSConvexNumericalEpochRun.prepare c s).val).cost+5

/-- Both status predicates are the previously compiled finite scalar tests.
The proof-indexed branch below has exactly their computed boolean value. -/
def next (c : Config N d) (R : Routines c) (s : Certified c) :
    Implementation (MSConvexNumericalEpochRun.next c s) :=
  if hs : Stopped c s.val then
    congr (MSConvexNumericalEpochRun.next_stopped c s hs).symm
      (overhead (pure s 0) ((MSCountedStateOperations.stopped (mesh c) s.val).cost+2))
  else
    if hp : Stopped c (MSConvexNumericalEpochRun.prepare c s).val then
      congr (by simp only [MSConvexNumericalEpochRun.next,dif_neg hs,dif_pos hp])
        (overhead (pure (MSConvexNumericalEpochRun.prepare c s) 0) (overheadCost c R s))
    else
      congr (by simp only [MSConvexNumericalEpochRun.next,dif_neg hs,dif_neg hp])
        (overhead (R.movement (MSConvexNumericalEpochRun.prepare c s)
          (MSConvexNumericalEpochRun.prepare_floor c s) hp) (overheadCost c R s))

def stepBudget (N U V : ℕ) : ℕ := U+V+1000*(N+1)^2

theorem next_bounded (c : Config N d) (R : Routines c) (U V : ℕ)
    (hU : ∀s,(R.prepare s).cost ≤ U)
    (hV : ∀s hfloor hnt,Bounded (R.movement s hfloor hnt) V 1)
    (s : Certified c) : Bounded (next c R s) (stepBudget N U V) 1 := by
  have ht:=MSCountedStateOperations.stopped_cost (mesh c) s.val
  have hp:=MSCountedStateOperations.stopped_cost (mesh c) (MSConvexNumericalEpochRun.prepare c s).val
  have hu:=hU s
  have h1 : N+1 ≤ (N+1)^2 := by nlinarith
  unfold next
  split_ifs with hs hp'
  · apply congr_bounded
    intro z out cost draws he
    have hb:=overhead_bounded (pure s 0)
      ((MSCountedStateOperations.stopped (mesh c) s.val).cost+2) (pure_bounded s 0) z out cost draws he
    unfold stepBudget
    constructor <;> omega
  · apply congr_bounded
    intro z out cost draws he
    have hb:=overhead_bounded (pure (MSConvexNumericalEpochRun.prepare c s) 0) _
      (pure_bounded _ 0) z out cost draws he
    dsimp only [overheadCost] at hb
    unfold stepBudget
    constructor <;> omega
  · apply congr_bounded
    intro z out cost draws he
    have hb:=overhead_bounded (R.movement (MSConvexNumericalEpochRun.prepare c s)
      (MSConvexNumericalEpochRun.prepare_floor c s) hp') _ (hV _ _ _) z out cost draws he
    dsimp only [overheadCost] at hb
    unfold stepBudget
    constructor <;> omega

theorem iterate_eq (c : Config N d) (k : ℕ) (s : Certified c) :
    iterateSample (MSConvexNumericalEpochRun.next c) k s=MSConvexNumericalEpochRun.run c k s := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>
    simp only [iterateSample,MSConvexNumericalEpochRun.run]
    rw [funext ih]

def run (c : Config N d) (R : Routines c) (k : ℕ) (s : Certified c) :
    Implementation (MSConvexNumericalEpochRun.run c k s) :=
  congr (iterate_eq c k s) (iterate (next c R) k s)

theorem run_bounded (c : Config N d) (R : Routines c) (U V : ℕ)
    (hU : ∀s,(R.prepare s).cost ≤ U)
    (hV : ∀s hfloor hnt,Bounded (R.movement s hfloor hnt) V 1)
    (k : ℕ) (s : Certified c) :
    Bounded (run c R k s) (k*(stepBudget N U V+2)+1) k := by
  exact congr_bounded (iterate_eq c k s) _
    (by simpa only [Nat.mul_one] using iterate_bounded (next c R) (next_bounded c R U V hU hV) k s)

def output (c : Config N d) (R : Routines c) :
    Implementation (MSConvexNumericalEpochRun.output c) :=
  overhead (run c R (count c) (initial c))
    ((MSCountedStateOperations.initial c.start).cost+2)

theorem output_bounded (c : Config N d) (R : Routines c) (U V : ℕ)
    (hU : ∀s,(R.prepare s).cost ≤ U)
    (hV : ∀s hfloor hnt,Bounded (R.movement s hfloor hnt) V 1) :
    Bounded (output c R)
      ((count c)*(stepBudget N U V+2)+20*(N+1)^2+3) (count c) := by
  have h:=overhead_bounded (run c R (count c) (initial c))
    ((MSCountedStateOperations.initial c.start).cost+2) (run_bounded c R U V hU hV _ _)
  convert h using 1 <;> simp only [MSCountedStateOperations.initial] <;> omega

end MatrixSpencer.MSCountedEpochStep
