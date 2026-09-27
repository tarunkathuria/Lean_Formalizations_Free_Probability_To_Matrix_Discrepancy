import FaithfulMS.RectangularDirectEpochRun
import MatrixSpencer.RectangularRidgeStateWork
import MatrixSpencer.MSCountedAdaptive

/-! Literal stopping/preparation/movement control flow for the numerical rectangular ridge
walk. The records below assemble counted concrete routines; they are not
unit-cost computational primitives. Primitive implementations and uniform
bounds are supplied by the adjoining numerical modules. -/
noncomputable section
namespace MatrixSpencer.RectangularDirectEpochWork
open MSManuscriptAdaptive
open MSCountedSampler
open RealRAM.JacobiIteration (Counted)
open RectangularRidgeEpochInput (Config mesh)
open RectangularDirectEpochRun (Certified Stopped movement initial count)
variable {N d : ℕ} [Nonempty (Fin d)]
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

structure Routines (solver : RectangularDirectSolver.Service) (a : Fin d) (c : Config N d) where
  prepare : Certified c → Counted (Certified c)
  prepare_value : ∀s,(prepare s).value=RectangularDirectEpochRun.prepare solver a c s
  movement : ∀(s : Certified c) (hfloor : s.val.owner.Valid (2*RectangularRidgePreparationData.floor))
    (hnt : ¬Stopped c s.val),Implementation (RectangularDirectEpochRun.movement c s hfloor hnt)

def overheadCost (solver : RectangularDirectSolver.Service) (a : Fin d) (c : Config N d) (R : Routines solver a c) (s : Certified c) : ℕ :=
  (RectangularRidgeStateWork.stopped c s.val).cost+(R.prepare s).cost+
    (RectangularRidgeStateWork.stopped c (RectangularDirectEpochRun.prepare solver a c s).val).cost+5

/-- Both status predicates are the previously compiled finite scalar tests.
The proof-indexed branch below has exactly their computed boolean value. -/
def next (solver : RectangularDirectSolver.Service) (a : Fin d) (c : Config N d) (R : Routines solver a c) (s : Certified c) :
    Implementation (RectangularDirectEpochRun.next solver a c s) :=
  if hs : Stopped c s.val then
    congr (RectangularDirectEpochRun.next_stopped solver a c s hs).symm
      (overhead (pure s 0) ((RectangularRidgeStateWork.stopped c s.val).cost+2))
  else
    if hp : Stopped c (RectangularDirectEpochRun.prepare solver a c s).val then
      congr (by simp only [RectangularDirectEpochRun.next,dif_neg hs,dif_pos hp])
        (overhead (pure (RectangularDirectEpochRun.prepare solver a c s) 0) (overheadCost solver a c R s))
    else
      congr (by simp only [RectangularDirectEpochRun.next,dif_neg hs,dif_neg hp])
        (overhead (R.movement (RectangularDirectEpochRun.prepare solver a c s)
          (RectangularDirectEpochRun.prepare_floor solver a c s) hp) (overheadCost solver a c R s))

def stepBudget (N U V : ℕ) : ℕ := U+V+1000*(N+1)^2

theorem next_bounded (solver : RectangularDirectSolver.Service) (a : Fin d) (c : Config N d) (R : Routines solver a c) (U V : ℕ)
    (hU : ∀s,(R.prepare s).cost ≤ U)
    (hV : ∀s hfloor hnt,Bounded (R.movement s hfloor hnt) V 1)
    (s : Certified c) : Bounded (next solver a c R s) (stepBudget N U V) 1 := by
  have ht:=RectangularRidgeStateWork.stopped_cost c s.val
  have hp:=RectangularRidgeStateWork.stopped_cost c (RectangularDirectEpochRun.prepare solver a c s).val
  have hu:=hU s
  have h1 : N+1 ≤ (N+1)^2 := by nlinarith
  unfold next
  split_ifs with hs hp'
  · apply congr_bounded
    intro z out cost draws he
    have hb:=overhead_bounded (pure s 0)
      ((RectangularRidgeStateWork.stopped c s.val).cost+2) (pure_bounded s 0) z out cost draws he
    unfold stepBudget
    constructor <;> omega
  · apply congr_bounded
    intro z out cost draws he
    have hb:=overhead_bounded (pure (RectangularDirectEpochRun.prepare solver a c s) 0) _
      (pure_bounded _ 0) z out cost draws he
    dsimp only [overheadCost] at hb
    unfold stepBudget
    constructor <;> omega
  · apply congr_bounded
    intro z out cost draws he
    have hb:=overhead_bounded (R.movement (RectangularDirectEpochRun.prepare solver a c s)
      (RectangularDirectEpochRun.prepare_floor solver a c s) hp') _ (hV _ _ _) z out cost draws he
    dsimp only [overheadCost] at hb
    unfold stepBudget
    constructor <;> omega

theorem iterate_eq (solver : RectangularDirectSolver.Service) (a : Fin d) (c : Config N d) (k : ℕ) (s : Certified c) :
    iterateSample (RectangularDirectEpochRun.next solver a c) k s=RectangularDirectEpochRun.run solver a c k s := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>
    simp only [iterateSample,RectangularDirectEpochRun.run]
    rw [funext ih]

def run (solver : RectangularDirectSolver.Service) (a : Fin d) (c : Config N d) (R : Routines solver a c) (k : ℕ) (s : Certified c) :
    Implementation (RectangularDirectEpochRun.run solver a c k s) :=
  congr (iterate_eq solver a c k s) (iterate (next solver a c R) k s)

theorem run_bounded (solver : RectangularDirectSolver.Service) (a : Fin d) (c : Config N d) (R : Routines solver a c) (U V : ℕ)
    (hU : ∀s,(R.prepare s).cost ≤ U)
    (hV : ∀s hfloor hnt,Bounded (R.movement s hfloor hnt) V 1)
    (k : ℕ) (s : Certified c) :
    Bounded (run solver a c R k s) (k*(stepBudget N U V+2)+1) k := by
  exact congr_bounded (iterate_eq solver a c k s) _
    (by simpa only [Nat.mul_one] using iterate_bounded (next solver a c R) (next_bounded solver a c R U V hU hV) k s)

def output (solver : RectangularDirectSolver.Service) (a : Fin d) (c : Config N d) (R : Routines solver a c) :
    Implementation (RectangularDirectEpochRun.output solver a c) :=
  overhead (run solver a c R (count c) (initial c))
    ((RectangularRidgeStateWork.initial c.start).cost+2)

theorem output_bounded (solver : RectangularDirectSolver.Service) (a : Fin d) (c : Config N d) (R : Routines solver a c) (U V : ℕ)
    (hU : ∀s,(R.prepare s).cost ≤ U)
    (hV : ∀s hfloor hnt,Bounded (R.movement s hfloor hnt) V 1) :
    Bounded (output solver a c R)
      ((count c)*(stepBudget N U V+2)+120*(N+1)^3+3) (count c) := by
  have h:=overhead_bounded (run solver a c R (count c) (initial c))
    ((RectangularRidgeStateWork.initial c.start).cost+2) (run_bounded solver a c R U V hU hV _ _)
  have hi:=RectangularRidgeStateWork.initial_cost c.start
  intro z out cost draws he
  have hb:=h z out cost draws he
  constructor <;> omega

end MatrixSpencer.RectangularDirectEpochWork
