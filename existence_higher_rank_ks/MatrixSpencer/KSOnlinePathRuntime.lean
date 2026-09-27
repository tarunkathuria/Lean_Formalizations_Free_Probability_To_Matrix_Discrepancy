import MatrixSpencer.KSEighthManuscriptBranchingRun
import MatrixSpencer.KSFiniteCoinRun
import MatrixSpencer.KSEighthManuscriptRetryCost
import MatrixSpencer.RealRAMJacobiIteration

/-!
# Runtime of one sampled adaptive history

The tree is a probability specification, not an object constructed by the
implementation. `Executes` below follows only the one selected child at each
step. A separate counted implementation supplies the terminal test and child
evaluation. Equality with the original leaf state preserves every original
leaf event and its probability. No tree enumeration is charged or executed.

Arithmetic/address/control costs and the number of finite random draws are
reported separately. A child choice has the original conditional transition
law; implementing random bits is outside this real-RAM bookkeeping layer.
-/

open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSOnlinePathRuntime

open FiniteBranchingTermination
open RealRAM.JacobiIteration (Counted)
attribute [local instance] Classical.propDecidable
variable {State : Type*}

structure Evaluator (terminal : State → Prop) (step : State → Transition State) where
  test : State → Counted Bool
  test_correct : ∀ s, (test s).value = decide (terminal s)
  child : (s : State) → Fin (step s).arity → Counted State
  child_correct : ∀ s i, (child s i).value = (step s).child i

/-- An execution has fuel, a current state, an output, a primitive-operation
count, and a finite-random-draw count. The active constructor evaluates only
its chosen child and passes that computed result to the remaining execution. -/
inductive Executes {terminal : State → Prop} {step : State → Transition State}
    (E : Evaluator terminal step) : ℕ → State → State → ℕ → ℕ → Prop where
  | cutoff (s : State) : Executes E 0 s s 1 0
  | terminal {T : ℕ} {s : State} (ht : (E.test s).value = true) :
      Executes E (T+1) s s ((E.test s).cost+2) 0
  | active {T : ℕ} {s z : State} {k r : ℕ}
      (ht : (E.test s).value = false) (i : Fin (step s).arity) :
      Executes E T (E.child s i).value z k r →
      Executes E (T+1) s z ((E.test s).cost+(E.child s i).cost+k+3) (r+1)

theorem execution_budget {terminal : State → Prop} {step : State → Transition State}
    (E : Evaluator terminal step) {D B : ℕ}
    (hD : ∀ s, (E.test s).cost ≤ D)
    (hB : ∀ s, ¬terminal s → ∀ i, (E.child s i).cost ≤ B)
    {T : ℕ} {s z : State} {k r : ℕ} (h : Executes E T s z k r) :
    k ≤ T*(D+B+3)+D+2 ∧ r ≤ T := by
  induction h with
  | cutoff s => constructor <;> omega
  | @terminal T s ht =>
    have hd := hD s
    constructor <;> omega
  | @active T s z k r ht i hr ih =>
    have hs : ¬terminal s := by
      rw [E.test_correct] at ht
      simpa using ht
    have hd := hD s
    have hb := hB s hs i
    constructor
    · nlinarith [ih.1]
    · omega

def LeafExecutable {terminal : State → Prop} {step : State → Transition State}
    (E : Evaluator terminal step) (T : ℕ) (s : State)
    {legal : State → Transition State → Prop} (t : Tree (fun _ => True) legal s) : Prop :=
  ∀ l : t.Leaves, ∃ k r, Executes E T s (t.leafState l) k r

/-- Every leaf of the original finite distribution admits an online execution
to exactly that leaf's state. The proof does not enumerate sibling paths. -/
theorem leaf_execution {terminal : State → Prop} {step : State → Transition State}
    (E : Evaluator terminal step) (T : ℕ) (s : State)
    (l : (KSEighthManuscriptBranchingRun.runTree terminal step T s).Leaves) :
    ∃ k r, Executes E T s
      ((KSEighthManuscriptBranchingRun.runTree terminal step T s).leafState l) k r := by
  induction T generalizing s with
  | zero => exact ⟨1, 0, Executes.cutoff s⟩
  | succ T ih =>
    revert l
    change LeafExecutable E (T+1) s (KSEighthManuscriptBranchingRun.runTree terminal step (T+1) s)
    simp only [KSEighthManuscriptBranchingRun.runTree]
    split
    · rename_i ht
      intro l
      have he : (E.test s).value = true := by rw [E.test_correct]; simp [ht]
      exact ⟨(E.test s).cost+2, 0, Executes.terminal (T := T) he⟩
    · rename_i ht
      intro l
      obtain ⟨k, r, hr⟩ := ih ((step s).child l.1) l.2
      have he : (E.test s).value = false := by rw [E.test_correct]; simp [ht]
      have hr' : Executes E T (E.child s l.1).value
          ((KSEighthManuscriptBranchingRun.runTree terminal step T
            ((step s).child l.1)).leafState l.2) k r := by
        rwa [E.child_correct]
      exact ⟨_, _, Executes.active he l.1 hr'⟩

theorem leaf_execution_bounded {terminal : State → Prop} {step : State → Transition State}
    (E : Evaluator terminal step) {D B : ℕ}
    (hD : ∀ s, (E.test s).cost ≤ D)
    (hB : ∀ s, ¬terminal s → ∀ i, (E.child s i).cost ≤ B)
    (T : ℕ) (s : State)
    (l : (KSEighthManuscriptBranchingRun.runTree terminal step T s).Leaves) :
    ∃ k r, Executes E T s
      ((KSEighthManuscriptBranchingRun.runTree terminal step T s).leafState l) k r ∧
      k ≤ T*(D+B+3)+D+2 ∧ r ≤ T := by
  obtain ⟨k, r, h⟩ := leaf_execution E T s l
  exact ⟨k, r, h, execution_budget E hD hB h⟩

/-- The same online certificate applies to the full-cube binary run, without
changing its Boolean convention or its exact tree. -/
theorem coin_leaf_execution {terminal : State → Prop} {step : State → Bool → State}
    (E : Evaluator terminal (KSFiniteCoinRun.coinTransition step)) (T : ℕ) (s : State)
    (l : (KSFiniteCoinRun.runTree terminal step T s).Leaves) :
    ∃ k r, Executes E T s ((KSFiniteCoinRun.runTree terminal step T s).leafState l) k r := by
  induction T generalizing s with
  | zero => exact ⟨1, 0, Executes.cutoff s⟩
  | succ T ih =>
    revert l
    change LeafExecutable E (T+1) s (KSFiniteCoinRun.runTree terminal step (T+1) s)
    simp only [KSFiniteCoinRun.runTree]
    split
    · rename_i ht
      intro l
      have he : (E.test s).value = true := by rw [E.test_correct]; simp [ht]
      exact ⟨(E.test s).cost+2, 0, Executes.terminal (T := T) he⟩
    · rename_i ht
      intro l
      obtain ⟨k, r, hr⟩ := ih ((KSFiniteCoinRun.coinTransition step s).child l.1) l.2
      have he : (E.test s).value = false := by rw [E.test_correct]; simp [ht]
      have hr' : Executes E T (E.child s l.1).value
          ((KSFiniteCoinRun.runTree terminal step T
            ((KSFiniteCoinRun.coinTransition step s).child l.1)).leafState l.2) k r := by
        rwa [E.child_correct]
      exact ⟨_, _, Executes.active he l.1 hr'⟩

theorem coin_leaf_execution_bounded {terminal : State → Prop} {step : State → Bool → State}
    (E : Evaluator terminal (KSFiniteCoinRun.coinTransition step)) {D B : ℕ}
    (hD : ∀ s, (E.test s).cost ≤ D)
    (hB : ∀ s, ¬terminal s → ∀ i, (E.child s i).cost ≤ B)
    (T : ℕ) (s : State)
    (l : (KSFiniteCoinRun.runTree terminal step T s).Leaves) :
    ∃ k r, Executes E T s ((KSFiniteCoinRun.runTree terminal step T s).leafState l) k r ∧
      k ≤ T*(D+B+3)+D+2 ∧ r ≤ T := by
  obtain ⟨k, r, h⟩ := coin_leaf_execution E T s l
  exact ⟨k, r, h, execution_budget E hD hB h⟩

end MatrixSpencer.KSOnlinePathRuntime
