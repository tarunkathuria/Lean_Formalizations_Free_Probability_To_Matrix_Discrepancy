import MatrixSpencer.FiniteBranchingTermination
import MatrixSpencer.KSStoppedProgress



open scoped BigOperators
noncomputable section

namespace MatrixSpencer
namespace KSEighthManuscriptBranchingRun

open FiniteBranchingTermination
open KSStoppedProgress (activeIndicator)

variable {State : Type*}

/-- Only nonterminal states take a movement, using the supplied step itself. -/
def Legal (terminal : State → Prop) (step : State → Transition State)
    (s : State) (b : Transition State) : Prop :=
  ¬terminal s ∧ b = step s

/-- Fuel limits the number of actual movements.  A leaf may be a terminal
state or a nonterminal state at the cutoff; neither is conflated with the other. -/
def runTree (terminal : State → Prop) (step : State → Transition State) :
    (N : ℕ) → (s : State) → Tree (fun _ => True) (Legal terminal step) s
  | 0, _ => .leaf trivial
  | N + 1, s => by
    classical
    exact if ht : terminal s then .leaf trivial else
      .node (step s) ⟨ht, rfl⟩
        (fun i => runTree terminal step N ((step s).child i))

/-- Expectation with respect to the weights of the actual run's leaves. -/
def expectation (terminal : State → Prop) (step : State → Transition State)
    (N : ℕ) (s : State) (f : State → ℝ) : ℝ :=
  (runTree terminal step N s).expectation f

/-- The expected number of movements actually taken before absorption/cutoff. -/
def expectedSteps (terminal : State → Prop) (step : State → Transition State)
    (N : ℕ) (s : State) : ℝ :=
  (runTree terminal step N s).expectedCost (fun _ _ => 1)

/-- Noncompletion is evaluated using the supplied terminal predicate. -/
def activeProbability (terminal : State → Prop) (step : State → Transition State)
    (N : ℕ) (s : State) : ℝ :=
  expectation terminal step N s (activeIndicator terminal)

theorem expectation_zero (terminal : State → Prop) (step : State → Transition State)
    (s : State) (f : State → ℝ) : expectation terminal step 0 s f = f s := by
  simp [expectation, runTree, Tree.expectation_leaf]

theorem expectedSteps_zero (terminal : State → Prop) (step : State → Transition State)
    (s : State) : expectedSteps terminal step 0 s = 0 := by
  simp [expectedSteps, runTree, Tree.expectedCost_leaf]

/-- Exact conditional expectation over the supplied transition. -/
theorem expectation_succ (terminal : State → Prop) [DecidablePred terminal]
    (step : State → Transition State) (N : ℕ) (s : State) (f : State → ℝ) :
    expectation terminal step (N+1) s f = if terminal s then f s else
      ∑ i, (step s).weight i * expectation terminal step N ((step s).child i) f := by
  classical
  by_cases ht : terminal s
  · simp [expectation, runTree, ht, Tree.expectation_leaf]
  · simp [expectation, runTree, ht, Tree.expectation_node]

theorem expectedSteps_succ (terminal : State → Prop) [DecidablePred terminal]
    (step : State → Transition State) (N : ℕ) (s : State) :
    expectedSteps terminal step (N+1) s = if terminal s then 0 else
      1 + ∑ i, (step s).weight i * expectedSteps terminal step N ((step s).child i) := by
  classical
  by_cases ht : terminal s
  · simp [expectedSteps, runTree, ht, Tree.expectedCost_leaf]
  · simp [expectedSteps, runTree, ht, Tree.expectedCost_node, mul_add,
      Finset.sum_add_distrib, (step s).weight_sum]

theorem expectation_nonneg (terminal : State → Prop) (step : State → Transition State)
    (N : ℕ) (s : State) (f : State → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ expectation terminal step N s f := by
  apply Finset.sum_nonneg
  intro l _
  exact mul_nonneg (Tree.leafWeight_pos _ l).le (hf _)

theorem expectation_le_const (terminal : State → Prop) (step : State → Transition State)
    (N : ℕ) (s : State) (f : State → ℝ) (B : ℝ) (hf : ∀ a, f a ≤ B) :
    expectation terminal step N s f ≤ B := by
  change (∑ l, (runTree terminal step N s).leafWeight l *
    f ((runTree terminal step N s).leafState l)) ≤ B
  calc
    _ ≤ ∑ l, (runTree terminal step N s).leafWeight l * B :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hf _)
        (Tree.leafWeight_pos _ l).le
    _ = B := by rw [← Finset.sum_mul, Tree.leafWeight_sum, one_mul]

theorem activeProbability_nonneg (terminal : State → Prop) (step : State → Transition State)
    (N : ℕ) (s : State) : 0 ≤ activeProbability terminal step N s :=
  expectation_nonneg terminal step N s _ (KSStoppedProgress.activeIndicator_nonneg terminal)

theorem activeProbability_le_one (terminal : State → Prop) (step : State → Transition State)
    (N : ℕ) (s : State) : activeProbability terminal step N s ≤ 1 :=
  expectation_le_const terminal step N s _ 1 (KSStoppedProgress.activeIndicator_le_one terminal)

/-- Every nonterminal leaf has consumed the entire horizon. -/
theorem horizon_mul_activeProbability_le (terminal : State → Prop)
    (step : State → Transition State) (N : ℕ) (s : State) :
    (N : ℝ) * activeProbability terminal step N s ≤ expectedSteps terminal step N s := by
  classical
  induction N generalizing s with
  | zero => simp [expectedSteps_zero]
  | succ N ih =>
    rw [expectedSteps_succ]
    unfold activeProbability
    rw [expectation_succ]
    by_cases ht : terminal s
    · simp [ht, activeIndicator]
    · simp only [if_neg ht, Nat.cast_add, Nat.cast_one]
      have hi := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
        mul_le_mul_of_nonneg_left (ih ((step s).child i)) ((step s).weight_pos i).le)
      have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
        mul_le_mul_of_nonneg_left (activeProbability_le_one terminal step N ((step s).child i))
          ((step s).weight_pos i).le)
      simp only [mul_one, (step s).weight_sum] at hb
      simp only [activeProbability] at hi hb
      have he : (∑ i, (step s).weight i * ((N : ℝ) *
          expectation terminal step N ((step s).child i) (activeIndicator terminal))) =
          (N : ℝ) * ∑ i, (step s).weight i *
            expectation terminal step N ((step s).child i) (activeIndicator terminal) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [he] at hi
      nlinarith

/-- Positive conditional drift telescopes over the actual weighted run. -/
theorem progress_telescope (terminal : State → Prop) (step : State → Transition State)
    (R : State → ℝ) (c : ℝ)
    (hgain : ∀ s, ¬terminal s → R s+c ≤ ∑ i, (step s).weight i * R ((step s).child i))
    (N : ℕ) (s : State) :
    R s + c * expectedSteps terminal step N s ≤ expectation terminal step N s R := by
  classical
  induction N generalizing s with
  | zero => simp [expectedSteps_zero, expectation_zero]
  | succ N ih =>
    rw [expectedSteps_succ, expectation_succ]
    by_cases ht : terminal s
    · simp [ht]
    · simp only [if_neg ht]
      have hi := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
        mul_le_mul_of_nonneg_left (ih ((step s).child i)) ((step s).weight_pos i).le)
      have he : (∑ i, (step s).weight i *
          (R ((step s).child i) + c * expectedSteps terminal step N ((step s).child i))) =
          (∑ i, (step s).weight i * R ((step s).child i)) +
            c * ∑ i, (step s).weight i * expectedSteps terminal step N ((step s).child i) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [he] at hi
      linarith [hgain s ht]

/-- Expected actual movements are bounded from progress alone. -/
theorem expectedSteps_le (terminal : State → Prop) (step : State → Transition State)
    (R : State → ℝ) {c B : ℝ} (hc : 0 < c)
    (hbound : ∀ s, R s ≤ B)
    (hgain : ∀ s, ¬terminal s →
      R s + c ≤ ∑ i, (step s).weight i * R ((step s).child i))
    (N : ℕ) (s : State) (hzero : 0 ≤ R s) :
    expectedSteps terminal step N s ≤ B / c := by
  have ht := progress_telescope terminal step R c hgain N s
  have hb := expectation_le_const terminal step N s R B hbound
  apply (le_div_iff₀ hc).mpr
  nlinarith

/-- A finite-horizon bound on the probability that the actual state is not
terminal.  No finiteness assumption is placed on the real state space. -/
theorem activeProbability_le (terminal : State → Prop) (step : State → Transition State)
    (R : State → ℝ) {c B : ℝ} (hc : 0 < c)
    (hbound : ∀ s, R s ≤ B)
    (hgain : ∀ s, ¬terminal s →
      R s + c ≤ ∑ i, (step s).weight i * R ((step s).child i))
    (N : ℕ) (hN : 0 < N) (s : State) (hzero : 0 ≤ R s) :
    activeProbability terminal step N s ≤ B / (c * (N : ℝ)) := by
  have hs := expectedSteps_le terminal step R hc hbound hgain N s hzero
  have hp := horizon_mul_activeProbability_le terminal step N s
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ (mul_pos hc hNr)).mpr
  have hh := mul_le_mul_of_nonneg_left (hp.trans hs) hc.le
  rw [mul_div_cancel₀ B (ne_of_gt hc)] at hh
  nlinarith

end KSEighthManuscriptBranchingRun
end MatrixSpencer
