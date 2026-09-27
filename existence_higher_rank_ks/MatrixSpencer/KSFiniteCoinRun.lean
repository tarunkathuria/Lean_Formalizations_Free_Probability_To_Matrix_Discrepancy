import MatrixSpencer.FiniteBranchingTermination
import MatrixSpencer.KSStoppedProgress

/-!
# An actual finite binary run on an arbitrary state space

The state space may contain real matrices and need not be finite.  `runTree`
recursively applies the supplied deterministic Boolean step, gives each child
weight one half, and stops at the actual terminal predicate or the horizon.
Its leaves are finite path occurrences, including distinct paths with the same
state.  Terminal states are absorbed by construction.

The cutoff theorem below is a finite distribution theorem.  It does not assert
an infinite-path measure or almost-sure termination, and the concrete KS step's
progress inequality remains an explicit input.
-/

open scoped BigOperators
noncomputable section

namespace MatrixSpencer
namespace KSFiniteCoinRun

open FiniteBranchingTermination
open KSStoppedProgress (activeIndicator)

variable {State : Type*}

/-- The two actual successor states, each with probability one half. -/
def coinTransition (step : State → Bool → State) (s : State) : Transition State where
  arity := 2
  child i := step s (decide (i.val = 0))
  weight _ := 1 / 2
  weight_pos _ := by norm_num
  weight_sum := by norm_num [Fin.sum_univ_two]

theorem coinTransition_average (step : State → Bool → State) (s : State) (f : State → ℝ) :
    (∑ i, (coinTransition step s).weight i * f ((coinTransition step s).child i)) =
      (f (step s false) + f (step s true)) / 2 := by
  change (∑ i : Fin 2, (1 / 2 : ℝ) * f (step s (decide (i.val = 0)))) = _
  norm_num [coinTransition, Fin.sum_univ_two]
  ring

/-- Only nonterminal states take a movement, using the supplied step itself. -/
def Legal (terminal : State → Prop) (step : State → Bool → State)
    (s : State) (b : Transition State) : Prop :=
  ¬terminal s ∧ b = coinTransition step s

/-- Fuel limits the number of actual movements.  A leaf may be a terminal
state or a nonterminal state at the cutoff; neither is conflated with the other. -/
def runTree (terminal : State → Prop) (step : State → Bool → State) :
    (N : ℕ) → (s : State) → Tree (fun _ => True) (Legal terminal step) s
  | 0, _ => .leaf trivial
  | N + 1, s => by
    classical
    exact if ht : terminal s then .leaf trivial else
      .node (coinTransition step s) ⟨ht, rfl⟩
        (fun i => runTree terminal step N ((coinTransition step s).child i))

/-- Expectation with respect to the weights of the actual run's leaves. -/
def expectation (terminal : State → Prop) (step : State → Bool → State)
    (N : ℕ) (s : State) (f : State → ℝ) : ℝ :=
  (runTree terminal step N s).expectation f

/-- The expected number of movements actually taken before absorption/cutoff. -/
def expectedSteps (terminal : State → Prop) (step : State → Bool → State)
    (N : ℕ) (s : State) : ℝ :=
  (runTree terminal step N s).expectedCost (fun _ _ => 1)

/-- Noncompletion is evaluated using the supplied terminal predicate. -/
def activeProbability (terminal : State → Prop) (step : State → Bool → State)
    (N : ℕ) (s : State) : ℝ :=
  expectation terminal step N s (activeIndicator terminal)

theorem expectation_zero (terminal : State → Prop) (step : State → Bool → State)
    (s : State) (f : State → ℝ) : expectation terminal step 0 s f = f s := by
  simp [expectation, runTree, Tree.expectation_leaf]

theorem expectedSteps_zero (terminal : State → Prop) (step : State → Bool → State)
    (s : State) : expectedSteps terminal step 0 s = 0 := by
  simp [expectedSteps, runTree, Tree.expectedCost_leaf]

/-- Finite conditional expectation is exactly the average of the two actual
successor runs; already terminal states have a deterministic constant run. -/
theorem expectation_succ (terminal : State → Prop) [DecidablePred terminal]
    (step : State → Bool → State)
    (N : ℕ) (s : State) (f : State → ℝ) :
    expectation terminal step (N + 1) s f =
      if terminal s then f s else
        (expectation terminal step N (step s false) f +
          expectation terminal step N (step s true) f) / 2 := by
  classical
  by_cases ht : terminal s
  · simp [expectation, runTree, ht, Tree.expectation_leaf]
  · simp only [expectation, runTree, dif_neg ht, if_neg ht, Tree.expectation_node]
    exact coinTransition_average step s (fun a => (runTree terminal step N a).expectation f)

theorem expectedSteps_succ (terminal : State → Prop) [DecidablePred terminal]
    (step : State → Bool → State)
    (N : ℕ) (s : State) :
    expectedSteps terminal step (N + 1) s =
      if terminal s then 0 else 1 +
        (expectedSteps terminal step N (step s false) +
          expectedSteps terminal step N (step s true)) / 2 := by
  classical
  by_cases ht : terminal s
  · simp [expectedSteps, runTree, ht, Tree.expectedCost_leaf]
  · simp only [expectedSteps, runTree, dif_neg ht, if_neg ht, Tree.expectedCost_node]
    rw [coinTransition_average step s
      (fun a => 1 + (runTree terminal step N a).expectedCost (fun _ _ => 1))]
    ring

theorem expectation_nonneg (terminal : State → Prop) (step : State → Bool → State)
    (N : ℕ) (s : State) (f : State → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ expectation terminal step N s f := by
  apply Finset.sum_nonneg
  intro l _
  exact mul_nonneg (Tree.leafWeight_pos _ l).le (hf _)

theorem expectation_le_const (terminal : State → Prop) (step : State → Bool → State)
    (N : ℕ) (s : State) (f : State → ℝ) (B : ℝ) (hf : ∀ a, f a ≤ B) :
    expectation terminal step N s f ≤ B := by
  change (∑ l, (runTree terminal step N s).leafWeight l *
    f ((runTree terminal step N s).leafState l)) ≤ B
  calc
    _ ≤ ∑ l, (runTree terminal step N s).leafWeight l * B :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hf _)
        (Tree.leafWeight_pos _ l).le
    _ = B := by rw [← Finset.sum_mul, Tree.leafWeight_sum, one_mul]

theorem activeProbability_nonneg (terminal : State → Prop) (step : State → Bool → State)
    (N : ℕ) (s : State) : 0 ≤ activeProbability terminal step N s :=
  expectation_nonneg terminal step N s _ (KSStoppedProgress.activeIndicator_nonneg terminal)

theorem activeProbability_le_one (terminal : State → Prop) (step : State → Bool → State)
    (N : ℕ) (s : State) : activeProbability terminal step N s ≤ 1 :=
  expectation_le_const terminal step N s _ 1 (KSStoppedProgress.activeIndicator_le_one terminal)

/-- A remaining active leaf has consumed the full horizon.  The inequality is
proved for the actual truncated tree, not assumed as a stopping-time law. -/
theorem horizon_mul_activeProbability_le (terminal : State → Prop)
    (step : State → Bool → State) (N : ℕ) (s : State) :
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
      have h₁ := ih (step s false)
      have h₂ := ih (step s true)
      have hb₁ := activeProbability_le_one terminal step N (step s false)
      have hb₂ := activeProbability_le_one terminal step N (step s true)
      unfold activeProbability at h₁ h₂ hb₁ hb₂
      nlinarith

/-- Positive drift telescopes over the concrete coin-run tree. -/
theorem progress_telescope (terminal : State → Prop) (step : State → Bool → State)
    (R : State → ℝ) (c : ℝ)
    (hgain : ∀ s, ¬terminal s →
      R s + c ≤ (R (step s false) + R (step s true)) / 2)
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
      nlinarith [ih (step s false), ih (step s true), hgain s ht]

/-- Expected actual movements are bounded from progress alone. -/
theorem expectedSteps_le (terminal : State → Prop) (step : State → Bool → State)
    (R : State → ℝ) {c B : ℝ} (hc : 0 < c)
    (hbound : ∀ s, R s ≤ B)
    (hgain : ∀ s, ¬terminal s →
      R s + c ≤ (R (step s false) + R (step s true)) / 2)
    (N : ℕ) (s : State) (hzero : 0 ≤ R s) :
    expectedSteps terminal step N s ≤ B / c := by
  have ht := progress_telescope terminal step R c hgain N s
  have hb := expectation_le_const terminal step N s R B hbound
  apply (le_div_iff₀ hc).mpr
  nlinarith

/-- A finite-horizon bound on the probability that the actual state is not
terminal.  No finiteness assumption is placed on the real state space. -/
theorem activeProbability_le (terminal : State → Prop) (step : State → Bool → State)
    (R : State → ℝ) {c B : ℝ} (hc : 0 < c)
    (hbound : ∀ s, R s ≤ B)
    (hgain : ∀ s, ¬terminal s →
      R s + c ≤ (R (step s false) + R (step s true)) / 2)
    (N : ℕ) (hN : 0 < N) (s : State) (hzero : 0 ≤ R s) :
    activeProbability terminal step N s ≤ B / (c * (N : ℝ)) := by
  have hs := expectedSteps_le terminal step R hc hbound hgain N s hzero
  have hp := horizon_mul_activeProbability_le terminal step N s
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ (mul_pos hc hNr)).mpr
  have hh := mul_le_mul_of_nonneg_left (hp.trans hs) hc.le
  rw [mul_div_cancel₀ B (ne_of_gt hc)] at hh
  nlinarith

end KSFiniteCoinRun
end MatrixSpencer
