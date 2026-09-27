import MatrixSpencer.KSEighthManuscriptBranchingRun

/-!
# Upper drift and event estimates for the actual finite branching run

These lemmas telescope the supplied step's conditional inequalities over its
actual leaf distribution. They do not replace the numerical KS controller's
local estimates, which must be supplied when the run is instantiated.
-/

open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptBranchingRun
open FiniteBranchingTermination
variable {State : Type*}

theorem pathCost_constant {terminal : State → Prop} {legal : State → Transition State → Prop}
    {s : State} (t : Tree terminal legal s) (a : ℝ) (l : t.Leaves) :
    t.pathCost (fun _ _ => a) l = a * t.pathCost (fun _ _ => 1) l := by
  induction t with
  | leaf hs => simp [Tree.pathCost]
  | node b hb children ih =>
    change a + (children l.1).pathCost (fun _ _ => a) l.2 =
      a * (1 + (children l.1).pathCost (fun _ _ => 1) l.2)
    rw [ih l.1 l.2]
    ring

theorem expectedCost_constant {terminal : State → Prop} {legal : State → Transition State → Prop}
    {s : State} (t : Tree terminal legal s) (a : ℝ) :
    t.expectedCost (fun _ _ => a) = a * t.expectedCost (fun _ _ => 1) := by
  simp only [Tree.expectedCost, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [pathCost_constant t a l]
  ring

/-- A per-movement upper drift becomes the drift times actual expected movements. -/
theorem drift_telescope (terminal : State → Prop) (step : State → Transition State)
    (f : State → ℝ) (β : ℝ)
    (hstep : ∀ s, ¬terminal s → ∑ i, (step s).weight i * f ((step s).child i) ≤ f s + β)
    (N : ℕ) (s : State) :
    expectation terminal step N s f ≤ f s + β * expectedSteps terminal step N s := by
  have ht := (runTree terminal step N s).expectation_le_add_cost_of_local f (fun _ _ => β)
    (fun a b hb => by
      obtain ⟨ha, rfl⟩ := hb
      simpa only [← Finset.sum_mul, (step a).weight_sum, one_mul] using hstep a ha)
  rwa [expectedCost_constant] at ht

theorem expectedSteps_nonneg (terminal : State → Prop) (step : State → Transition State)
    (N : ℕ) (s : State) : 0 ≤ expectedSteps terminal step N s :=
  (runTree terminal step N s).expectedCost_nonneg _ (fun _ _ _ _ => zero_le_one)

theorem leaf_invariant (terminal : State → Prop) (step : State → Transition State)
    (I : State → Prop) (hstep : ∀ s, ¬terminal s → I s → ∀ i, I ((step s).child i))
    (N : ℕ) (s : State) (hs : I s) (l : (runTree terminal step N s).Leaves) :
    I ((runTree terminal step N s).leafState l) :=
  (runTree terminal step N s).leaf_invariant I hs (fun a b hb ha => by
    obtain ⟨ht, rfl⟩ := hb
    exact hstep a ht ha) l

def eventProbability (terminal : State → Prop) (step : State → Transition State)
    (N : ℕ) (s : State) (event : State → Prop) : ℝ := by
  classical
  exact expectation terminal step N s (fun a => if event a then 1 else 0)

theorem expectation_mono (terminal : State → Prop) (step : State → Transition State)
    (N : ℕ) (s : State) (f g : State → ℝ) (hfg : ∀ a, f a ≤ g a) :
    expectation terminal step N s f ≤ expectation terminal step N s g :=
  Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (hfg _)
    (Tree.leafWeight_pos _ l).le)

theorem eventProbability_nonneg (terminal : State → Prop) (step : State → Transition State)
    (N : ℕ) (s : State) (event : State → Prop) :
    0 ≤ eventProbability terminal step N s event := by
  classical
  apply expectation_nonneg
  intro a
  split_ifs <;> norm_num

theorem eventProbability_le_one (terminal : State → Prop) (step : State → Transition State)
    (N : ℕ) (s : State) (event : State → Prop) :
    eventProbability terminal step N s event ≤ 1 := by
  classical
  apply expectation_le_const
  intro a
  split_ifs <;> norm_num

/-- Markov's inequality for the actual finite leaf distribution. -/
theorem eventProbability_le_expectation_div (terminal : State → Prop)
    (step : State → Transition State) (N : ℕ) (s : State) (f : State → ℝ)
    (hf : ∀ a, 0 ≤ f a) {B : ℝ} (hB : 0 < B) :
    eventProbability terminal step N s (fun a => B < f a) ≤
      expectation terminal step N s f / B := by
  have hpoint : ∀ a, B * (if B < f a then (1 : ℝ) else 0) ≤ f a := by
    intro a
    split_ifs with h
    · simpa using h.le
    · simpa using hf a
  have h := expectation_mono terminal step N s _ f hpoint
  have he : expectation terminal step N s
      (fun a => B * (if B < f a then (1 : ℝ) else 0)) =
      B * eventProbability terminal step N s (fun a => B < f a) := by
    unfold eventProbability expectation Tree.expectation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he] at h
  exact (le_div_iff₀ hB).mpr (by nlinarith)

theorem eventProbability_union_le (terminal : State → Prop) (step : State → Transition State)
    (N : ℕ) (s : State) (E F : State → Prop) :
    eventProbability terminal step N s (fun a => E a ∨ F a) ≤
      eventProbability terminal step N s E + eventProbability terminal step N s F := by
  classical
  unfold eventProbability expectation Tree.expectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro l _
  have hw := (Tree.leafWeight_pos (runTree terminal step N s) l).le
  by_cases he : E ((runTree terminal step N s).leafState l) <;>
    by_cases hf : F ((runTree terminal step N s).leafState l) <;>
      simp [he, hf] <;> linarith

end MatrixSpencer.KSEighthManuscriptBranchingRun
