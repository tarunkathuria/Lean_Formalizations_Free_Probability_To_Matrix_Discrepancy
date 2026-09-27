import MatrixSpencer.FiniteProcessMoments

/-!
# Finite-horizon progress for an absorbed KS process

This module proves the stopping estimate from the recursively defined masses of
`FiniteProcessMoments.Process`.  A terminal state is absorbed, while a reachable
nonterminal state has a positive conditional progress gain.  No independence of
successive steps or pointwise monotonicity of progress is assumed.

The concrete KS state, transition kernel, terminal predicate, and local progress
inequality are inputs here.  They are not asserted to follow from local descent
alone.  For a fixed horizon the state space can encode all finite histories.
-/

open scoped BigOperators
noncomputable section

namespace MatrixSpencer
namespace KSStoppedProgress

open FiniteProcessMoments

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The indicator that the process has not yet reached its absorbing set. -/
def activeIndicator (terminal : Ω → Prop) (a : Ω) : ℝ := by
  classical
  exact if terminal a then 0 else 1

/-- The actual nonterminal mass at a given time. -/
def activeProbability (P : Process Ω) (terminal : Ω → Prop) (n : ℕ) : ℝ :=
  P.expectation n (activeIndicator terminal)

/-- The expected number of active steps before a finite horizon. -/
def expectedActiveSteps (P : Process Ω) (terminal : Ω → Prop) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, activeProbability P terminal n

omit [Fintype Ω] [DecidableEq Ω] in
theorem activeIndicator_nonneg (terminal : Ω → Prop) (a : Ω) :
    0 ≤ activeIndicator terminal a := by
  classical
  simp only [activeIndicator]
  split_ifs <;> norm_num

omit [Fintype Ω] [DecidableEq Ω] in
theorem activeIndicator_le_one (terminal : Ω → Prop) (a : Ω) :
    activeIndicator terminal a ≤ 1 := by
  classical
  simp only [activeIndicator]
  split_ifs <;> norm_num

omit [DecidableEq Ω] in
theorem activeProbability_nonneg (P : Process Ω) (terminal : Ω → Prop) (n : ℕ) :
    0 ≤ activeProbability P terminal n :=
  Finset.sum_nonneg fun a _ =>
    mul_nonneg (P.mass_nonneg n a) (activeIndicator_nonneg terminal a)

omit [DecidableEq Ω] in
theorem activeProbability_le_one (P : Process Ω) (terminal : Ω → Prop) (n : ℕ) :
    activeProbability P terminal n ≤ 1 := by
  calc
    _ ≤ P.expectation n (fun _ => 1) :=
      P.expectation_le_of_le_on_support n (fun a _ => activeIndicator_le_one terminal a)
    _ = 1 := P.expectation_const n 1

omit [DecidableEq Ω] in
private theorem expectation_mul (P : Process Ω) (n : ℕ) (c : ℝ) (f : Ω → ℝ) :
    P.expectation n (fun a => c * f a) = c * P.expectation n f := by
  simp only [Process.expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [DecidableEq Ω] in
private theorem conditional_active_le_one (P : Process Ω) (terminal : Ω → Prop)
    (n : ℕ) (a : Ω) : P.conditional n a (activeIndicator terminal) ≤ 1 := by
  calc
    _ ≤ ∑ b, P.transition n a b * 1 :=
      Finset.sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_left (activeIndicator_le_one terminal b)
          (P.transition_nonneg n a b)
    _ = 1 := by simp only [mul_one, P.transition_sum]

/-- Absorption makes the remaining nonterminal mass nonincreasing.  Only
reachable terminal states need the absorbing transition rule. -/
theorem activeProbability_succ_le (P : Process Ω) (terminal : Ω → Prop) (n : ℕ)
    (habsorb : ∀ a, 0 < P.mass n a → terminal a → P.IsAbsorbingAt n a) :
    activeProbability P terminal (n + 1) ≤ activeProbability P terminal n := by
  classical
  unfold activeProbability
  rw [P.expectation_succ]
  apply P.expectation_le_of_le_on_support
  intro a ha
  by_cases ht : terminal a
  · rw [P.conditional_of_absorbing n a (habsorb a ha ht)]
  · simpa only [activeIndicator, if_neg ht] using conditional_active_le_one P terminal n a

/-- The horizon's active probability is no larger than any earlier one. -/
theorem activeProbability_le_of_le (P : Process Ω) (terminal : Ω → Prop) (N : ℕ)
    (habsorb : ∀ n < N, ∀ a, 0 < P.mass n a → terminal a → P.IsAbsorbingAt n a)
    {i j : ℕ} (hij : i ≤ j) (hjN : j ≤ N) :
    activeProbability P terminal j ≤ activeProbability P terminal i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (activeProbability_succ_le P terminal j
      (habsorb j (by omega))).trans (ih (by omega))

/-- A local positive conditional gain becomes a gain proportional to the
current nonterminal probability; absorbed states contribute exactly zero. -/
theorem progress_step (P : Process Ω) (terminal : Ω → Prop) (R : Ω → ℝ)
    (c : ℝ) (n : ℕ)
    (habsorb : ∀ a, 0 < P.mass n a → terminal a → P.IsAbsorbingAt n a)
    (hdrift : ∀ a, 0 < P.mass n a → ¬terminal a →
      R a + c ≤ P.conditional n a R) :
    P.expectation n R + c * activeProbability P terminal n ≤
      P.expectation (n + 1) R := by
  classical
  rw [P.expectation_succ]
  have h : P.expectation n (fun a => R a + c * activeIndicator terminal a) ≤
      P.expectation n (fun a => P.conditional n a R) := by
    apply P.expectation_le_of_le_on_support
    intro a ha
    by_cases ht : terminal a
    · rw [P.conditional_of_absorbing n a (habsorb a ha ht)]
      simp [activeIndicator, ht]
    · simpa [activeIndicator, ht] using hdrift a ha ht
  simpa only [P.expectation_add, expectation_mul, activeProbability] using h

/-- Exact finite telescoping of the conditional gain, before taking any limit. -/
theorem progress_telescope (P : Process Ω) (terminal : Ω → Prop) (R : Ω → ℝ)
    (c : ℝ) (N : ℕ)
    (habsorb : ∀ n < N, ∀ a, 0 < P.mass n a → terminal a → P.IsAbsorbingAt n a)
    (hdrift : ∀ n < N, ∀ a, 0 < P.mass n a → ¬terminal a →
      R a + c ≤ P.conditional n a R) :
    c * expectedActiveSteps P terminal N ≤ P.expectation N R - P.expectation 0 R := by
  have ht := telescope_le (fun n => -P.expectation n R)
    (fun n => c * activeProbability P terminal n) (fun _ => 0) N
    (fun n hn => by
      have h := progress_step P terminal R c n (habsorb n hn) (hdrift n hn)
      dsimp
      linarith)
  simp only [Finset.sum_const_zero, add_zero, ← Finset.mul_sum] at ht
  change c * (∑ n ∈ Finset.range N, activeProbability P terminal n) ≤ _
  linarith

/-- Initial nonnegativity and a horizon upper bound control the expected active
step count.  Bounds are needed only on the corresponding actual supports. -/
theorem expectedActiveSteps_le (P : Process Ω) (terminal : Ω → Prop) (R : Ω → ℝ)
    {c B : ℝ} (hc : 0 < c) (N : ℕ)
    (hzero : ∀ a, 0 < P.mass 0 a → 0 ≤ R a)
    (hbound : ∀ a, 0 < P.mass N a → R a ≤ B)
    (habsorb : ∀ n < N, ∀ a, 0 < P.mass n a → terminal a → P.IsAbsorbingAt n a)
    (hdrift : ∀ n < N, ∀ a, 0 < P.mass n a → ¬terminal a →
      R a + c ≤ P.conditional n a R) :
    expectedActiveSteps P terminal N ≤ B / c := by
  have ht := progress_telescope P terminal R c N habsorb hdrift
  have h0 : 0 ≤ P.expectation 0 R := by
    simpa only [P.expectation_const] using
      P.expectation_le_of_le_on_support 0 hzero
  have hN : P.expectation N R ≤ B := by
    simpa only [P.expectation_const] using
      P.expectation_le_of_le_on_support N hbound
  apply (le_div_iff₀ hc).mpr
  nlinarith

/-- Absorption bounds the horizon's remaining probability by the expected
number of active steps divided by the horizon length. -/
theorem horizon_mul_activeProbability_le (P : Process Ω) (terminal : Ω → Prop) (N : ℕ)
    (habsorb : ∀ n < N, ∀ a, 0 < P.mass n a → terminal a → P.IsAbsorbingAt n a) :
    (N : ℝ) * activeProbability P terminal N ≤ expectedActiveSteps P terminal N := by
  calc
    _ = ∑ _n ∈ Finset.range N, activeProbability P terminal N := by simp
    _ ≤ _ := Finset.sum_le_sum fun n hn =>
      activeProbability_le_of_le P terminal N habsorb
        (Nat.le_of_lt (Finset.mem_range.mp hn)) le_rfl

/-- The finite-horizon noncompletion bound.  It does not assume termination,
and includes any probability mass already absorbed at the initial state. -/
theorem activeProbability_le (P : Process Ω) (terminal : Ω → Prop) (R : Ω → ℝ)
    {c B : ℝ} (hc : 0 < c) (N : ℕ) (hN : 0 < N)
    (hzero : ∀ a, 0 < P.mass 0 a → 0 ≤ R a)
    (hbound : ∀ a, 0 < P.mass N a → R a ≤ B)
    (habsorb : ∀ n < N, ∀ a, 0 < P.mass n a → terminal a → P.IsAbsorbingAt n a)
    (hdrift : ∀ n < N, ∀ a, 0 < P.mass n a → ¬terminal a →
      R a + c ≤ P.conditional n a R) :
    activeProbability P terminal N ≤ B / (c * (N : ℝ)) := by
  have he := expectedActiveSteps_le P terminal R hc N hzero hbound habsorb hdrift
  have hp := horizon_mul_activeProbability_le P terminal N habsorb
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ (mul_pos hc hNr)).mpr
  have hmul := mul_le_mul_of_nonneg_left (hp.trans he) hc.le
  rw [mul_div_cancel₀ B (ne_of_gt hc)] at hmul
  nlinarith

omit [DecidableEq Ω] in
private theorem conditional_const_sub (P : Process Ω) (n : ℕ) (a : Ω)
    (B : ℝ) (U : Ω → ℝ) :
    P.conditional n a (fun b => B - U b) = B - P.conditional n a U := by
  simp only [Process.conditional, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, P.transition_sum, one_mul]

/-- The entropy form: a positive expected decrease of a nonnegative remaining
progress quantity bounds the expected number of active steps. -/
theorem expectedActiveSteps_le_of_decrease (P : Process Ω) (terminal : Ω → Prop)
    (U : Ω → ℝ) {c B : ℝ} (hc : 0 < c) (N : ℕ)
    (hzero : ∀ a, 0 < P.mass 0 a → U a ≤ B)
    (hnonneg : ∀ a, 0 < P.mass N a → 0 ≤ U a)
    (habsorb : ∀ n < N, ∀ a, 0 < P.mass n a → terminal a → P.IsAbsorbingAt n a)
    (hdecrease : ∀ n < N, ∀ a, 0 < P.mass n a → ¬terminal a →
      P.conditional n a U + c ≤ U a) :
    expectedActiveSteps P terminal N ≤ B / c := by
  apply expectedActiveSteps_le P terminal (fun a => B - U a) hc N
  · intro a ha
    exact sub_nonneg.mpr (hzero a ha)
  · intro a ha
    linarith [hnonneg a ha]
  · exact habsorb
  · intro n hn a ha ht
    rw [conditional_const_sub]
    linarith [hdecrease n hn a ha ht]

/-- Finite-horizon noncompletion from an entropy decrease.  The terminal
entropy need not be zero: nonnegativity is sufficient. -/
theorem activeProbability_le_of_decrease (P : Process Ω) (terminal : Ω → Prop)
    (U : Ω → ℝ) {c B : ℝ} (hc : 0 < c) (N : ℕ) (hN : 0 < N)
    (hzero : ∀ a, 0 < P.mass 0 a → U a ≤ B)
    (hnonneg : ∀ a, 0 < P.mass N a → 0 ≤ U a)
    (habsorb : ∀ n < N, ∀ a, 0 < P.mass n a → terminal a → P.IsAbsorbingAt n a)
    (hdecrease : ∀ n < N, ∀ a, 0 < P.mass n a → ¬terminal a →
      P.conditional n a U + c ≤ U a) :
    activeProbability P terminal N ≤ B / (c * (N : ℝ)) := by
  apply activeProbability_le P terminal (fun a => B - U a) hc N hN
  · intro a ha
    exact sub_nonneg.mpr (hzero a ha)
  · intro a ha
    linarith [hnonneg a ha]
  · exact habsorb
  · intro n hn a ha ht
    rw [conditional_const_sub]
    linarith [hdecrease n hn a ha ht]

end KSStoppedProgress
end MatrixSpencer
