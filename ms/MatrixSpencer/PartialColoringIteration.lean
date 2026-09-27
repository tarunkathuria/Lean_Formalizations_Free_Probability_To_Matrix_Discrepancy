import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Finite iteration of partial-coloring phases

This is a conditional iteration theorem on an arbitrary state space. Each
phase must actually supply a permitted successor with an invariant, geometric
live-count decrease, and the stated scalar cost. No Matrix Spencer phase or
epoch existence assertion is assumed to have been proved by this module.
-/

namespace MatrixSpencer
namespace PartialColoringIteration

/-- A geometric live-count reduction gives a linear decrease of its square root. -/
lemma sqrt_geometric_le {k k' : ℕ} {β : ℝ} (_hβ : 0 < β) (hβone : β ≤ 1)
    (hshrink : (k' : ℝ) ≤ (1 - β) * k) :
    Real.sqrt k' ≤ (1 - β / 2) * Real.sqrt k := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk' : (0 : ℝ) ≤ k' := Nat.cast_nonneg k'
  have hcoeff : 0 ≤ 1 - β / 2 := by linarith
  have hsq : (Real.sqrt k') ^ 2 ≤ ((1 - β / 2) * Real.sqrt k) ^ 2 := by
    rw [Real.sq_sqrt hk', mul_pow, Real.sq_sqrt hk]
    nlinarith [mul_nonneg hk (sq_nonneg β)]
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hcoeff (Real.sqrt_nonneg _))).mp hsq

/-- The natural live count strictly decreases at every nonterminal phase. -/
lemma live_lt_of_geometric {k k' : ℕ} {β : ℝ} (hβ : 0 < β) (hk : 0 < k)
    (hshrink : (k' : ℝ) ≤ (1 - β) * k) : k' < k := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hlt : (k' : ℝ) < k := by nlinarith
  exact Nat.cast_lt.mp hlt

/-- A single phase can be charged to the decrease of the remaining square-root budget. -/
lemma phase_cost_le_budget_drop {k k' : ℕ} {β B : ℝ}
    (hβ : 0 < β) (hβone : β ≤ 1) (hB : 0 ≤ B)
    (hshrink : (k' : ℝ) ≤ (1 - β) * k) :
    B * Real.sqrt k + (2 * B / β) * Real.sqrt k' ≤ (2 * B / β) * Real.sqrt k := by
  have h := mul_le_mul_of_nonneg_left (sqrt_geometric_le hβ hβone hshrink)
    (show 0 ≤ 2 * B / β from div_nonneg (mul_nonneg (by norm_num) hB) hβ.le)
  have he : B * Real.sqrt k + (2 * B / β) * ((1 - β / 2) * Real.sqrt k) =
      (2 * B / β) * Real.sqrt k := by
    field_simp
    ring
  linarith

/-- Iterating actual admissible phases terminates while preserving the invariant and cost budget. -/
theorem exists_terminal_of_phases {State : Type*}
    (live : State → ℕ) (potential : State → ℝ) (invariant : State → Prop)
    (step : State → State → Prop) {β B : ℝ}
    (hβ : 0 < β) (hβone : β ≤ 1) (hB : 0 ≤ B)
    (phase : ∀ s, invariant s → 0 < live s →
      ∃ s', step s s' ∧ invariant s' ∧
        (live s' : ℝ) ≤ (1 - β) * live s ∧
        potential s' ≤ potential s + B * Real.sqrt (live s))
    (start : State) (hstart : invariant start) :
    ∃ finish, Relation.ReflTransGen step start finish ∧ invariant finish ∧ live finish = 0 ∧
      potential finish ≤ potential start + (2 * B / β) * Real.sqrt (live start) := by
  have hind : ∀ s, invariant s → ∃ finish, Relation.ReflTransGen step s finish ∧
      invariant finish ∧ live finish = 0 ∧
      potential finish ≤ potential s + (2 * B / β) * Real.sqrt (live s) := by
    intro s
    induction s using (measure live).wf.induction with
    | h s ih =>
      intro hInv
      by_cases hz : live s = 0
      · refine ⟨s, Relation.ReflTransGen.refl, hInv, hz, ?_⟩
        simp only [hz, Nat.cast_zero, Real.sqrt_zero, mul_zero, add_zero, le_refl]
      · have hk : 0 < live s := Nat.pos_of_ne_zero hz
        obtain ⟨s', hstep, hInv', hshrink, hcost⟩ := phase s hInv hk
        have hlt : live s' < live s := live_lt_of_geometric hβ hk hshrink
        obtain ⟨finish, hreach, hInvf, hzero, hbound⟩ := ih s' hlt hInv'
        refine ⟨finish, hreach.head hstep, hInvf, hzero, ?_⟩
        have hdrop := phase_cost_le_budget_drop hβ hβone hB hshrink
        linarith
  exact hind start hstart

/-- The same iteration theorem when no additional invariant needs to be carried. -/
theorem exists_terminal {State : Type*} (live : State → ℕ) (potential : State → ℝ)
    (step : State → State → Prop) {β B : ℝ}
    (hβ : 0 < β) (hβone : β ≤ 1) (hB : 0 ≤ B)
    (phase : ∀ s, 0 < live s → ∃ s', step s s' ∧
      (live s' : ℝ) ≤ (1 - β) * live s ∧
      potential s' ≤ potential s + B * Real.sqrt (live s))
    (start : State) :
    ∃ finish, Relation.ReflTransGen step start finish ∧ live finish = 0 ∧
      potential finish ≤ potential start + (2 * B / β) * Real.sqrt (live start) := by
  have hphase : ∀ s, True → 0 < live s → ∃ s', step s s' ∧ True ∧
      (live s' : ℝ) ≤ (1 - β) * live s ∧
      potential s' ≤ potential s + B * Real.sqrt (live s) := by
    intro s _ hk
    obtain ⟨s', hs', hk', hcost⟩ := phase s hk
    exact ⟨s', hs', trivial, hk', hcost⟩
  obtain ⟨finish, hreach, _, hz, hbound⟩ :=
    exists_terminal_of_phases live potential (fun _ => True) step hβ hβone hB hphase start trivial
  exact ⟨finish, hreach, hz, hbound⟩

end PartialColoringIteration
end MatrixSpencer
