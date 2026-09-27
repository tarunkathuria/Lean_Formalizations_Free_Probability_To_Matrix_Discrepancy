import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Removing a positive regularization parameter on a finite output set

The local analysis may require a strictly positive parameter `θ`.  The
existence proof does not set that parameter to zero: it first minimizes the
final cost over the finite collection of outputs, then proves that the
minimum satisfies the limiting bound.  The output is allowed to depend on
`θ` in every hypothesis below.

These are internal finite-choice and real-arithmetic lemmas.  Their cost
estimate hypotheses must still be supplied by the analytic proof.
-/

open Set

noncomputable section

namespace HigherRankKS.RegularizationLimit

/-- An upper bound with arbitrarily small positive regularization implies
the limiting upper bound.  The error coefficient may be any real number. -/
theorem le_of_forall_positive_regularization {m C R : ℝ}
    (hbound : ∀ θ : ℝ, 0 < θ → m ≤ C + θ * R) : m ≤ C := by
  by_contra hnot
  have hgap : 0 < m - C := sub_pos.mpr (lt_of_not_ge hnot)
  let θ : ℝ := (m - C) / (2 * (|R| + 1))
  have hden : 0 < 2 * (|R| + 1) := by positivity
  have hθ : 0 < θ := div_pos hgap hden
  have hproduct : θ * (2 * (|R| + 1)) = m - C :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  have hupper := hbound θ hθ
  have habs := mul_le_mul_of_nonneg_left (le_abs_self R) hθ.le
  nlinarith

/-- Minimize the cost over the finite output set before taking the bound
to its limit.  No continuous optimizer or common output for all `θ` is
assumed. -/
theorem exists_minimum_le_of_regularized_bounds {α : Type*}
    (S : Set α) (hfinite : S.Finite) (hne : S.Nonempty)
    (cost : α → ℝ) (C R : ℝ)
    (hbound : ∀ θ : ℝ, 0 < θ → ∃ s ∈ S, cost s ≤ C + θ * R) :
    ∃ s ∈ S, (∀ t ∈ S, cost s ≤ cost t) ∧ cost s ≤ C := by
  obtain ⟨s, hs, hmin⟩ := Set.exists_min_image S cost hfinite hne
  refine ⟨s, hs, hmin, le_of_forall_positive_regularization (R := R) ?_⟩
  intro θ hθ
  obtain ⟨t, ht, hcost⟩ := hbound θ hθ
  exact (hmin t ht).trans hcost

/-- Type-valued version of finite-output regularization removal. -/
theorem exists_le_of_regularized_bounds {α : Type*} [Finite α] [Nonempty α]
    (cost : α → ℝ) (C R : ℝ)
    (hbound : ∀ θ : ℝ, 0 < θ → ∃ s : α, cost s ≤ C + θ * R) :
    ∃ s : α, cost s ≤ C := by
  obtain ⟨s, _, _, hs⟩ := exists_minimum_le_of_regularized_bounds
    (Set.univ : Set α) Set.finite_univ Set.univ_nonempty cost C R (by
      intro θ hθ
      obtain ⟨s, hs⟩ := hbound θ hθ
      exact ⟨s, Set.mem_univ s, hs⟩)
  exact ⟨s, hs⟩

/-- A Boolean choice gives a literal real sign for every original label. -/
def realSigning {N : ℕ} (b : Fin N → Bool) (i : Fin N) : ℝ :=
  if b i then 1 else -1

theorem realSigning_is_sign {N : ℕ} (b : Fin N → Bool) (i : Fin N) :
    realSigning b i = 1 ∨ realSigning b i = -1 := by
  unfold realSigning
  split <;> simp

/-- Every literal real signing is represented by a Boolean signing. -/
theorem exists_bool_representation {N : ℕ} (s : Fin N → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) :
    ∃ b : Fin N → Bool, realSigning b = s := by
  classical
  refine ⟨fun i => decide (s i = 1), ?_⟩
  funext i
  by_cases hi : s i = 1
  · simp [realSigning, hi]
  · have hneg : s i = -1 := (hs i).resolve_left hi
    norm_num [realSigning, hneg]

/-- The regularized witnesses can be literal real signings, chosen anew
for each positive parameter.  Some literal real signing achieves the
unregularized cost bound. -/
theorem exists_real_signing_le_of_regularized_bounds {N : ℕ}
    (cost : (Fin N → ℝ) → ℝ) (C R : ℝ)
    (hbound : ∀ θ : ℝ, 0 < θ → ∃ s : Fin N → ℝ,
      (∀ i, s i = 1 ∨ s i = -1) ∧ cost s ≤ C + θ * R) :
    ∃ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧ cost s ≤ C := by
  obtain ⟨b, hb⟩ := exists_le_of_regularized_bounds
    (fun b : Fin N → Bool => cost (realSigning b)) C R (by
      intro θ hθ
      obtain ⟨s, hs, hcost⟩ := hbound θ hθ
      obtain ⟨b, hb⟩ := exists_bool_representation s hs
      refine ⟨b, ?_⟩
      simpa only [hb] using hcost)
  exact ⟨realSigning b, realSigning_is_sign b, hb⟩

end HigherRankKS.RegularizationLimit
