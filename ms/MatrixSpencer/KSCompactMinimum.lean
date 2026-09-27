import MatrixSpencer.KSStatement
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The global minimum and maximal-frozen-coordinate arguments

The truncated potential need not be continuous when an owner is deleted.
The first lemma proves attainment from its finite continuous closed-face
majorants. This is an explicit alternative to proving lower semicontinuity.
The second lemma is the finite-rank part of both signing arguments.
Neither lemma asserts any analytic property of a Kadison–Singer potential.
-/

open Set

namespace MatrixSpencer

variable {X J : Type*} [TopologicalSpace X] [Finite J]

/-- A function represented pointwise by finitely many continuous compact
branch majorants attains its global minimum. Branches may jump down where
their domains meet; no continuity of the represented function is assumed. -/
theorem ks_exists_minimum_of_compact_branches
    (D : Set X) (K : J → Set X) (f : X → ℝ) (F : J → X → ℝ)
    (hne : D.Nonempty) (hcompact : ∀ j, IsCompact (K j))
    (hcont : ∀ j, ContinuousOn (F j) (K j))
    (hsubset : ∀ j, K j ⊆ D)
    (hmajorant : ∀ j, ∀ x ∈ K j, f x ≤ F j x)
    (hexact : ∀ x ∈ D, ∃ j, x ∈ K j ∧ F j x = f x) :
    ∃ x ∈ D, IsMinOn f D x := by
  let V : Set ℝ := ⋃ j, F j '' K j
  have hVcompact : IsCompact V :=
    isCompact_iUnion (fun j => (hcompact j).image_of_continuousOn (hcont j))
  have hVne : V.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨j, hj, he⟩ := hexact x hx
    exact ⟨F j x, mem_iUnion.mpr ⟨j, ⟨x, hj, rfl⟩⟩⟩
  obtain ⟨r, hr, hmin⟩ := hVcompact.exists_isMinOn hVne continuous_id.continuousOn
  obtain ⟨j, x, hx, hxr⟩ := mem_iUnion.mp hr
  refine ⟨x, hsubset j hx, ?_⟩
  intro y hy
  obtain ⟨k, hk, hky⟩ := hexact y hy
  have hFy : F k y ∈ V := mem_iUnion.mpr ⟨k, ⟨y, hk, rfl⟩⟩
  exact (hmajorant j x hx).trans (hxr ▸ (hmin hFy : r ≤ F k y) |>.trans_eq hky)

/-- Among global minima a bounded natural-number rank has a maximum. -/
theorem ks_exists_minimum_maximal_rank
    (D : Set X) (f : X → ℝ) (rank : X → ℕ) (N : ℕ)
    (hmin : ∃ x ∈ D, IsMinOn f D x)
    (hrank : ∀ x ∈ D, rank x ≤ N) :
    ∃ x ∈ D, IsMinOn f D x ∧
      ∀ y ∈ D, IsMinOn f D y → rank y ≤ rank x := by
  let M := {x ∈ D | IsMinOn f D x}
  have hMne : M.Nonempty := by
    obtain ⟨x, hx, hm⟩ := hmin
    exact ⟨x, hx, hm⟩
  have hfinite : (rank '' M).Finite := (Set.finite_le_nat N).subset (by
    rintro _ ⟨x, hx, rfl⟩
    exact hrank x hx.1)
  obtain ⟨r, hr, hmax⟩ := Set.exists_max_image (rank '' M) id hfinite (hMne.image rank)
  obtain ⟨x, hx, hrx⟩ := hr
  refine ⟨x, hx.1, hx.2, ?_⟩
  intro y hy hm
  have h := hmax (rank y) ⟨y, ⟨hy, hm⟩, rfl⟩
  simpa only [id_eq, ← hrx] using h

/-- Exact abstract last step of both proofs: every nonterminal minimizer
either retires a coordinate without increasing its value, or has a strictly
smaller feasible value. The analytic alternatives are supplied separately. -/
theorem ks_exists_terminal_minimum
    (D : Set X) (f : X → ℝ) (rank : X → ℕ) (N : ℕ) (terminal : X → Prop)
    (hmin : ∃ x ∈ D, IsMinOn f D x)
    (hrank : ∀ x ∈ D, rank x ≤ N)
    (hstep : ∀ x ∈ D, IsMinOn f D x → ¬ terminal x →
      (∃ y ∈ D, f y ≤ f x ∧ rank x < rank y) ∨
      (∃ y ∈ D, f y < f x)) :
    ∃ x ∈ D, terminal x ∧ IsMinOn f D x := by
  obtain ⟨x, hx, hm, hmax⟩ := ks_exists_minimum_maximal_rank D f rank N hmin hrank
  refine ⟨x, hx, ?_, hm⟩
  by_contra hn
  rcases hstep x hx hm hn with ⟨y, hy, hval, hmore⟩ | ⟨y, hy, hless⟩
  · have hym : IsMinOn f D y := fun z hz => hval.trans (hm hz)
    exact (not_lt_of_ge (hmax y hy hym)) hmore
  · exact (not_lt_of_ge (hm hy)) hless

end MatrixSpencer
