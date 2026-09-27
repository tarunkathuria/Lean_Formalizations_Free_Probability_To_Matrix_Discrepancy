import AugmentedHigherRankKS.StateCurves

/-! The compact minimizer reduction. Its local analytic premise is discharged
separately for the actual augmented potential; it is not a signing theorem. -/

open Set
open scoped BigOperators

noncomputable section
namespace AugmentedHigherRankKS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem face_reserve_zero_at_lexicographic_minimum {a R : ℝ}
    (F : EpochState ι → ℝ) {z : EpochState ι}
    (hz : z ∈ epochDomain a R) (hmin : IsMinOn F (epochDomain a R) z)
    (htie : ∀ y ∈ epochDomain a R, F y = F z → totalReserve z ≤ totalReserve y)
    (hdrop : ∀ y ∈ epochDomain a R, ∀ i, |position y i| = 1 →
      F (dropReserve y i) ≤ F y) :
    ∀ i, |position z i| = 1 → reserve z i = 0 := by
  intro i hi
  have hnew := dropReserve_mem hz i hi
  have heq : F (dropReserve z i) = F z :=
    le_antisymm (hdrop z hz i hi) (hmin hnew)
  have ht := htie (dropReserve z i) hnew heq
  rw [totalReserve_dropReserve] at ht
  have hc := (hz i).2.2.2.2.1
  linarith

/-- Generic compact reduction with explicit analytic obligations. The concrete
potential theorem must supply both obligations before exporting existence. -/
theorem exists_exhausted_minimum_of_descent {a R : ℝ}
    (ha : 0 ≤ a) (hR : 0 ≤ R) (x₀ : ι → ℝ)
    (hx : ∀ i, -1 ≤ x₀ i ∧ x₀ i ≤ 1)
    (F : EpochState ι → ℝ) (hF : ContinuousOn F (epochDomain a R))
    (hdrop : ∀ z ∈ epochDomain a R, ∀ i, |position z i| = 1 →
      F (dropReserve z i) ≤ F z)
    (hdescent : ∀ z ∈ epochDomain a R, IsMinOn F (epochDomain a R) z →
      (∀ i, |position z i| = 1 → reserve z i = 0) →
      (∃ i, 0 < reserve z i) → ∃ y ∈ epochDomain a R, F y < F z) :
    ∃ z ∈ epochDomain a R, IsMinOn F (epochDomain a R) z ∧
      (∀ i, reserve z i = 0) ∧ F z ≤ F (initialState a R x₀) := by
  obtain ⟨z, hz, hmin, htie⟩ := exists_lexicographic_minimum ha hR x₀ hx F hF
  have hfaces := face_reserve_zero_at_lexicographic_minimum F hz hmin htie hdrop
  have hall : ∀ i, reserve z i = 0 := by
    intro i
    by_contra hne
    have hc : 0 < reserve z i := lt_of_le_of_ne (hz i).2.2.2.2.1 (Ne.symm hne)
    obtain ⟨y, hy, hlt⟩ := hdescent z hz hmin hfaces ⟨i, hc⟩
    exact (not_lt_of_ge (hmin hy)) hlt
  exact ⟨z, hz, hmin, hall, hmin (initialState_mem ha hR x₀ hx)⟩

end AugmentedHigherRankKS
