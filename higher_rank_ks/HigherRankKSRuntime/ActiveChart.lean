import HigherRankKSRuntime.ActiveEnumeration

/-! Exact reindexing of the actual source and centered value-query chart. -/
noncomputable section
open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.ActiveEnumeration
open AugmentedHigherRankKS
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- A relabeling preserves the complete nonlinear source before optimization. -/
theorem source_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) :
    source A β c S = source (fun j => A (e j)) β (fun j => c (e j)) S :=
  (e.sum_comp (fun i => c i • sourceTerm β (A i) S)).symm

theorem potential_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : ι → Matrix n n ℂ) (β θ : ℝ) (c : ι → ℝ) :
    potential H A β c θ = potential H (fun j => A (e j)) β (fun j => c (e j)) θ := by
  have he : objective H A β c θ = objective H (fun j => A (e j)) β (fun j => c (e j)) θ := by
    funext S
    unfold objective
    rw [source_reindex e]
  simp only [potential,he]

theorem active_source_eq (A : Fin N → Matrix n n ℂ) (β : ℝ)
    {a R : ℝ} {z : EpochState (Fin N)} (hz : z ∈ epochDomain a R)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) :
    source A β (reserve z) S = source (restrictedAtoms A z) β (restrictedReserve z) S := by
  rw [source_eq_live A β (positiveReserves z) (reserve z) (reserve_zero_of_not_positive hz)]
  exact source_reindex (activeEquiv z) _ _ _ _

theorem active_potential_eq (A : Fin N → Matrix n n ℂ) (β θ : ℝ)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    {a R : ℝ} {z : EpochState (Fin N)} (hz : z ∈ epochDomain a R) :
    potential H A β (reserve z) θ = potential H (restrictedAtoms A z) β (restrictedReserve z) θ := by
  rw [potential_eq_restrict H A β θ (positiveReserves z) (reserve z) (reserve_zero_of_not_positive hz)]
  exact potential_reindex (activeEquiv z) _ _ _ _ _

theorem restricted_atoms_subisotropic (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1) (z : EpochState (Fin N)) :
    ∑ j, restrictedAtoms A z j ≤ 1 := by
  have he := (activeEquiv z).sum_comp (fun i : ActiveOwners z => A i)
  change (∑ j, A (activeEquiv z j)) ≤ 1
  rw [he,Finset.sum_coe_sort]
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => (hA i).nonneg)).trans hsum

theorem force_sum_eq (A : Fin N → Matrix n n ℂ) (z : EpochState (Fin N))
    (v : EuclideanSpace ℝ (Fin (count z))) :
    (∑ i, extend z v i • forceAtom (position z i) (A i)) =
      ∑ j, v j • forceAtom (restrictedPosition z j) (restrictedAtoms A z j) := by
  rw [sum_active z _ (by intro i hi; rw [extend_inactive z v i hi,zero_smul])]
  have he := (activeEquiv z).sum_comp (fun i : ActiveOwners z =>
    extend z v i • forceAtom (position z i) (A i))
  rw [← he]
  simp only [extend_index,restrictedPosition,restrictedAtoms]
  rfl

/-- The scalar oracle chart is exactly the potential of the full original-owner update. -/
theorem movement_chart_eq (A : Fin N → Matrix n n ℂ) (β θ : ℝ)
    (x₀ : Fin N → ℝ) {a R : ℝ} {z : EpochState (Fin N)} (hz : z ∈ epochDomain a R)
    (v : EuclideanSpace ℝ (Fin (count z))) (t : ℝ) :
    epochPotential A β θ x₀ (movement a z (extend z v) t) =
      potential (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z) +
        t • ∑ j, v j • forceAtom (restrictedPosition z j) (restrictedAtoms A z j))
        (restrictedAtoms A z) β (fun j => restrictedReserve z j-a*t^2*(v j)^2) θ := by
  have he := epochPotential_movement_eq A β θ x₀ hz
    (fun i : ActiveOwners z => v ((activeEquiv z).symm i)) t
  change epochPotential A β θ x₀ (movement a z (extend z v) t) = _ at he
  rw [he,potential_reindex (activeEquiv z)]
  have hsum := (activeEquiv z).sum_comp (fun i : ActiveOwners z =>
    v ((activeEquiv z).symm i) • forceAtom (position z i) (A i))
  rw [← hsum]
  have hcancel (j : Fin (count z)) : (activeEquiv z).symm (activeEquiv z j) = j :=
    (activeEquiv z).symm_apply_apply j
  congr 1
  · congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hcancel j]
    rfl
  · funext j
    rw [hcancel j]
    rfl
end HigherRankKSRuntime.ActiveEnumeration
