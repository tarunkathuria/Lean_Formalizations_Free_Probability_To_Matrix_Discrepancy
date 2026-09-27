import AugmentedHigherRankKS.EpochPotential

/-! The reserve tie-break removes zero atoms as well as completed faces. -/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

@[simp] theorem sourceTerm_zero_atom (β : ℝ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) : sourceTerm β 0 S = 0 := by
  simp [sourceTerm, HigherRankKS.sourceTerm, HigherRankKS.sourceBlock]

theorem source_congr_weights_on_nonzero (A : ι → Matrix n n ℂ) (β : ℝ)
    {c d : ι → ℝ} (hcd : ∀ i, A i ≠ 0 → c i = d i)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) : source A β c S = source A β d S := by
  unfold source
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hAi : A i = 0
  · simp [hAi]
  · rw [hcd i hAi]

theorem epochPotential_congr_on_nonzero (A : ι → Matrix n n ℂ) (β θ : ℝ)
    (x₀ : ι → ℝ) {z w : EpochState ι}
    (hx : ∀ i, A i ≠ 0 → position z i = position w i)
    (hs : ∀ i, A i ≠ 0 → spent z i = spent w i)
    (hc : ∀ i, A i ≠ 0 → reserve z i = reserve w i) :
    epochPotential A β θ x₀ z = epochPotential A β θ x₀ w := by
  have hH : discrepancy A x₀ z = discrepancy A x₀ w := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hAi : A i = 0
    · simp [hAi]
    · rw [hx i hAi]
  have hK : budgetCenter A x₀ z = budgetCenter A x₀ w := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hAi : A i = 0
    · simp [hAi]
    · rw [hx i hAi, hs i hAi]
  unfold epochPotential potential
  rw [hH, hK]
  have ho : objective (augmentedCenter (discrepancy A x₀ w) (budgetCenter A x₀ w))
      A β (reserve z) θ = objective
      (augmentedCenter (discrepancy A x₀ w) (budgetCenter A x₀ w))
      A β (reserve w) θ := by
    funext S
    unfold objective
    rw [source_congr_weights_on_nonzero A β hc S]
  rw [ho]

/-- A zero owner cannot retain covariance at a lexicographic minimizer.
Its reserve is withdrawn with the ledger charge, so feasibility is preserved. -/
theorem zero_atom_reserve_zero_at_minimum [DecidableEq ι]
    (A : ι → Matrix n n ℂ) (β θ : ℝ) (x₀ : ι → ℝ)
    {a R : ℝ} (ha : 0 < a) {z : EpochState ι}
    (hz : z ∈ epochDomain a R)
    (htie : ∀ y ∈ epochDomain a R,
      epochPotential A β θ x₀ y = epochPotential A β θ x₀ z →
        totalReserve z ≤ totalReserve y) :
    ∀ i, A i = 0 → reserve z i = 0 := by
  intro i hAi
  let u : ι → ℝ := fun j => if j = i then reserve z i else 0
  have hu : ∀ j, 0 ≤ u j ∧ u j ≤ reserve z j := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [u, if_pos rfl]
      exact ⟨(hz i).2.2.2.2.1, le_rfl⟩
    · simp only [u, if_neg hji]
      exact ⟨le_rfl, (hz j).2.2.2.2.1⟩
  have hp := preparation_mem ha hz u hu
  have heq : epochPotential A β θ x₀ (preparation a z u) =
      epochPotential A β θ x₀ z := by
    apply epochPotential_congr_on_nonzero
    · intro j hj; rfl
    · intro j hj
      have hji : j ≠ i := by rintro rfl; exact hj hAi
      simp [preparation, spent, u, hji]
    · intro j hj
      have hji : j ≠ i := by rintro rfl; exact hj hAi
      simp [preparation, reserve, u, hji]
  have ht := htie _ hp heq
  rw [totalReserve_preparation] at ht
  have hsum : ∑ j, u j = reserve z i := by simp [u]
  rw [hsum] at ht
  have hc := (hz i).2.2.2.2.1
  linarith

end AugmentedHigherRankKS
