import AugmentedHigherRankKS.FourBlockInitialPotential
import AugmentedHigherRankKS.BudgetOrder

/-! Exact epoch bounds and removal of the auxiliary density regularization. -/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

theorem discrepancy_isHermitian (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x₀ : ι → ℝ) (z : EpochState ι) :
    (discrepancy A x₀ z).IsHermitian := by
  change (∑ i, (position z i - x₀ i) • A i)ᴴ = _
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    star_trivial, (hA _).isHermitian.eq]
  rfl

theorem budgetCenter_isHermitian (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x₀ : ι → ℝ) (z : EpochState ι) :
    (budgetCenter A x₀ z).IsHermitian := by
  change (∑ i, ((x₀ i)^2 - (position z i)^2 + spent z i) • A i)ᴴ = _
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    star_trivial, (hA _).isHermitian.eq]
  rfl

def epochCenterSize (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ) (z : EpochState ι) : ℝ :=
  max ‖discrepancy A x₀ z‖ ‖budgetCenter A x₀ z‖

theorem continuous_epochCenterSize (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ) :
    Continuous (epochCenterSize A x₀) :=
  (continuous_discrepancy A x₀).norm.max (continuous_budgetCenter A x₀).norm

theorem epochCenterSize_le_potential [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {β θ : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hθ : 0 ≤ θ)
    (x₀ : ι → ℝ) {a R : ℝ} {z : EpochState ι} (hz : z ∈ epochDomain a R) :
    epochCenterSize A x₀ z ≤ epochPotential A β θ x₀ z := by
  apply max_le
  · exact left_center_norm_le_potential (discrepancy_isHermitian A hA x₀ z)
      A hβ hβ1 (fun i => (hz i).2.2.2.2.1) hθ
  · exact right_center_norm_le_potential (budgetCenter_isHermitian A hA x₀ z)
      A hβ hβ1 (fun i => (hz i).2.2.2.2.1) hθ

/-- States with exhausted reserves form a fixed compact set. -/
theorem isCompact_exhaustedStates (a R : ℝ) :
    IsCompact {z : EpochState ι | z ∈ epochDomain a R ∧ ∀ i, reserve z i = 0} := by
  have hc : IsClosed {z : EpochState ι | ∀ i, reserve z i = 0} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_eq ((continuous_apply i).comp continuous_reserve) continuous_const
  exact (isCompact_epochDomain a R).inter_right hc

/-- Compactness removes the positive root regularizer without varying the
source support in a derivative argument. -/
theorem exists_exhausted_bound_of_arbitrarily_small_error (a R : ℝ)
    (G : EpochState ι → ℝ) (hG : Continuous G) (B : ℝ)
    (happrox : ∀ η : ℝ, 0 < η → ∃ z : EpochState ι,
      z ∈ epochDomain a R ∧ (∀ i, reserve z i = 0) ∧ G z ≤ B + η) :
    ∃ z : EpochState ι, z ∈ epochDomain a R ∧
      (∀ i, reserve z i = 0) ∧ G z ≤ B := by
  obtain ⟨w, hw, hwc, hwB⟩ := happrox 1 (by norm_num)
  obtain ⟨z, hz, hmin⟩ := (isCompact_exhaustedStates (ι := ι) a R).exists_isMinOn
    ⟨w, hw, hwc⟩ hG.continuousOn
  refine ⟨z, hz.1, hz.2, ?_⟩
  by_contra hn
  have hgap : 0 < (G z - B) / 2 := by linarith
  obtain ⟨y, hy, hyc, hyB⟩ := happrox ((G z - B) / 2) hgap
  have hm := hmin (show y ∈ {z | z ∈ epochDomain a R ∧ ∀ i, reserve z i = 0}
    from ⟨hy, hyc⟩)
  change G z ≤ G y at hm
  linarith

/-- The concrete terminal epoch bounds charge the budget center explicitly. -/
theorem exhausted_epoch_bounds (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x₀ : ι → ℝ)
    {a R D : ℝ} (ha : a ≠ 0) (hR : 0 < R) {z : EpochState ι}
    (hz : z ∈ epochDomain a R) (hc : ∀ i, reserve z i = 0)
    (hD : epochCenterSize A x₀ z ≤ D) :
    ‖discrepancy A x₀ z‖ ≤ D ∧
      ‖unfinishedMass A z‖ ≤ (‖∑ i, A i‖ + D) / R := by
  have hH := (le_max_left _ _).trans hD
  have hK := (le_max_right _ _).trans hD
  refine ⟨hH, (terminal_mass_norm_le A hA x₀ ha hR hz hc).trans ?_⟩
  exact (div_le_div_iff_of_pos_right hR).mpr (add_le_add_left hK _)

end AugmentedHigherRankKS
