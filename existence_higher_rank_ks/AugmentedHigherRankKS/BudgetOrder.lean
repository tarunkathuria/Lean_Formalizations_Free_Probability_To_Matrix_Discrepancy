import AugmentedHigherRankKS.State
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace AugmentedHigherRankKS

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance budgetCStar : CStarAlgebra (Matrix n n ℂ) := {}

def unfinishedMass (A : ι → Matrix n n ℂ) (z : EpochState ι) : Matrix n n ℂ := by
  classical
  exact ∑ i, if |position z i| < 1 then A i else 0

theorem unfinishedMass_nonneg (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (z : EpochState ι) : 0 ≤ unfinishedMass A z := by
  classical
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact (hA i).nonneg
  · exact le_rfl

theorem position_sq_le_one {a R : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) (i : ι) : (position z i)^2 ≤ 1 := by
  have hlo := (hz i).1
  have hhi := (hz i).2.1
  nlinarith [sq_nonneg (position z i)]

theorem budgetMatrix_nonneg (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) {a R : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) : 0 ≤ budgetMatrix A z := by
  apply Finset.sum_nonneg
  intro i _
  apply smul_nonneg _ (hA i).nonneg
  have hs := (hz i).2.2.1
  have hx := position_sq_le_one hz i
  linarith

theorem initialRemaining_le_mass (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x₀ : ι → ℝ) :
    initialRemaining A x₀ ≤ ∑ i, A i := by
  calc
    initialRemaining A x₀ ≤ ∑ i, (1 : ℝ) • A i := by
      apply Finset.sum_le_sum
      intro i _
      exact smul_le_smul_of_nonneg_right (by nlinarith [sq_nonneg (x₀ i)])
        (hA i).nonneg
    _ = _ := by simp

theorem budget_le_mass_add_center (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x₀ : ι → ℝ) (z : EpochState ι) :
    budgetMatrix A z ≤ (∑ i, A i) + budgetCenter A x₀ z := by
  rw [budget_decomposition A x₀ z]
  exact add_le_add_right (initialRemaining_le_mass A hA x₀) _

/-- Every unfinished original owner at zero reserve has paid its full epoch budget. -/
theorem terminal_mass_le_budget (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) {a R : ℝ} (ha : a ≠ 0)
    {z : EpochState ι} (hz : z ∈ epochDomain a R)
    (hc : ∀ i, reserve z i = 0) :
    R • unfinishedMass A z ≤ budgetMatrix A z := by
  classical
  unfold unfinishedMass budgetMatrix
  rw [Finset.smul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : |position z i| < 1
  · simp only [if_pos hi]
    apply smul_le_smul_of_nonneg_right _ (hA i).nonneg
    rw [exhausted_spent_eq ha hz hi (hc i)]
    have hx := position_sq_le_one hz i
    linarith
  · simp only [if_neg hi, smul_zero]
    apply smul_nonneg _ (hA i).nonneg
    have hx := position_sq_le_one hz i
    have hs := (hz i).2.2.1
    linarith

/-- Exact deterministic live-mass bound. The budget center is charged explicitly. -/
theorem terminal_mass_norm_le (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x₀ : ι → ℝ)
    {a R : ℝ} (ha : a ≠ 0) (hR : 0 < R)
    {z : EpochState ι} (hz : z ∈ epochDomain a R)
    (hc : ∀ i, reserve z i = 0) :
    ‖unfinishedMass A z‖ ≤ (‖∑ i, A i‖ + ‖budgetCenter A x₀ z‖) / R := by
  have horder := (terminal_mass_le_budget A hA ha hz hc).trans
    (budget_le_mass_add_center A hA x₀ z)
  have hnonneg : 0 ≤ R • unfinishedMass A z :=
    smul_nonneg hR.le (unfinishedMass_nonneg A hA z)
  have hn := (CStarAlgebra.norm_le_norm_of_nonneg_of_le hnonneg horder).trans
    (norm_add_le (∑ i, A i) (budgetCenter A x₀ z))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR] at hn
  apply (le_div_iff₀ hR).2
  simpa only [mul_comm] using hn

end AugmentedHigherRankKS
