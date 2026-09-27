import AugmentedHigherRankKS.CompactEpoch
import AugmentedHigherRankKS.FourBlockPotential

/-! The concrete augmented potential on the compact reserve state space. -/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace AugmentedHigherRankKS

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance epochCStar {k : Type*} [Fintype k] [DecidableEq k] :
    CStarAlgebra (Matrix k k ℂ) := {}

/-- Four signed blocks monitor discrepancy and the reserve ledger simultaneously. -/
def augmentedCenter (H K : Matrix n n ℂ) : Matrix (FourSpin n) (FourSpin n) ℂ :=
  Matrix.fromBlocks (signedLift H) 0 0 (signedLift K)

/-- The actual optimized four-block value, with one reserve per original atom. -/
def epochPotential (A : ι → Matrix n n ℂ) (β θ : ℝ) (x₀ : ι → ℝ)
    (z : EpochState ι) : ℝ :=
  potential (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z))
    A β (reserve z) θ

theorem augmentedCenter_isHermitian {H K : Matrix n n ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    (augmentedCenter H K).IsHermitian :=
  Matrix.IsHermitian.fromBlocks (signedLift_isHermitian hH) (by simp)
    (signedLift_isHermitian hK)

theorem continuous_augmentedCenter : Continuous
    (fun p : Matrix n n ℂ × Matrix n n ℂ => augmentedCenter p.1 p.2) := by
  unfold augmentedCenter signedLift
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  rcases i with (i | i) <;> rcases i with (i | i) <;>
    rcases j with (j | j) <;> rcases j with (j | j) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply] <;> fun_prop

theorem continuous_discrepancy (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ) :
    Continuous (discrepancy A x₀) := by
  unfold discrepancy
  apply continuous_finset_sum
  intro i hi
  exact (((continuous_apply i).comp continuous_position).sub continuous_const).smul
    continuous_const

theorem continuous_budgetCenter (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ) :
    Continuous (budgetCenter A x₀) := by
  unfold budgetCenter
  apply continuous_finset_sum
  intro i hi
  exact ((continuous_const.sub (((continuous_apply i).comp continuous_position).pow 2)).add
    ((continuous_apply i).comp continuous_spent)).smul continuous_const

theorem continuousOn_epochPotential (A : ι → Matrix n n ℂ) {β : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (θ : ℝ) (x₀ : ι → ℝ) (a R : ℝ) :
    ContinuousOn (epochPotential A β θ x₀) (epochDomain a R) := by
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_potential_of_data A
  · exact continuous_augmentedCenter.comp
      (((continuous_discrepancy A x₀).comp continuous_subtype_val).prodMk
        ((continuous_budgetCenter A x₀).comp continuous_subtype_val))
  · exact hβ
  · exact hβ1
  · intro i
    exact ((continuous_apply i).comp continuous_reserve).comp continuous_subtype_val
  · intro z i
    exact (z.property i).2.2.2.2.1

/-- Covariance withdrawal at fixed centers can only lower the source. -/
theorem source_mono_weights (A : ι → Matrix n n ℂ) (β : ℝ)
    {c d : ι → ℝ} (hcd : ∀ i, c i ≤ d i)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef) :
    source A β c S ≤ source A β d S := by
  exact Finset.sum_le_sum fun i _ =>
    smul_le_smul_of_nonneg_right (hcd i) (sourceTerm_posSemidef β (A i) hS).nonneg

theorem objective_mono_weights (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : ι → Matrix n n ℂ) (β θ : ℝ)
    {c d : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i)
    (hcd : ∀ i, c i ≤ d i)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef) :
    objective H A β c θ S ≤ objective H A β d θ S := by
  have hf := fidelity_mono hS hS (source_posSemidef A β hc hS)
    (source_posSemidef A β hd hS) le_rfl (source_mono_weights A β hcd hS)
  unfold objective
  linarith

/-- Monotonicity is proved for the optimized value, rather than postulated. -/
theorem potential_mono_weights [Nonempty n]
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (θ : ℝ)
    {c d : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i)
    (hcd : ∀ i, c i ≤ d i) : potential H A β c θ ≤ potential H A β d θ := by
  obtain ⟨S, hS, hmax⟩ := exists_optimizer H A hβ hβ1 hc θ
  rw [potential_eq_of_optimizer H A β c θ hS hmax]
  exact (objective_mono_weights H A β θ hc hd hcd hS.1).trans
    (objective_le_potential H A hβ hβ1 hd θ hS)

theorem epochPotential_dropReserve_le [Nonempty n] [DecidableEq ι]
    (A : ι → Matrix n n ℂ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (θ : ℝ) (x₀ : ι → ℝ) {a R : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) (i : ι) :
    epochPotential A β θ x₀ (dropReserve z i) ≤ epochPotential A β θ x₀ z := by
  apply potential_mono_weights _ A hβ hβ1 θ
  · intro j
    by_cases hji : j = i
    · subst j; simp [dropReserve, reserve]
    · simpa [dropReserve, reserve, hji] using (hz j).2.2.2.2.1
  · intro j
    exact (hz j).2.2.2.2.1
  · intro j
    by_cases hji : j = i
    · subst j; simpa [dropReserve, reserve] using (hz i).2.2.2.2.1
    · simp [dropReserve, reserve, hji]

end AugmentedHigherRankKS
