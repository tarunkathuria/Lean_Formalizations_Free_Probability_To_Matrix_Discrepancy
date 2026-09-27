import AugmentedHigherRankKS.EpochMovement
import AugmentedHigherRankKS.BudgetOrder
import MatrixSpencer.SignedLift

/-! Bounds for actual epoch centers and their finite-query perturbations. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance queryCenterCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}

theorem weighted_sum_norm_le (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hsum : ∑ i, A i ≤ 1) {u : ι → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hu : ∀ i, |u i| ≤ r) : ‖∑ i, u i • A i‖ ≤ r := by
  have hb : (∑ i, u i • A i).IsHermitian := by
    change (∑ i, u i • A i)ᴴ = _
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial, (hA _).isHermitian.eq]
  have hs : r • (∑ i, A i) ≤ r • (1 : Matrix n n ℂ) := smul_le_smul_of_nonneg_left hsum hr
  have hu' : (∑ i, u i • A i) ≤ r • (∑ i, A i) := by
    rw [Finset.smul_sum]
    exact Finset.sum_le_sum fun i _ => smul_le_smul_of_nonneg_right (abs_le.mp (hu i)).2 (hA i).nonneg
  have hl' : -(r • (∑ i, A i)) ≤ ∑ i, u i • A i := by
    rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [← neg_smul]
    exact smul_le_smul_of_nonneg_right (abs_le.mp (hu i)).1 (hA i).nonneg
  exact hermitian_norm_le_of_order hb ((neg_le_neg hs).trans hl') (hu'.trans hs)

theorem query_fromBlocks_norm_le {H K : Matrix n n ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) {r : ℝ}
    (hHN : ‖H‖ ≤ r) (hKN : ‖K‖ ≤ r) : ‖Matrix.fromBlocks H 0 0 K‖ ≤ r := by
  have hbound (B : Matrix n n ℂ) (hB : B.IsHermitian) (hb : ‖B‖ ≤ r) :
      B ≤ r • (1 : Matrix n n ℂ) := by
    have h := IsSelfAdjoint.le_algebraMap_norm_self hB
    rw [Algebra.algebraMap_eq_smul_one] at h
    exact h.trans (smul_le_smul_of_nonneg_right hb zero_le_one)
  have hdiag : Matrix.fromBlocks (r • (1 : Matrix n n ℂ)) 0 0 (r • (1 : Matrix n n ℂ)) =
      r • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
    simpa only [smul_zero, Matrix.fromBlocks_one] using
      (Matrix.fromBlocks_smul r (1 : Matrix n n ℂ) (0 : Matrix n n ℂ)
        (0 : Matrix n n ℂ) (1 : Matrix n n ℂ)).symm
  have hu := fromBlocks_diagonal_mono (hbound H hH hHN) (hbound K hK hKN)
  rw [hdiag] at hu
  have hl := fromBlocks_diagonal_mono
    (hbound (-H) hH.neg (by simpa using hHN)) (hbound (-K) hK.neg (by simpa using hKN))
  rw [hdiag] at hl
  have hneg : Matrix.fromBlocks (-H) 0 0 (-K) = -(Matrix.fromBlocks H 0 0 K) := by
    simp only [Matrix.fromBlocks_neg, neg_zero]
  rw [hneg] at hl
  exact hermitian_norm_le_of_order (Matrix.IsHermitian.fromBlocks hH (by simp) hK) (neg_le.mp hl) hu

theorem augmentedCenter_norm_le {H K : Matrix n n ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) {r : ℝ}
    (hHN : ‖H‖ ≤ r) (hKN : ‖K‖ ≤ r) : ‖augmentedCenter H K‖ ≤ r :=
  query_fromBlocks_norm_le (signedLift_isHermitian hH) (signedLift_isHermitian hK)
    (signedLift_norm_le hH hHN) (signedLift_norm_le hK hKN)

theorem epoch_center_norm_le_five (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hsum : ∑ i, A i ≤ 1) (x₀ : ι → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1)
    {a : ℝ} {z : EpochState ι} (hz : z ∈ epochDomain a 4) :
    ‖augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z)‖ ≤ 5 := by
  have hh : ‖discrepancy A x₀ z‖ ≤ 2 := by
    apply weighted_sum_norm_le A hA hsum (by norm_num)
    intro i
    have hx := abs_le.mp (hx₀ i)
    have hz' := hz i
    exact abs_le.mpr ⟨by linarith [hz'.1], by linarith [hz'.2.1]⟩
  have hk : ‖budgetCenter A x₀ z‖ ≤ 5 := by
    apply weighted_sum_norm_le A hA hsum (by norm_num)
    intro i
    have hx : (x₀ i)^2 ≤ 1 := by nlinarith [(abs_le.mp (hx₀ i)).1,(abs_le.mp (hx₀ i)).2]
    have hz2 := position_sq_le_one hz i
    have hb := (hz i).2.2.1
    have hb' := (hz i).2.2.2.1
    exact abs_le.mpr ⟨by nlinarith [sq_nonneg (x₀ i)], by nlinarith [sq_nonneg (position z i)]⟩
  apply augmentedCenter_norm_le _ _ (hh.trans (by norm_num)) hk
  all_goals
    change _ᴴ = _
    simp only [discrepancy, budgetCenter, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_smul, star_trivial, (hA _).isHermitian.eq]

/-- The full coefficient force is bounded by twice the largest coordinate increment. -/
theorem coefficient_force_norm_le [DecidableEq ι] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    (x u : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) {r : ℝ} (hr : 0 ≤ r)
    (hu : ∀ i, |u i| ≤ r) : ‖∑ i, u i • forceAtom (x i) (A i)‖ ≤ 2*r := by
  rw [← augmentedCenter_force_sum]
  have hh := weighted_sum_norm_le A hA hsum hr hu
  have hk := weighted_sum_norm_le A hA hsum hr (u := fun i => x i*u i) (by
    intro i
    rw [abs_mul]
    calc _ ≤ 1*r := mul_le_mul (hx i) (hu i) (abs_nonneg _) (by norm_num)
         _ = _ := one_mul _)
  apply augmentedCenter_norm_le _ _ (hh.trans (by linarith))
    (by simpa only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 2)] using mul_le_mul_of_nonneg_left hk (by norm_num : (0:ℝ) ≤ 2))
  all_goals
    change _ᴴ = _
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
      star_trivial, (hA _).isHermitian.eq]

/-- Every enlarged coefficient query of radius at most one remains within the denominator's center cap. -/
theorem coefficient_query_center_norm [DecidableEq ι] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : ‖H‖ ≤ 5)
    (x u : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) (hu : ∀ i, |u i| ≤ 1) :
    ‖H + ∑ i, u i • forceAtom (x i) (A i)‖ ≤ 8 := by
  have hg := coefficient_force_norm_le A hA hsum x u hx zero_le_one hu
  exact (norm_add_le _ _).trans (by linarith)
end AugmentedHigherRankKS
