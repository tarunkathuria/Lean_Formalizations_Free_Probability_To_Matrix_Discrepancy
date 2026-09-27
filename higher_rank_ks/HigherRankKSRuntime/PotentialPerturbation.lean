import HigherRankKSRuntime.StateUpdates
import AugmentedHigherRankKS.EpochPotential
import MatrixSpencer.SignedLift

/-! Center perturbation bounds for the actual four-block optimized potential.
Source deletion is combined with a center estimate before taking the maximum. -/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKSRuntime
open AugmentedHigherRankKS

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance perturbationCStar {k : Type*} [Fintype k] [DecidableEq k] :
    CStarAlgebra (Matrix k k ℂ) := {}

theorem potential_center_source_le
    {H H' : Matrix (FourSpin n) (FourSpin n) ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (A : ι → Matrix n n ℂ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (θ : ℝ)
    {c c' : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (hc' : ∀ i, 0 ≤ c' i)
    (hcc : ∀ i, c' i ≤ c i) :
    potential H' A β c' θ ≤ potential H A β c θ + ‖H' - H‖ := by
  obtain ⟨S, hS, hmax⟩ := exists_optimizer H' A hβ hβ1 hc' θ
  rw [potential_eq_of_optimizer H' A β c' θ hS hmax]
  have hmono := objective_mono_weights H' A β θ hc' hc hcc hS.1
  have hbase := objective_le_potential H A hβ hβ1 hc θ hS
  have hcenter := realTrace_mul_density_le_norm (hH'.sub hH) hS
  rw [Matrix.sub_mul, realTrace_sub] at hcenter
  unfold objective at hmono hbase ⊢
  linarith

theorem potential_center_lipschitz
    {H H' : Matrix (FourSpin n) (FourSpin n) ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (A : ι → Matrix n n ℂ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (θ : ℝ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) :
    |potential H' A β c θ - potential H A β c θ| ≤ ‖H' - H‖ := by
  have hu := potential_center_source_le hH hH' A hβ hβ1 θ hc hc (fun _ => le_rfl)
  have hl := potential_center_source_le hH' hH A hβ hβ1 θ hc hc (fun _ => le_rfl)
  rw [norm_sub_rev H H'] at hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem fromBlocks_norm_le {H K : Matrix n n ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) {r : ℝ}
    (hHN : ‖H‖ ≤ r) (hKN : ‖K‖ ≤ r) :
    ‖Matrix.fromBlocks H 0 0 K‖ ≤ r := by
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
    (hbound (-H) hH.neg (by simpa using hHN))
    (hbound (-K) hK.neg (by simpa using hKN))
  rw [hdiag] at hl
  have hneg : Matrix.fromBlocks (-H) 0 0 (-K) = -(Matrix.fromBlocks H 0 0 K) := by
    simp only [Matrix.fromBlocks_neg, neg_zero]
  rw [hneg] at hl
  exact hermitian_norm_le_of_order
    (Matrix.IsHermitian.fromBlocks hH (by simp) hK) (neg_le.mp hl) hu

theorem augmentedCenter_norm_le {H K : Matrix n n ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) {r : ℝ}
    (hHN : ‖H‖ ≤ r) (hKN : ‖K‖ ≤ r) :
    ‖augmentedCenter H K‖ ≤ r :=
  fromBlocks_norm_le (signedLift_isHermitian hH) (signedLift_isHermitian hK)
    (signedLift_norm_le hH hHN) (signedLift_norm_le hK hKN)

theorem augmentedCenter_sub (H K H' K' : Matrix n n ℂ) :
    augmentedCenter H' K' - augmentedCenter H K = augmentedCenter (H' - H) (K' - K) := by
  ext ((i | i) | (i | i)) ((j | j) | (j | j)) <;>
    simp [augmentedCenter, signedLift, sub_eq_add_neg, add_comm]

theorem linearCombination_hermitian (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (x : ι → ℝ) :
    (∑ i, x i • A i).IsHermitian := by
  change (∑ i, x i • A i)ᴴ = ∑ i, x i • A i
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial,
    fun i => (hA i).eq]

theorem discrepancy_hermitian (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (x₀ : ι → ℝ) (z : EpochState ι) :
    (discrepancy A x₀ z).IsHermitian := linearCombination_hermitian A hA _

theorem budgetCenter_hermitian (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (x₀ : ι → ℝ) (z : EpochState ι) :
    (budgetCenter A x₀ z).IsHermitian := linearCombination_hermitian A hA _

theorem epoch_center_hermitian (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (x₀ : ι → ℝ) (z : EpochState ι) :
    (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z)).IsHermitian :=
  augmentedCenter_isHermitian (discrepancy_hermitian A hA x₀ z)
    (budgetCenter_hermitian A hA x₀ z)

theorem epochPotential_perturb_le (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (θ : ℝ) (x₀ : ι → ℝ) {z z' : EpochState ι} {r : ℝ}
    (hz : ∀ i, 0 ≤ reserve z i) (hz' : ∀ i, 0 ≤ reserve z' i)
    (hcc : ∀ i, reserve z' i ≤ reserve z i)
    (hH : ‖discrepancy A x₀ z' - discrepancy A x₀ z‖ ≤ r)
    (hK : ‖budgetCenter A x₀ z' - budgetCenter A x₀ z‖ ≤ r) :
    epochPotential A β θ x₀ z' ≤ epochPotential A β θ x₀ z + r := by
  have hb := potential_center_source_le (epoch_center_hermitian A hA x₀ z)
    (epoch_center_hermitian A hA x₀ z') A hβ hβ1 θ hz hz' hcc
  have hn : ‖augmentedCenter (discrepancy A x₀ z') (budgetCenter A x₀ z') -
      augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z)‖ ≤ r := by
    rw [augmentedCenter_sub]
    apply augmentedCenter_norm_le _ _ hH hK
    · exact (discrepancy_hermitian A hA x₀ z').sub (discrepancy_hermitian A hA x₀ z)
    · exact (budgetCenter_hermitian A hA x₀ z').sub (budgetCenter_hermitian A hA x₀ z)
  unfold epochPotential
  exact hb.trans (add_le_add_left hn _)

end HigherRankKSRuntime
