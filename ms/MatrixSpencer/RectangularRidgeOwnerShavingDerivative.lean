import MatrixSpencer.RegularizedShavingDerivative
import MatrixSpencer.RegularizedFamilyDeletion
import MatrixSpencer.RectangularRidgeOwnerFrame
import MatrixSpencer.RectangularRidgeCovarianceResponse

/-! Actual mixed owner derivatives along every supported covariance shave. -/
open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 300000
attribute [local irreducible] RectangularRidgePotential.optimizer
variable {ι ρ n : Type*} [Fintype ι] [Fintype ρ] [Fintype n]
  [DecidableEq ι] [DecidableEq ρ] [DecidableEq n]
local instance ridgeShavingCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance ridgeShavingPhysicalSpace {j : Type*} [Fintype j] [DecidableEq j] :
    NormedSpace ℝ (selfAdjoint (Matrix j j ℂ)) := inferInstance
local instance ridgeShavingCoeffSpace {j : Type*} [Fintype j] [DecidableEq j] :
    NormedSpace ℝ (selfAdjoint (Matrix j j ℝ)) := inferInstance

omit [DecidableEq ι] in
theorem differentiableAt_ridgeOwnerPotential_lift_shave [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (U : Matrix ι ρ ℝ) (K : selfAdjoint (Matrix ρ ρ ℝ))
    (hK : (K : Matrix ρ ρ ℝ).PosDef) (v : ρ → ℝ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) :
    DifferentiableAt ℝ (fun t : ℝ => regularizedOwnerPotential H A
      (covarianceLift U ((K : Matrix ρ ρ ℝ) - t • realRankOne v))
        (RectangularRidgeCovarianceCalculus.regularizer m θ κ)) 0 := by
  have hmix : ∀ j, (mixFamily A U j).IsHermitian := mixFamily_isHermitian A U hA
  have hp := (contDiffAt_hermitianRidgeOwnerPotential H (mixFamily A U) hmix
    m hm θ κ hθ hκ K hK).differentiableAt (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  have hpath : HasDerivAt (fun t : ℝ => K - t • hermitianRankOne v) (-hermitianRankOne v) 0 := by
    simpa only [zero_sub, one_smul] using (hasDerivAt_const (0 : ℝ) K).sub
      ((hasDerivAt_id (0 : ℝ)).smul_const (hermitianRankOne v))
  have hp' : DifferentiableAt ℝ (hermitianRidgeOwnerPotential H (mixFamily A U) m θ κ)
      (K - (0 : ℝ) • hermitianRankOne v) := by simpa using hp
  have h := hp'.comp (0 : ℝ) hpath.differentiableAt
  convert h using 1
  funext t
  exact regularizedOwnerPotential_covarianceLift H A U _ (RectangularRidgeCovarianceCalculus.regularizer m θ κ)

theorem differentiableAt_ridgeOwnerPotential_supported_shave [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (u : EuclideanSpace ℝ ι)
    (hu : u ∈ LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) :
    DifferentiableAt ℝ (fun t : ℝ => regularizedOwnerPotential H A
      (C - t • realRankOne (WithLp.ofLp u)) (RectangularRidgeCovarianceCalculus.regularizer m θ κ)) 0 := by
  let U := covarianceRangeEmbedding C hC
  let K : selfAdjoint (Matrix (covarianceRangeIndex C hC) (covarianceRangeIndex C hC) ℝ) :=
    ⟨covarianceRangeMatrix C hC, (covarianceRangeMatrix_posDef C hC).isHermitian⟩
  have hur : WithLp.ofLp u ∈ LinearMap.range U.mulVecLin := by
    rw [← covarianceRange_range C hC]
    exact covariance_mem_mulVec_range hu
  have he : ∀ t : ℝ, covarianceLift U ((K : Matrix _ _ ℝ) -
      t • realRankOne (Uᵀ *ᵥ WithLp.ofLp u)) = C - t • realRankOne (WithLp.ofLp u) := by
    intro t
    exact (covarianceLift_supported_shave U (covarianceRangeEmbedding_isometry C hC)
      K hur t).trans (congrArg (fun D => D - t • realRankOne (WithLp.ofLp u))
        (covarianceRange_reconstruct C hC))
  have h := differentiableAt_ridgeOwnerPotential_lift_shave H A hA U K
    (covarianceRangeMatrix_posDef C hC) (Uᵀ *ᵥ WithLp.ofLp u) m hm θ κ hθ hκ
  simpa only [he] using h

/-- The actual supremum derivative uses its own optimizer and its own supported Gram. -/
theorem hasDerivAt_ridgeOwnerPotential_supported_shave [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (u : EuclideanSpace ℝ ι)
    (hu : u ∈ LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) :
    HasDerivAt (fun t : ℝ => regularizedOwnerPotential (H : Matrix n n ℂ) A
      (C - t • realRankOne (WithLp.ofLp u)) (RectangularRidgeCovarianceCalculus.regularizer m θ κ))
      (-(WithLp.ofLp u ⬝ᵥ ((RectangularRidgeOwnerFrame.ownedGram A C
        (RectangularRidgePotential.optimizer (H : Matrix n n ℂ) (covarianceKraus A C) m θ κ)) *ᵥ WithLp.ofLp u))) 0 := by
  let Cₛ : selfAdjoint (Matrix ι ι ℝ) := ⟨C, hC.isHermitian⟩
  let S := RectangularRidgeCalculus.hermitianOptimizer (H : Matrix n n ℂ) (covarianceKraus A C) m θ κ
  let f := fun t : ℝ => regularizedOwnerPotential (H : Matrix n n ℂ) A
    (C - t • realRankOne (WithLp.ofLp u)) (RectangularRidgeCovarianceCalculus.regularizer m θ κ)
  let g := fun t : ℝ => regularizedOwnerObjective (H : Matrix n n ℂ) A
    (C - t • realRankOne (WithLp.ofLp u)) (RectangularRidgeCovarianceCalculus.regularizer m θ κ) S
  have hf : DifferentiableAt ℝ f 0 :=
    differentiableAt_ridgeOwnerPotential_supported_shave (H : Matrix n n ℂ) A hA hC u hu m hm θ κ hθ hκ
  have hg : HasDerivAt g
      (-(WithLp.ofLp u ⬝ᵥ ((RectangularRidgeOwnerFrame.ownedGram A C
        (RectangularRidgePotential.optimizer (H : Matrix n n ℂ) (covarianceKraus A C) m θ κ)) *ᵥ WithLp.ofLp u))) 0 := by
    have hd := hasDerivAt_regularizedOwnerObjective_supported_shave (H : Matrix n n ℂ) A hA Cₛ hC
      (WithLp.ofLp u) (covariance_mem_mulVec_range hu) (RectangularRidgeCovarianceCalculus.regularizer m θ κ) S
      (RectangularRidgeCalculus.hermitianOptimizer_posDef (H : Matrix n n ℂ) (covarianceKraus A C) m hm θ κ hθ hκ)
    dsimp only at hd
    simpa only [RectangularRidgeOwnerFrame.ownedGram, RectangularRidgeOwnerFrame.sourceTransport,
      RectangularRidgeOwnerFrame.sourceDensity, RectangularRidgeCalculus.hermitianOptimizer,
      krausReducedFamily_channel (covarianceKraus A C) (covarianceKraus_isHermitian A hA C)] using hd
  have hbase : f 0 = g 0 := by
    simp only [f, g, zero_smul, sub_zero]
    change RectangularRidgeCovarianceCalculus.ownerPotential m (H : Matrix n n ℂ) A C θ κ =
      RectangularRidgeCovarianceCalculus.ownerObjective m (H : Matrix n n ℂ) A C θ κ S
    rw [RectangularRidgeCovarianceCalculus.ownerPotential_eq_densityPotential m (H : Matrix n n ℂ) A hA hC,
      RectangularRidgeCovarianceCalculus.ownerObjective_eq_densityObjective m (H : Matrix n n ℂ) A hA hC]
    exact RectangularRidgePotential.potential_eq_optimizer (H : Matrix n n ℂ) (covarianceKraus A C) m θ κ
  have hmin : IsLocalMin (fun t => f t - g t) 0 := by
    filter_upwards [eventually_posSemidef_supported_shave hC u hu] with t ht
    change f 0 - g 0 ≤ f t - g t
    rw [hbase, sub_self]
    apply sub_nonneg.mpr
    change RectangularRidgeCovarianceCalculus.ownerObjective m (H : Matrix n n ℂ) A
      (C - t • realRankOne (WithLp.ofLp u)) θ κ S ≤
      RectangularRidgeCovarianceCalculus.ownerPotential m (H : Matrix n n ℂ) A
      (C - t • realRankOne (WithLp.ofLp u)) θ κ
    rw [RectangularRidgeCovarianceCalculus.ownerObjective_eq_densityObjective m (H : Matrix n n ℂ) A hA ht,
      RectangularRidgeCovarianceCalculus.ownerPotential_eq_densityPotential m (H : Matrix n n ℂ) A hA ht]
    exact RectangularRidgePotential.objective_le_potential (H : Matrix n n ℂ) _ m θ κ
      (RectangularRidgePotential.optimizer_mem (H : Matrix n n ℂ) (covarianceKraus A C) m θ κ)
  have hz := hmin.hasDerivAt_eq_zero (hf.hasDerivAt.sub hg)
  have hd := hf.hasDerivAt
  rw [sub_eq_zero.mp hz] at hd
  exact hd

end
end MatrixSpencer
