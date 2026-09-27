import MatrixSpencer.RegularizedShavingDerivative
import MatrixSpencer.RegularizedFamilyDeletion
import MatrixSpencer.DyadicOwnerFrame
import MatrixSpencer.DyadicCovarianceResponse

/-! Actual dyadic owner derivatives along every supported covariance shave. -/
open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι κ n : Type*} [Fintype ι] [Fintype κ] [Fintype n]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq n]
local instance dyadicShavingCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance dyadicShavingPhysicalSpace {j : Type*} [Fintype j] [DecidableEq j] :
    NormedSpace ℝ (selfAdjoint (Matrix j j ℂ)) := inferInstance
local instance dyadicShavingCoeffSpace {j : Type*} [Fintype j] [DecidableEq j] :
    NormedSpace ℝ (selfAdjoint (Matrix j j ℝ)) := inferInstance

omit [DecidableEq ι] in
theorem differentiableAt_dyadicOwnerPotential_lift_shave [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (U : Matrix ι κ ℝ) (K : selfAdjoint (Matrix κ κ ℝ))
    (hK : (K : Matrix κ κ ℝ).PosDef) (v : κ → ℝ)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    DifferentiableAt ℝ (fun t : ℝ => regularizedOwnerPotential H A
      (covarianceLift U ((K : Matrix κ κ ℝ) - t • realRankOne v))
        (dyadicTsallisRegularizer m θ)) 0 := by
  have hmix : ∀ j, (mixFamily A U j).IsHermitian := mixFamily_isHermitian A U hA
  have hp := (contDiffAt_hermitianDyadicOwnerPotential H (mixFamily A U) hmix
    m hm θ hθ K hK).differentiableAt (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  have hpath : HasDerivAt (fun t : ℝ => K - t • hermitianRankOne v) (-hermitianRankOne v) 0 := by
    simpa only [zero_sub, one_smul] using (hasDerivAt_const (0 : ℝ) K).sub
      ((hasDerivAt_id (0 : ℝ)).smul_const (hermitianRankOne v))
  have hp' : DifferentiableAt ℝ (hermitianDyadicOwnerPotential H (mixFamily A U) m θ)
      (K - (0 : ℝ) • hermitianRankOne v) := by simpa using hp
  have h := hp'.comp (0 : ℝ) hpath.differentiableAt
  convert h using 1
  funext t
  exact regularizedOwnerPotential_covarianceLift H A U _ (dyadicTsallisRegularizer m θ)

theorem differentiableAt_dyadicOwnerPotential_supported_shave [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (u : EuclideanSpace ℝ ι)
    (hu : u ∈ LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    DifferentiableAt ℝ (fun t : ℝ => regularizedOwnerPotential H A
      (C - t • realRankOne (WithLp.ofLp u)) (dyadicTsallisRegularizer m θ)) 0 := by
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
  have h := differentiableAt_dyadicOwnerPotential_lift_shave H A hA U K
    (covarianceRangeMatrix_posDef C hC) (Uᵀ *ᵥ WithLp.ofLp u) m hm θ hθ
  simpa only [he] using h

/-- The actual supremum derivative uses its own optimizer and its own supported Gram. -/
theorem hasDerivAt_dyadicOwnerPotential_supported_shave [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (u : EuclideanSpace ℝ ι)
    (hu : u ∈ LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    HasDerivAt (fun t : ℝ => regularizedOwnerPotential (H : Matrix n n ℂ) A
      (C - t • realRankOne (WithLp.ofLp u)) (dyadicTsallisRegularizer m θ))
      (-(WithLp.ofLp u ⬝ᵥ (DyadicOwnerFrame.observedOwnedGram H A C m θ *ᵥ WithLp.ofLp u))) 0 := by
  let Cₛ : selfAdjoint (Matrix ι ι ℝ) := ⟨C, hC.isHermitian⟩
  let S := hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) (covarianceKraus A C) m θ
  let f := fun t : ℝ => regularizedOwnerPotential (H : Matrix n n ℂ) A
    (C - t • realRankOne (WithLp.ofLp u)) (dyadicTsallisRegularizer m θ)
  let g := fun t : ℝ => regularizedOwnerObjective (H : Matrix n n ℂ) A
    (C - t • realRankOne (WithLp.ofLp u)) (dyadicTsallisRegularizer m θ) S
  have hf : DifferentiableAt ℝ f 0 :=
    differentiableAt_dyadicOwnerPotential_supported_shave (H : Matrix n n ℂ) A hA hC u hu m hm θ hθ
  have hg : HasDerivAt g
      (-(WithLp.ofLp u ⬝ᵥ (DyadicOwnerFrame.observedOwnedGram H A C m θ *ᵥ WithLp.ofLp u))) 0 := by
    have hd := hasDerivAt_regularizedOwnerObjective_supported_shave (H : Matrix n n ℂ) A hA Cₛ hC
      (WithLp.ofLp u) (covariance_mem_mulVec_range hu) (dyadicTsallisRegularizer m θ) S
      (hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) (covarianceKraus A C) m hm θ hθ)
    dsimp only at hd
    simpa only [DyadicOwnerFrame.observedOwnedGram, DyadicOwnerFrame.observedOwnedTransport,
      DyadicOwnerFrame.observedSourceTransport, DyadicOwnerFrame.observedSourceDensity,
      DyadicOwnerFrame.observedOwnerDensity,
      krausReducedFamily_channel (covarianceKraus A C) (covarianceKraus_isHermitian A hA C)] using hd
  have hbase : f 0 = g 0 := by
    simp only [f, g, zero_smul, sub_zero]
    rw [regularizedOwnerPotential_eq_dyadicDensityPotential (H : Matrix n n ℂ) A hA hC,
      regularizedOwnerObjective_eq_dyadicDensityObjective (H : Matrix n n ℂ) A hA hC]
    exact dyadicDensityPotential_eq_optimizer (H : Matrix n n ℂ) (covarianceKraus A C) m θ
  have hmin : IsLocalMin (fun t => f t - g t) 0 := by
    filter_upwards [eventually_posSemidef_supported_shave hC u hu] with t ht
    change f 0 - g 0 ≤ f t - g t
    rw [hbase, sub_self]
    apply sub_nonneg.mpr
    change regularizedOwnerObjective (H : Matrix n n ℂ) A _ (dyadicTsallisRegularizer m θ) S ≤
      regularizedOwnerPotential (H : Matrix n n ℂ) A _ (dyadicTsallisRegularizer m θ)
    rw [regularizedOwnerObjective_eq_dyadicDensityObjective (H : Matrix n n ℂ) A hA ht,
      regularizedOwnerPotential_eq_dyadicDensityPotential (H : Matrix n n ℂ) A hA ht]
    exact dyadicDensityObjective_le_potential (H : Matrix n n ℂ) _ m θ
      (dyadicDensityOptimizer_mem (H : Matrix n n ℂ) (covarianceKraus A C) m θ)
  have hz := hmin.hasDerivAt_eq_zero (hf.hasDerivAt.sub hg)
  have hd := hf.hasDerivAt
  rw [sub_eq_zero.mp hz] at hd
  exact hd

end
end MatrixSpencer
