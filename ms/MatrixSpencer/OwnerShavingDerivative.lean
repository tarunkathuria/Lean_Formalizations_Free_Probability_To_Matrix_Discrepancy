import MatrixSpencer.OwnerFrame
import MatrixSpencer.CovarianceFace

/-!
# Actual owner-potential shaving at an arbitrary covariance face

All coefficient directions are required to lie in the actual covariance range.
The physical transport used in the derivative is the one in OwnerFrame.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

noncomputable section
namespace MatrixSpencer

set_option maxHeartbeats 600000
variable {ι κ n : Type*} [Fintype ι] [Fintype κ] [Fintype n]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq n]

local instance ownerShavingCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance ownerShavingPhysicalSpace {j : Type*} [Fintype j] [DecidableEq j] :
    NormedSpace ℝ (selfAdjoint (Matrix j j ℂ)) := inferInstance
local instance ownerShavingCoefficientSpace {j : Type*} [Fintype j] [DecidableEq j] :
    NormedSpace ℝ (selfAdjoint (Matrix j j ℝ)) := inferInstance

omit [DecidableEq ι] [DecidableEq κ] in
/-- Exact objective identity on a coefficient face, even away from its PSD cone. -/
theorem ownerObjective_covarianceLift (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (U : Matrix ι κ ℝ) (K : Matrix κ κ ℝ) (θ : ℝ) (S : Matrix n n ℂ) :
    ownerObjective H A (covarianceLift U K) θ S = ownerObjective H (mixFamily A U) K θ S := by
  unfold ownerObjective
  rw [covarianceSource_rectangular_mixing]

omit [DecidableEq ι] [DecidableEq κ] in
/-- The supremum is the same actual function in any fixed covariance-face coordinates. -/
theorem ownerPotential_covarianceLift (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (U : Matrix ι κ ℝ) (K : Matrix κ κ ℝ) (θ : ℝ) :
    ownerPotential H A (covarianceLift U K) θ = ownerPotential H (mixFamily A U) K θ := by
  unfold ownerPotential
  congr 2
  funext S
  exact ownerObjective_covarianceLift H A U K θ S

/-- Conversion from the Euclidean operator range to its raw matrix-vector coordinates. -/
theorem covariance_mem_mulVec_range {C : Matrix ι ι ℝ} {u : EuclideanSpace ℝ ι}
    (hu : u ∈ LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap) :
    WithLp.ofLp u ∈ LinearMap.range C.mulVecLin := by
  obtain ⟨w, hw⟩ := hu
  exact ⟨WithLp.ofLp w, congrArg WithLp.ofLp hw⟩

omit [DecidableEq ι] in
/-- A shave inside an isometric face is differentiable at every positive definite face point. -/
theorem differentiableAt_ownerPotential_lift_shave [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (U : Matrix ι κ ℝ) (K : selfAdjoint (Matrix κ κ ℝ))
    (hK : (K : Matrix κ κ ℝ).PosDef) (v : κ → ℝ) {θ : ℝ} (hθ : 0 < θ) :
    DifferentiableAt ℝ (fun t : ℝ => ownerPotential H A
      (covarianceLift U ((K : Matrix κ κ ℝ) - t • realRankOne v)) θ) 0 := by
  have hm : ∀ j, (mixFamily A U j).IsHermitian := mixFamily_isHermitian A U hA
  have hp := (contDiffAt_hermitianOwnerPotential H (mixFamily A U) hm hθ K hK).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  have hpath : HasDerivAt (fun t : ℝ => K - t • hermitianRankOne v) (-hermitianRankOne v) 0 := by
    simpa only [zero_sub, one_smul] using (hasDerivAt_const (0 : ℝ) K).sub
      ((hasDerivAt_id (0 : ℝ)).smul_const (hermitianRankOne v))
  have hp' : DifferentiableAt ℝ (hermitianOwnerPotential H (mixFamily A U) θ)
      (K - (0 : ℝ) • hermitianRankOne v) := by simpa using hp
  have h := hp'.comp (0 : ℝ) hpath.differentiableAt
  convert h using 1
  funext t
  exact ownerPotential_covarianceLift H A U _ θ

/-- The actual owner potential has a two-sided derivative along every supported
shaving direction, including at a singular covariance. -/
theorem differentiableAt_ownerPotential_supported_shave [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (u : EuclideanSpace ℝ ι)
    (hu : u ∈ LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap)
    {θ : ℝ} (hθ : 0 < θ) :
    DifferentiableAt ℝ (fun t : ℝ => ownerPotential H A (C - t • realRankOne (WithLp.ofLp u)) θ) 0 := by
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
  have h := differentiableAt_ownerPotential_lift_shave H A hA U K
    (covarianceRangeMatrix_posDef C hC) (Uᵀ *ᵥ WithLp.ofLp u) hθ
  simpa only [he] using h


/-- The physical force associated to an original coefficient vector. -/
def ownerCoefficientForce (A : ι → Matrix n n ℂ) (u : ι → ℝ) : Matrix n n ℂ :=
  ∑ i, u i • A i

omit [Fintype n] [DecidableEq ι] [DecidableEq n] in
theorem ownerCoefficientForce_mixed (A : ι → Matrix n n ℂ) (R : Matrix ι ι ℝ) (v : ι → ℝ) :
    ownerCoefficientForce (mixedKraus A R) v = ownerCoefficientForce A (R *ᵥ v) := by
  simp only [ownerCoefficientForce, mixedKraus, Finset.smul_sum, smul_smul,
    Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

omit [Fintype n] [DecidableEq ι] [DecidableEq n] in
theorem ownerCoefficientForce_isHermitian (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (u : ι → ℝ) : (ownerCoefficientForce A u).IsHermitian := by
  unfold ownerCoefficientForce Matrix.IsHermitian
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial]
  simp only [(hA _).eq]

omit [Fintype n] [DecidableEq n] in
/-- Every supported original coefficient force is a linear combination of the
actual square-root covariance Kraus family. -/
theorem ownerCoefficientForce_of_range (A : ι → Matrix n n ℂ)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {u : ι → ℝ}
    (hu : u ∈ LinearMap.range C.mulVecLin) :
    ∃ v : ι → ℝ, ownerCoefficientForce A u = ownerCoefficientForce (covarianceKraus A C) v := by
  obtain ⟨w, hw⟩ := hu
  let v := CFC.sqrt C *ᵥ w
  have hv : CFC.sqrt C *ᵥ v = u := by
    rw [show CFC.sqrt C *ᵥ v = (CFC.sqrt C * CFC.sqrt C) *ᵥ w from
      Matrix.mulVec_mulVec w (CFC.sqrt C) (CFC.sqrt C), CFC.sqrt_mul_sqrt_self C hC.nonneg]
    exact hw
  refine ⟨v, ?_⟩
  change ownerCoefficientForce A u = ownerCoefficientForce (mixedKraus A (CFC.sqrt C)) v
  rw [ownerCoefficientForce_mixed, hv]

theorem ownerCoefficientForce_projection_left (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {u : ι → ℝ}
    (hu : u ∈ LinearMap.range C.mulVecLin) :
    krausSupportProjection (covarianceKraus A C) * ownerCoefficientForce A u = ownerCoefficientForce A u := by
  obtain ⟨v, hv⟩ := ownerCoefficientForce_of_range A hC hu
  rw [hv]
  simp only [ownerCoefficientForce, Matrix.mul_sum, Matrix.mul_smul,
    kraus_projection_left (covarianceKraus A C) (covarianceKraus_isHermitian A hA C)]

theorem ownerCoefficientForce_projection_right (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {u : ι → ℝ}
    (hu : u ∈ LinearMap.range C.mulVecLin) :
    ownerCoefficientForce A u * krausSupportProjection (covarianceKraus A C) = ownerCoefficientForce A u := by
  obtain ⟨v, hv⟩ := ownerCoefficientForce_of_range A hC hu
  rw [hv]
  simp only [ownerCoefficientForce, Matrix.sum_mul, Matrix.smul_mul,
    kraus_projection_right (covarianceKraus A C) (covarianceKraus_isHermitian A hA C)]

omit [DecidableEq ι] [DecidableEq n] in
theorem covarianceSource_rankOne_force (A : ι → Matrix n n ℂ) (u : ι → ℝ) (S : Matrix n n ℂ) :
    covarianceSource A (realRankOne u) S = ownerCoefficientForce A u * S * ownerCoefficientForce A u := by
  simp only [covarianceSource, realRankOne, Matrix.vecMulVec_apply, ownerCoefficientForce,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

theorem supported_rankOne_source_reconstruct (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {u : ι → ℝ}
    (hu : u ∈ LinearMap.range C.mulVecLin) (S : Matrix n n ℂ) :
    let V := krausSupportEmbedding (covarianceKraus A C)
    V * (Vᴴ * covarianceSource A (realRankOne u) S * V) * Vᴴ = covarianceSource A (realRankOne u) S := by
  dsimp only
  rw [covarianceSource_rankOne_force]
  calc
    _ = (krausSupportProjection (covarianceKraus A C) * ownerCoefficientForce A u) * S *
      (ownerCoefficientForce A u * krausSupportProjection (covarianceKraus A C)) := by
        simp only [krausSupportProjection, Matrix.mul_assoc]
    _ = _ := by rw [ownerCoefficientForce_projection_left A hA hC hu,
      ownerCoefficientForce_projection_right A hA hC hu]

/-- The source of the entire shaving line remains in the original constructed
physical support; this exact identity holds for every real line parameter. -/
theorem supported_shaving_source_reconstruct (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {u : ι → ℝ}
    (hu : u ∈ LinearMap.range C.mulVecLin) (S : Matrix n n ℂ) (hS : S.PosSemidef) (t : ℝ) :
    let V := krausSupportEmbedding (covarianceKraus A C)
    V * (Vᴴ * covarianceSource A (C - t • realRankOne u) S * V) * Vᴴ =
      covarianceSource A (C - t • realRankOne u) S := by
  dsimp only
  rw [covarianceSource_sub_covariance, covarianceSource_smul_covariance]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [supported_rankOne_source_reconstruct A hA hC hu S]
  congr 1
  rw [covarianceSource_eq_kraus A hA hC]
  have h := krausCompressedSource_reconstruct (covarianceKraus A C) hS
  rw [krausCompressedSource_eq_compression] at h
  exact h


/-- Covariance source differentiated in the fixed actual owner support. -/
def ownerCompressedCovarianceAtDensity (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) : selfAdjoint (Matrix ι ι ℝ) →L[ℝ]
      selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport (covarianceKraus A C))))
        (Fin (Module.finrank ℂ (krausSupport (covarianceKraus A C)))) ℂ) :=
  (hermitianRectangularCompressionCLM (krausSupportEmbedding (covarianceKraus A C))).comp
    (covarianceAtDensity A S)

theorem ownerCompressedCovarianceAtDensity_coe (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (K : selfAdjoint (Matrix ι ι ℝ)) :
    (ownerCompressedCovarianceAtDensity A C S K : Matrix _ _ ℂ) =
      (krausSupportEmbedding (covarianceKraus A C))ᴴ * covarianceSource A K S *
        krausSupportEmbedding (covarianceKraus A C) := by
  simp only [ownerCompressedCovarianceAtDensity, ContinuousLinearMap.comp_apply,
    hermitianRectangularCompressionCLM_coe, covarianceAtDensity_apply,
    hermitianCovarianceSource_coe A hA]

/-- The initial source in those fixed coordinates is the actual compressed source. -/
theorem ownerCompressedCovarianceAtDensity_base (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosSemidef) (S : selfAdjoint (Matrix n n ℂ)) :
    (ownerCompressedCovarianceAtDensity A C S C : Matrix _ _ ℂ) =
      krausCompressedSource (covarianceKraus A C) S := by
  rw [ownerCompressedCovarianceAtDensity_coe A hA, covarianceSource_eq_kraus A hA hC,
    krausCompressedSource_eq_compression]

/-- Exact derivative of the fixed-density objective along supported covariance shaving. -/
theorem hasDerivAt_ownerObjective_supported_shave (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (hC : (C : Matrix ι ι ℝ).PosSemidef)
    (u : ι → ℝ) (hu : u ∈ LinearMap.range (C : Matrix ι ι ℝ).mulVecLin)
    (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    let B := covarianceKraus A C
    let V := krausSupportEmbedding B
    let Z := transportOptimizer (krausCompressedDensity B S) (krausCompressedSource B S)
    HasDerivAt (fun t : ℝ => ownerObjective H A ((C : Matrix ι ι ℝ) - t • realRankOne u) θ S)
      (-(u ⬝ᵥ (covarianceGram A S (V * Z * Vᴴ) *ᵥ u))) 0 := by
  let B := covarianceKraus A C
  let V := krausSupportEmbedding B
  let Q := krausReducedDensityCLM B S
  let L := ownerCompressedCovarianceAtDensity A C S
  let r := hermitianRankOne u
  have hQ : (Q : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ).PosDef := krausCompressedDensity_posDef B hS
  have hL : (L C : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ).PosDef := by
    rw [ownerCompressedCovarianceAtDensity_base A hA C hC S]
    exact krausCompressedSource_posDef B hS
  have hpath : HasDerivAt (fun t : ℝ => C - t • r) (-r) 0 := by
    simpa only [zero_sub, one_smul] using (hasDerivAt_const (0 : ℝ) C).sub
      ((hasDerivAt_id (0 : ℝ)).smul_const r)
  have hsource : HasDerivAt (fun t : ℝ => L (C - t • r)) (-(L r)) 0 := by
    simpa only [map_neg] using L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hpath
  have hpair := (hasDerivAt_const (0 : ℝ) Q).prodMk hsource
  have hf : HasDerivAt (fun t : ℝ => doubleFidelity (Q, L (C - t • r)))
      (jointTransportFunctional (transportOptimizer (Q : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ) (L C)) (0, -(L r))) 0 := by
    have ho : HasFDerivAt doubleFidelity
        (jointTransportFunctional (transportOptimizer (Q : Matrix (Fin (Module.finrank ℂ (krausSupport B)))
          (Fin (Module.finrank ℂ (krausSupport B))) ℂ) (L C)))
        ((fun t : ℝ => (Q, L (C - t • r))) 0) := by
      simpa only [zero_smul, sub_zero] using hasFDerivAt_doubleFidelity Q (L C) hQ hL
    exact ho.comp_hasDerivAt (0 : ℝ) hpair
  have hd : jointTransportFunctional (transportOptimizer (Q : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ) (L C)) (0, -(L r)) =
      -(u ⬝ᵥ (covarianceGram A S (V * transportOptimizer (krausCompressedDensity B S)
        (krausCompressedSource B S) * Vᴴ) *ᵥ u)) := by
    rw [jointTransportFunctional_apply]
    simp only [ZeroMemClass.coe_zero, Matrix.mul_zero, realTrace_zero, zero_add,
      AddSubgroup.coe_neg, Matrix.mul_neg, realTrace_neg]
    congr 1
    rw [← realTrace_covarianceSource_rankOne_eq A S _ u]
    change realTrace (transportOptimizer (krausCompressedDensity B S) (L C) * (L r : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ)) = _
    rw [ownerCompressedCovarianceAtDensity_base A hA C hC S,
      ownerCompressedCovarianceAtDensity_coe A hA]
    change realTrace (_ * (Vᴴ * covarianceSource A (realRankOne u) S * V)) = _
    rw [show realTrace (transportOptimizer (krausCompressedDensity B S) (krausCompressedSource B S) *
        (Vᴴ * covarianceSource A (realRankOne u) S * V)) =
      realTrace ((transportOptimizer (krausCompressedDensity B S) (krausCompressedSource B S) *
        Vᴴ * covarianceSource A (realRankOne u) S) * V) by simp only [Matrix.mul_assoc],
      realTrace_rectangular_mul_comm]
    simp only [Matrix.mul_assoc, hermitianRankOne]
  rw [hd] at hf
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, (L (C - t • r) : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ).PosDef := by
    have hc : Tendsto (fun t : ℝ => L (C - t • r)) (𝓝 (0 : ℝ)) (𝓝 (L C)) := by
      simpa only [zero_smul, sub_zero] using hsource.continuousAt.tendsto
    exact hc.eventually (eventually_posDef_of_posDef (L C) hL)
  have hg := ((hasDerivAt_const (0 : ℝ) (realTrace (H * (S : Matrix n n ℂ)))).add hf).add
    (hasDerivAt_const (0 : ℝ) (2 * θ * realTrace (CFC.sqrt (S : Matrix n n ℂ))))
  simp only [zero_add, add_zero] at hg
  apply hg.congr_of_eventuallyEq
  filter_upwards [hevent] with t ht
  unfold ownerObjective
  congr 2
  change 2 * fidelity (S : Matrix n n ℂ) (covarianceSource A ((C : Matrix ι ι ℝ) - t • realRankOne u) S) =
    2 * fidelity (Q : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ) (L (C - t • r) : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ)
  congr 1
  have hr := supported_shaving_source_reconstruct A hA hC hu S hS.posSemidef t
  have hc : (L (C - t • r) : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ) =
      Vᴴ * covarianceSource A ((C : Matrix ι ι ℝ) - t • realRankOne u) S * V := by
    rw [ownerCompressedCovarianceAtDensity_coe A hA]
    rfl
  rw [← hr]
  rw [← hc]
  exact fidelity_isometry_compression V (krausSupportEmbedding_isometry B) hS.posSemidef ht.posSemidef


/-- Supported shaving remains PSD on a two-sided neighborhood of zero. -/
theorem eventually_posSemidef_supported_shave {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (u : EuclideanSpace ℝ ι)
    (hu : u ∈ LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap) :
    ∀ᶠ t : ℝ in 𝓝 0, (C - t • realRankOne (WithLp.ofLp u)).PosSemidef := by
  obtain ⟨δ, hδ, hdom⟩ := exists_pos_smul_rankOne_le_of_mem_range hC hu
  filter_upwards [eventually_lt_nhds hδ] with t ht
  have hle : t • realRankOne (WithLp.ofLp u) ≤ δ • realRankOne (WithLp.ofLp u) := by
    apply sub_nonneg.mp
    rw [← sub_smul]
    exact ((realRankOne_posSemidef (WithLp.ofLp u)).smul (sub_nonneg.mpr ht.le)).nonneg
  exact (sub_nonneg.mpr (hle.trans hdom)).posSemidef

/-- The derivative of the actual owner potential at every covariance rank is
minus the actual supported owner Gram in the shaving direction. -/
theorem hasDerivAt_ownerPotential_supported_shave [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (u : EuclideanSpace ℝ ι)
    (hu : u ∈ LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap)
    {θ : ℝ} (hθ : 0 < θ) :
    HasDerivAt (fun t : ℝ => ownerPotential (H : Matrix n n ℂ) A
      (C - t • realRankOne (WithLp.ofLp u)) θ)
      (-(WithLp.ofLp u ⬝ᵥ (observedOwnedGram H A C θ *ᵥ WithLp.ofLp u))) 0 := by
  let Cₛ : selfAdjoint (Matrix ι ι ℝ) := ⟨C, hC.isHermitian⟩
  let S := hermitianDensityOptimizer (H : Matrix n n ℂ) (covarianceKraus A C) θ
  let f := fun t : ℝ => ownerPotential (H : Matrix n n ℂ) A
    (C - t • realRankOne (WithLp.ofLp u)) θ
  let g := fun t : ℝ => ownerObjective (H : Matrix n n ℂ) A
    (C - t • realRankOne (WithLp.ofLp u)) θ S
  have hf : DifferentiableAt ℝ f 0 :=
    differentiableAt_ownerPotential_supported_shave (H : Matrix n n ℂ) A hA hC u hu hθ
  have hg : HasDerivAt g (-(WithLp.ofLp u ⬝ᵥ (observedOwnedGram H A C θ *ᵥ WithLp.ofLp u))) 0 := by
    have hd := hasDerivAt_ownerObjective_supported_shave (H : Matrix n n ℂ) A hA Cₛ hC
      (WithLp.ofLp u) (covariance_mem_mulVec_range hu) θ S
      (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) (covarianceKraus A C) hθ)
    dsimp only at hd
    simpa only [observedOwnedGram, observedOwnedTransport, observedSourceTransport,
      observedSourceDensity, observedOwnerDensity,
      krausReducedFamily_channel (covarianceKraus A C) (covarianceKraus_isHermitian A hA C)] using hd
  have hbase : f 0 = g 0 := by
    simp only [f, g, zero_smul, sub_zero]
    exact ownerPotential_eq_chosenObjective (H : Matrix n n ℂ) A hA θ Cₛ hC
  have hmin : IsLocalMin (fun t => f t - g t) 0 := by
    filter_upwards [eventually_posSemidef_supported_shave hC u hu] with t ht
    change f 0 - g 0 ≤ f t - g t
    rw [hbase, sub_self]
    apply sub_nonneg.mpr
    change ownerObjective (H : Matrix n n ℂ) A _ θ S ≤ ownerPotential (H : Matrix n n ℂ) A _ θ
    rw [ownerObjective_eq_densityObjective (H : Matrix n n ℂ) A hA ht,
      ownerPotential_eq_densityPotential (H : Matrix n n ℂ) A hA ht]
    exact densityObjective_le_potential (H : Matrix n n ℂ) _ θ
      (densityOptimizer_mem (H : Matrix n n ℂ) (covarianceKraus A C) θ)
  have hz := hmin.hasDerivAt_eq_zero (hf.hasDerivAt.sub hg)
  have he := sub_eq_zero.mp hz
  have hd := hf.hasDerivAt
  rw [he] at hd
  exact hd

end MatrixSpencer

