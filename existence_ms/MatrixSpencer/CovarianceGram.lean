import MatrixSpencer.CovarianceResponse
import MatrixSpencer.SupportShaving

/-! Exact covariance Gram and rank-one shaving forms of the actual envelope derivative. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance covarianceGramCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance covarianceGramPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance covarianceGramCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance

/-- Full physical transport functional, when the physical source is positive definite. -/
def fullCovarianceDerivativeFunctional (A : ι → Matrix n n ℂ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix ι ι ℝ) →L[ℝ] ℝ :=
  (tracePairing (transportOptimizer (S : Matrix n n ℂ) (covarianceSource A C S))).comp
    (covarianceAtDensity A S)

theorem fullCovarianceDerivativeFunctional_apply (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C ΔC : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) :
    fullCovarianceDerivativeFunctional A C S ΔC =
      realTrace (transportOptimizer (S : Matrix n n ℂ) (covarianceSource A C S) *
        covarianceSource A ΔC S) := by
  change realTrace (_ * (covarianceAtDensity A S ΔC : Matrix n n ℂ)) = _
  rw [covarianceAtDensity_apply, hermitianCovarianceSource_coe A hA]

theorem hasStrictFDerivAt_covarianceFidelity_covariance_faithful
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (covarianceSource A C S).PosDef) :
    HasStrictFDerivAt (fun K => covarianceFidelity A (K, S))
      (fullCovarianceDerivativeFunctional A C S) C := by
  let L := covarianceAtDensity A S
  have hcoe (K : selfAdjoint (Matrix ι ι ℝ)) : (L K : Matrix n n ℂ) = covarianceSource A K S := by
    simp only [L, covarianceAtDensity_apply, hermitianCovarianceSource_coe A hA]
  have hL : (L C : Matrix n n ℂ).PosDef := by
    simpa only [L, covarianceAtDensity_apply, hermitianCovarianceSource_coe A hA] using hM
  have hf := (hasStrictFDerivAt_doubleFidelity S (L C) hS hL).comp C
    ((hasStrictFDerivAt_const (𝕜 := ℝ) S C).prodMk L.hasStrictFDerivAt)
  have he : (jointTransportFunctional (transportOptimizer (S : Matrix n n ℂ) (L C))).comp
      ((0 : selfAdjoint (Matrix ι ι ℝ) →L[ℝ] selfAdjoint (Matrix n n ℂ)).prod L) =
      fullCovarianceDerivativeFunctional A C S := by
    apply ContinuousLinearMap.ext
    intro ΔC
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.zero_apply, jointTransportFunctional_apply, ZeroMemClass.coe_zero,
      Matrix.mul_zero, realTrace_zero, zero_add]
    change realTrace (transportOptimizer (S : Matrix n n ℂ) (L C) * (L ΔC : Matrix n n ℂ)) = _
    rw [show (L C : Matrix n n ℂ) = covarianceSource A C S from
      hcoe C]
    rfl
  rw [he] at hf
  have hefun : (fun K => covarianceFidelity A (K, S)) = (fun K => doubleFidelity (S, L K)) := by
    funext K
    change 2 * fidelity (S : Matrix n n ℂ) (covarianceSource A K S) =
      2 * fidelity (S : Matrix n n ℂ) (L K : Matrix n n ℂ)
    rw [show (L K : Matrix n n ℂ) = covarianceSource A K S from hcoe K]
  rw [hefun]
  exact hf

theorem covarianceDerivativeFunctional_eq_full (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (covarianceSource A C S).PosDef) :
    covarianceDerivativeFunctional A C S = fullCovarianceDerivativeFunctional A C S :=
  (hasStrictFDerivAt_covarianceFidelity_covariance A hA C S hC hS).hasFDerivAt.unique
    (hasStrictFDerivAt_covarianceFidelity_covariance_faithful A hA C S hS hM).hasFDerivAt

/-- When the physical source is faithful, its ordinary positive transport gives the actual derivative. -/
theorem fderiv_hermitianOwnerPotential_covariance_apply_faithful [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) (C ΔC : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef)
    (hM : (covarianceSource A C (hermitianDensityOptimizer H (covarianceKraus A C) θ)).PosDef) :
    fderiv ℝ (hermitianOwnerPotential H A θ) C ΔC =
      realTrace (transportOptimizer (hermitianDensityOptimizer H (covarianceKraus A C) θ : Matrix n n ℂ)
        (covarianceSource A C (hermitianDensityOptimizer H (covarianceKraus A C) θ)) *
        covarianceSource A ΔC (hermitianDensityOptimizer H (covarianceKraus A C) θ)) := by
  rw [(hasFDerivAt_hermitianOwnerPotential_covariance H A hA hθ C hC).fderiv,
    covarianceDerivativeFunctional_eq_full A hA C _ hC
      (hermitianDensityOptimizer_posDef H (covarianceKraus A C) hθ) hM]
  exact fullCovarianceDerivativeFunctional_apply A hA C ΔC _

/-- The coefficient Gram entries in the original matrix labels. -/
def covarianceGram (A : ι → Matrix n n ℂ) (S Z : Matrix n n ℂ) : Matrix ι ι ℝ :=
  fun i j => realTrace (S * A i * Z * A j)

omit [DecidableEq ι] [DecidableEq n] in
/-- Symmetric coefficient variations contract with the Gram in the stated index order. -/
theorem realTrace_covarianceSource_eq_gram (A : ι → Matrix n n ℂ)
    (S Z : Matrix n n ℂ) (C : selfAdjoint (Matrix ι ι ℝ)) :
    realTrace (Z * covarianceSource A C S) = ∑ i, ∑ j, (C : Matrix ι ι ℝ) i j * covarianceGram A S Z i j := by
  have hC : ∀ i j, (C : Matrix ι ι ℝ) j i = (C : Matrix ι ι ℝ) i j := by
    intro i j
    have h := congrArg (fun M : Matrix ι ι ℝ => M i j) C.property
    simpa only [star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial] using h
  simp only [covarianceSource, Matrix.mul_sum, Matrix.mul_smul, realTrace_sum, realTrace_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hC]
  congr 1
  change realTrace (Z * (A j * S * A i)) = realTrace (S * A i * Z * A j)
  calc
    _ = realTrace ((Z * A j) * (S * A i)) := by simp only [Matrix.mul_assoc]
    _ = realTrace ((S * A i) * (Z * A j)) := realTrace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Rank-one covariance direction as a real Hermitian matrix. -/
def hermitianRankOne (u : ι → ℝ) : selfAdjoint (Matrix ι ι ℝ) :=
  ⟨realRankOne u, (realRankOne_posSemidef u).isHermitian⟩

omit [DecidableEq ι] [DecidableEq n] in
theorem realTrace_covarianceSource_shaving_eq (A : ι → Matrix n n ℂ)
    (S Z : Matrix n n ℂ) (u : ι → ℝ) :
    realTrace (Z * covarianceSource A (-hermitianRankOne u) S) =
      -(u ⬝ᵥ (covarianceGram A S Z *ᵥ u)) := by
  have he := realTrace_covarianceSource_eq_gram A S Z (-hermitianRankOne u)
  simp only [AddSubgroup.coe_neg] at he
  rw [he]
  simp only [hermitianRankOne, Matrix.neg_apply, realRankOne,
    Matrix.vecMulVec_apply, neg_mul, Finset.sum_neg_distrib, dotProduct, Matrix.mulVec,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Actual infinitesimal shaving cost in original coefficient labels. -/
theorem fderiv_hermitianOwnerPotential_shaving [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ)) (u : ι → ℝ)
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    fderiv ℝ (hermitianOwnerPotential H A θ) C (-hermitianRankOne u) =
      -(u ⬝ᵥ (covarianceGram A
        (hermitianDensityOptimizer H (covarianceKraus A C) θ)
        (covarianceSupportTransport A C (hermitianDensityOptimizer H (covarianceKraus A C) θ)) *ᵥ u)) := by
  rw [fderiv_hermitianOwnerPotential_covariance_apply H A hA hθ C _ hC]
  exact realTrace_covarianceSource_shaving_eq A _ _ u

omit [Fintype ι] [DecidableEq ι] [DecidableEq n] in
/-- The Gram is symmetric for Hermitian physical data. -/
theorem covarianceGram_isHermitian (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (S Z : Matrix n n ℂ) (hS : S.IsHermitian) (hZ : Z.IsHermitian) :
    (covarianceGram A S Z).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, covarianceGram]
  calc
    realTrace (S * A j * Z * A i) = realTrace ((A j * Z * A i) * S) := by
      simpa only [Matrix.mul_assoc] using realTrace_mul_comm S (A j * Z * A i)
    _ = realTrace ((S * A i * Z * A j)ᴴ) := by
      simp only [Matrix.conjTranspose_mul, hS.eq, hZ.eq, (hA i).eq, (hA j).eq, Matrix.mul_assoc]
    _ = realTrace (S * A i * Z * A j) := by
      unfold realTrace
      rw [Matrix.trace_conjTranspose]
      rfl

omit [DecidableEq ι] [DecidableEq n] in
theorem realTrace_covarianceSource_rankOne_eq (A : ι → Matrix n n ℂ)
    (S Z : Matrix n n ℂ) (u : ι → ℝ) :
    realTrace (Z * covarianceSource A (hermitianRankOne u) S) =
      u ⬝ᵥ (covarianceGram A S Z *ᵥ u) := by
  rw [realTrace_covarianceSource_eq_gram A S Z (hermitianRankOne u)]
  simp only [hermitianRankOne, realRankOne, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positivity of the concrete covariance Gram follows from source positivity. -/
theorem covarianceGram_posSemidef (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (S Z : Matrix n n ℂ) (hS : S.PosSemidef) (hZ : Z.PosSemidef) :
    (covarianceGram A S Z).PosSemidef := by
  refine ⟨covarianceGram_isHermitian A hA S Z hS.isHermitian hZ.isHermitian, ?_⟩
  intro u
  simp only [star_trivial]
  rw [← realTrace_covarianceSource_rankOne_eq A S Z u]
  exact realTrace_mul_nonneg hZ (covarianceSource_posSemidef A hA (realRankOne_posSemidef u) hS)

/-- The support transport used by the actual envelope derivative is positive semidefinite. -/
theorem covarianceSupportTransport_posSemidef (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef) : (covarianceSupportTransport A C S).PosSemidef :=
  (transportOptimizer_posDef (krausCompressedDensity_posDef A hS)
    (covarianceCompressedSource_posDef A hA hC hS)).posSemidef.mul_mul_conjTranspose_same
      (krausSupportEmbedding A)

/-- Faithful-source shaving, with the actual ordinary physical transport. -/
theorem fderiv_hermitianOwnerPotential_shaving_faithful [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ)) (u : ι → ℝ)
    (hC : (C : Matrix ι ι ℝ).PosDef)
    (hM : (covarianceSource A C (hermitianDensityOptimizer H (covarianceKraus A C) θ)).PosDef) :
    fderiv ℝ (hermitianOwnerPotential H A θ) C (-hermitianRankOne u) =
      -(u ⬝ᵥ (covarianceGram A
        (hermitianDensityOptimizer H (covarianceKraus A C) θ)
        (transportOptimizer (hermitianDensityOptimizer H (covarianceKraus A C) θ : Matrix n n ℂ)
          (covarianceSource A C (hermitianDensityOptimizer H (covarianceKraus A C) θ))) *ᵥ u)) := by
  rw [fderiv_hermitianOwnerPotential_covariance_apply_faithful H A hA hθ C _ hC hM]
  exact realTrace_covarianceSource_shaving_eq A _ _ u

end
end MatrixSpencer
