import MatrixSpencer.CovarianceGram
import MatrixSpencer.BalancedTransport
import MatrixSpencer.InverseComparison

/-!
# Factoring the actual covariance Gram on its owned range

The derivative cap is used only on the genuine range of the PSD covariance.
Factoring by its square root does not require an inverse of that covariance.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

omit [DecidableEq ι] [DecidableEq n] in
theorem covarianceGram_mixed (A : ι → Matrix n n ℂ) (R : Matrix ι ι ℝ)
    (S Z : Matrix n n ℂ) :
    covarianceGram (mixedKraus A R) S Z = Rᵀ * covarianceGram A S Z * R := by
  ext a b
  simp only [covarianceGram, mixedKraus, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, realTrace_sum, realTrace_smul,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The square root and the covariance have exactly the same actual Euclidean range. -/
theorem realPosSemidef_sqrt_range {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt C)).toLinearMap =
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap := by
  have hR := (CFC.sqrt_nonneg C).posSemidef.isHermitian
  have he (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
      Matrix.toEuclideanCLM (𝕜 := ℝ) A x = 0 ↔ A *ᵥ WithLp.ofLp x = 0 := by
    constructor
    · intro h
      simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_zero] using congrArg WithLp.ofLp h
    · intro h
      apply WithLp.ofLp_injective
      simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_zero] using h
  have hk : LinearMap.ker (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap =
      LinearMap.ker (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt C)).toLinearMap := by
    ext x
    change Matrix.toEuclideanCLM (𝕜 := ℝ) C x = 0 ↔ Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt C) x = 0
    rw [he, he]
    have h := Matrix.conjTranspose_mul_self_mulVec_eq_zero (CFC.sqrt C) (WithLp.ofLp x)
    rwa [hR.eq, CFC.sqrt_mul_sqrt_self C hC.nonneg] at h
  have hCsym := (show IsSelfAdjoint C from hC.isHermitian).map (Matrix.toEuclideanCLM (𝕜 := ℝ))
    |>.isSymmetric
  have hRsym := (show IsSelfAdjoint (CFC.sqrt C) from hR).map (Matrix.toEuclideanCLM (𝕜 := ℝ))
    |>.isSymmetric
  exact le_antisymm
    ((ContinuousLinearMap.ker_le_ker_iff_range_le_range hRsym hCsym).mp hk.le)
    ((ContinuousLinearMap.ker_le_ker_iff_range_le_range hCsym hRsym).mp hk.ge)

omit [Fintype n] [DecidableEq n] in
theorem realSqrt_mulVec_mem_range {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (x : ι → ℝ) :
    WithLp.toLp 2 (CFC.sqrt C *ᵥ x) ∈
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap := by
  rw [← realPosSemidef_sqrt_range hC]
  refine ⟨WithLp.toLp 2 x, ?_⟩
  apply WithLp.ofLp_injective
  simp only [ContinuousLinearMap.coe_coe, Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_toLp]

/-- A range-restricted derivative cap gives the full factored coefficient cap. -/
theorem realSqrt_gram_cap_of_range {C Γ : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (hC1 : C ≤ 1) (hΓ : Γ.PosSemidef) {t : ℝ} (ht : 0 ≤ t)
    (hcap : ∀ u : EuclideanSpace ℝ ι,
      u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap →
      WithLp.ofLp u ⬝ᵥ (Γ *ᵥ WithLp.ofLp u) ≤ t * (WithLp.ofLp u ⬝ᵥ WithLp.ofLp u)) :
    CFC.sqrt C * Γ * CFC.sqrt C ≤ t • (1 : Matrix ι ι ℝ) := by
  have hR := (CFC.sqrt_nonneg C).posSemidef.isHermitian
  have hRt : (CFC.sqrt C)ᵀ = CFC.sqrt C := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.eq
  have hlow : CFC.sqrt C * Γ * CFC.sqrt C ≤ t • C := by
    have hpos : (CFC.sqrt C * Γ * CFC.sqrt C).PosSemidef := by
      simpa only [hR.eq] using hΓ.conjTranspose_mul_mul_same (CFC.sqrt C)
    apply InverseComparison.le_of_quadratic_le hpos.isHermitian (hC.smul ht).isHermitian
    intro x
    have h := hcap (WithLp.toLp 2 (CFC.sqrt C *ᵥ x)) (realSqrt_mulVec_mem_range hC x)
    simp only [WithLp.ofLp_toLp] at h
    have heq : (CFC.sqrt C *ᵥ x) ⬝ᵥ (CFC.sqrt C *ᵥ x) = x ⬝ᵥ (C *ᵥ x) := by
      calc
        _ = x ⬝ᵥ ((CFC.sqrt C)ᵀ *ᵥ (CFC.sqrt C *ᵥ x)) := by
          simpa only [Matrix.transpose_transpose] using
            (InverseComparison.transpose_pairing (CFC.sqrt C)ᵀ x (CFC.sqrt C *ᵥ x)).symm
        _ = _ := by rw [hRt, Matrix.mulVec_mulVec, CFC.sqrt_mul_sqrt_self C hC.nonneg]
    have hquad := InverseComparison.quadratic_congruence (CFC.sqrt C) Γ x
    rw [hRt] at hquad
    rw [hquad]
    simpa only [InverseComparison.quadratic, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, heq] using h
  exact hlow.trans (smul_le_smul_of_nonneg_left hC1 ht)

/-- The balanced physical Gram is exactly the square-root congruence of the original derivative Gram. -/
theorem balanced_covarianceGram_factor (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (S : Matrix n n ℂ) {Z : Matrix n n ℂ} (hZ : Z.PosDef) :
    physicalRealGram (balancedDensity S Z) (balancedKraus (covarianceKraus A C) Z) =
      CFC.sqrt C * covarianceGram A S Z * CFC.sqrt C := by
  have heq : physicalRealGram (balancedDensity S Z) (balancedKraus (covarianceKraus A C) Z) =
      covarianceGram (mixedKraus A (CFC.sqrt C)) S Z := by
    ext a b
    exact balanced_physicalGram_entry (covarianceKraus A C) S hZ a b
  have hRt : (CFC.sqrt C)ᵀ = CFC.sqrt C := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg C).posSemidef.isHermitian.eq
  rw [heq, covarianceGram_mixed, hRt]

/-- Only the cap on owned directions is used to establish the physical cap required by the spectral theorem. -/
theorem balanced_covarianceGram_cap_of_range (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    {S Z : Matrix n n ℂ} (hS : S.PosSemidef) (hZ : Z.PosDef) {t : ℝ} (ht : 0 ≤ t)
    (hcap : ∀ u : EuclideanSpace ℝ ι,
      u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap →
      WithLp.ofLp u ⬝ᵥ (covarianceGram A S Z *ᵥ WithLp.ofLp u) ≤
        t * (WithLp.ofLp u ⬝ᵥ WithLp.ofLp u)) :
    physicalRealGram (balancedDensity S Z) (balancedKraus (covarianceKraus A C) Z) ≤
      algebraMap ℝ (Matrix ι ι ℝ) t := by
  rw [balanced_covarianceGram_factor A C S hZ, Algebra.algebraMap_eq_smul_one]
  exact realSqrt_gram_cap_of_range hC hC1 (covarianceGram_posSemidef A hA S Z hS hZ.posSemidef) ht hcap

end MatrixSpencer
