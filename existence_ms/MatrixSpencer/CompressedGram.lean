import MatrixSpencer.CompressedBudgets
import MatrixSpencer.CovarianceGramFactor

/-!
# The covariance Gram on the actual physical support

The full density is compressed only after the supported forces are accounted
for. Consequently the factored covariance cap is unchanged by this transfer.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

/-- The derivative Gram of supported Kraus forces agrees exactly with its physical compression. -/
theorem covarianceGram_krausReducedFamily (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (S : Matrix n n ℂ)
    (Z₀ : Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ) :
    covarianceGram B S (krausSupportEmbedding B * Z₀ * (krausSupportEmbedding B)ᴴ) =
      covarianceGram (krausReducedFamily B) (krausCompressedDensity B S) Z₀ := by
  ext a b
  change realTrace (S * B a * (krausSupportEmbedding B * Z₀ * (krausSupportEmbedding B)ᴴ) * B b) = _
  let V := krausSupportEmbedding B
  have hV : Vᴴ * V = 1 := krausSupportEmbedding_isometry B
  have ha := krausReducedFamily_reconstruct B hB a
  have hb := krausReducedFamily_reconstruct B hB b
  calc
    _ = realTrace (S * (V * krausReducedFamily B a * Vᴴ) *
        (V * Z₀ * Vᴴ) * (V * krausReducedFamily B b * Vᴴ)) := by rw [ha, hb]
    _ = realTrace (S * V * krausReducedFamily B a * (Vᴴ * V) * Z₀ *
        (Vᴴ * V) * krausReducedFamily B b * Vᴴ) := by simp only [Matrix.mul_assoc]
    _ = realTrace ((S * V * krausReducedFamily B a * Z₀ * krausReducedFamily B b) * Vᴴ) := by
      rw [hV, Matrix.mul_one, Matrix.mul_one]
    _ = _ := by rw [realTrace_rectangular_mul_comm]; simp only [covarianceGram, krausCompressedDensity, V, Matrix.mul_assoc]

/-- Exact coefficient factorization after passing to the actual source support. -/
theorem covarianceGram_compressed_factor (A : ι → Matrix n n ℂ)
    (hA : ∀ a, (A a).IsHermitian) (C : Matrix ι ι ℝ) (S : Matrix n n ℂ)
    (Z₀ : Matrix (Fin (Module.finrank ℂ (krausSupport (covarianceKraus A C))))
      (Fin (Module.finrank ℂ (krausSupport (covarianceKraus A C)))) ℂ) :
    let B := covarianceKraus A C
    let V := krausSupportEmbedding B
    covarianceGram (krausReducedFamily B) (krausCompressedDensity B S) Z₀ =
      CFC.sqrt C * covarianceGram A S (V * Z₀ * Vᴴ) * CFC.sqrt C := by
  dsimp only
  rw [← covarianceGram_krausReducedFamily (covarianceKraus A C)
    (mixedKraus_isHermitian A (CFC.sqrt C) hA) S Z₀]
  change covarianceGram (mixedKraus A (CFC.sqrt C)) S _ = _
  have hRt : (CFC.sqrt C)ᵀ = CFC.sqrt C := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg C).posSemidef.isHermitian.eq
  rw [covarianceGram_mixed, hRt]

/-- The original owned derivative cap yields the same physical Gram cap for the reduced balanced frame. -/
theorem compressed_balancedGram_cap (A : ι → Matrix n n ℂ)
    (hA : ∀ a, (A a).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    {S : Matrix n n ℂ} (hS : S.PosSemidef)
    (Z₀ : Matrix (Fin (Module.finrank ℂ (krausSupport (covarianceKraus A C))))
      (Fin (Module.finrank ℂ (krausSupport (covarianceKraus A C)))) ℂ)
    (hZ₀ : Z₀.PosDef) {t : ℝ} (ht : 0 ≤ t)
    (hcap : let V := krausSupportEmbedding (covarianceKraus A C)
      ∀ u : EuclideanSpace ℝ ι,
        u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap →
        WithLp.ofLp u ⬝ᵥ (covarianceGram A S (V * Z₀ * Vᴴ) *ᵥ WithLp.ofLp u) ≤
          t * (WithLp.ofLp u ⬝ᵥ WithLp.ofLp u)) :
    let B := covarianceKraus A C
    let S₀ := krausCompressedDensity B S
    physicalRealGram (balancedDensity S₀ Z₀) (balancedKraus (krausReducedFamily B) Z₀) ≤
      algebraMap ℝ (Matrix ι ι ℝ) t := by
  dsimp only
  have heq : physicalRealGram (balancedDensity (krausCompressedDensity (covarianceKraus A C) S) Z₀)
      (balancedKraus (krausReducedFamily (covarianceKraus A C)) Z₀) =
      covarianceGram (krausReducedFamily (covarianceKraus A C))
        (krausCompressedDensity (covarianceKraus A C) S) Z₀ := by
    ext a b
    exact balanced_physicalGram_entry _ _ hZ₀ a b
  rw [heq, covarianceGram_compressed_factor A hA C S Z₀, Algebra.algebraMap_eq_smul_one]
  exact realSqrt_gram_cap_of_range hC hC1
    (covarianceGram_posSemidef A hA S _ hS
      (hZ₀.posSemidef.mul_mul_conjTranspose_same (krausSupportEmbedding (covarianceKraus A C)))) ht hcap

end MatrixSpencer
