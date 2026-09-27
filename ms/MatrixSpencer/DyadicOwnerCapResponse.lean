import MatrixSpencer.DyadicModelBalancedResponse
import MatrixSpencer.DyadicSupportedPotentialResponse
import MatrixSpencer.DyadicOwnerFrame
import MatrixSpencer.DyadicCoefficientResponse

/-! The actual dyadic owner coefficient response under its owned Gram cap.
Source compression and the comparison model are fully discharged internally. -/

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
set_option maxHeartbeats 800000
namespace MatrixSpencer
namespace DyadicOwnerCapResponse
open DyadicSingularResponseTransfer DyadicModelBalancedResponse DyadicOwnerFrame

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance ownerCapDyadicCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance ownerCapDyadicSpace {j : Type*} [Fintype j] [DecidableEq j] :
    NormedSpace ℝ (selfAdjoint (Matrix j j ℂ)) := inferInstance

/-- The actual potential Hessian is compared with the faithful model in whitened coordinates. -/
theorem potential_hessian_supported_le_model_whitened [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (F : selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ)) :
    let S := hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) B m θ
    let S₀ := krausReducedDensityCLM B S
    let B₀ := krausReducedFamily B
    let Z₀ := transportOptimizer (S₀ : Matrix _ _ ℂ) (krausChannel B₀ (S₀ : Matrix _ _ ℂ))
    let X := hermitianRectangularEmbeddingCLM (krausSupportEmbedding B) F
    fderiv ℝ (fun K => fderiv ℝ (hermitianDyadicDensityPotential B m θ) K) H X X ≤
      ComplexInverseComparison.quadratic (balancedModelWhitenedFull B₀ m (coefficient m θ) S₀ Z₀)⁻¹
        (CFC.sqrt (jordanSuper (balancedDensity S₀ Z₀)) *ᵥ
          matrixVector (CFC.sqrt Z₀ * (F : Matrix _ _ ℂ) * CFC.sqrt Z₀)) := by
  dsimp only
  have h₁ := DyadicSupportedPotentialResponse.potential_hessian_supported_le_model H B hB m hm θ hθ F
  have h₂ := modelDensityInverse_le_whitened_inverse
    (n := Fin (Module.finrank ℂ (krausSupport B)))
    (krausReducedFamily B) (krausReducedFamily_isHermitian B hB) m (coefficient m θ)
    (coefficient_pos m hθ) (krausReducedDensityCLM B (hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) B m θ)) F
    (krausCompressedDensity_posDef B (hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) B m hm θ hθ))
    (krausReducedFamily_source_posDef B hB
      (hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) B m hm θ hθ))
  dsimp only at h₁ h₂
  exact h₁.trans h₂

lemma hermitianFamily_reduced_embedding (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (a : ι) :
    hermitianRectangularEmbeddingCLM (krausSupportEmbedding B)
      (hermitianMatrixFamily (krausReducedFamily B) (krausReducedFamily_isHermitian B hB) a) =
        hermitianMatrixFamily B hB a := by
  apply Subtype.ext
  simp only [hermitianRectangularEmbeddingCLM_coe, hermitianMatrixFamily,
    krausReducedFamily_reconstruct B hB]

/-- The full actual observed response is bounded at every physical source rank. -/
theorem singular_observed_response_le [Nonempty n] [DecidableEq ι]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    let S := hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) B m θ
    let S₀ := krausReducedDensityCLM B S
    let B₀ := krausReducedFamily B
    let Z₀ := transportOptimizer (S₀ : Matrix _ _ ℂ) (krausChannel B₀ (S₀ : Matrix _ _ ℂ))
    dyadicKrausObservedResponse H B hB m θ ≤
      realTrace (jordanForceFrame (balancedDensity S₀ Z₀) (balancedKraus B₀ Z₀) *
        (balancedModelWhitenedFull B₀ m (coefficient m θ) S₀ Z₀)⁻¹) := by
  dsimp only
  rw [dyadicKrausObservedResponse, jordanForceFrame_trace_eq_half_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  apply Finset.sum_le_sum
  intro a _
  have h := potential_hessian_supported_le_model_whitened H B hB m hm θ hθ
    (hermitianMatrixFamily (krausReducedFamily B) (krausReducedFamily_isHermitian B hB) a)
  dsimp only at h
  rw [hermitianFamily_reduced_embedding B hB a] at h
  exact h

/-- The actual half-Hessian coefficient matrix obeys the dyadic cap bound, at every source rank. -/
theorem owner_response_le_of_ownedGram_cap [Nonempty n] [DecidableEq ι]
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    (m : ℕ) (hm : 1 ≤ m) {θ L : ℝ} (hθ : 0 < θ) (hL : 0 < L) (hk : 0 < Fintype.card ι)
    (hcap : ∀ u : EuclideanSpace ℝ ι,
      u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap →
      WithLp.ofLp u ⬝ᵥ (observedOwnedGram H A C m θ *ᵥ WithLp.ofLp u) ≤
        (L / Real.sqrt (Fintype.card ι : ℝ)) * (WithLp.ofLp u ⬝ᵥ WithLp.ofLp u)) :
    realTrace (C * dyadicOwnerCoefficientResponse A hA C m θ H) ≤
      2 * Real.sqrt (Fintype.card ι : ℝ) +
        (6 * L ^ (1 / (2 : ℝ) ^ m) / (θ * (1 / (2 : ℝ) ^ m))) *
          (Fintype.card ι : ℝ) ^ (1 - 1 / (2 : ℝ) ^ m) := by
  let B := covarianceKraus A C
  have hB : ∀ a, (B a).IsHermitian := covarianceKraus_isHermitian A hA C
  let B₀ := krausReducedFamily B
  let S₀ := observedSourceDensity H A C m θ
  let Z₀ := observedSourceTransport H A C m θ
  have hS₀ : S₀.PosDef := observedSourceDensity_posDef H A C m hm hθ
  have hZ₀ : Z₀.PosDef := observedSourceTransport_posDef H A hA C m hm hθ
  have hf := observedOwner_balanced_family_data H A hA C m hm hθ
  have hbud := observedOwner_three_budgets H A hA hN hC0 hC1 m hm hθ
  have hgram := observedOwner_balancedGram_cap H A hA hC0 hC1 m hm hθ
    (show 0 ≤ L / Real.sqrt (Fintype.card ι : ℝ) by positivity) hcap
  have htrace := DyadicObservedCapResponse.model_response_trace_le m hm
    (balancedKraus B₀ Z₀) hf.1 hθ hS₀ hZ₀ (Nat.cast_pos.mpr hk) hL
    hbud.1 hbud.2.1 hbud.2.2 hgram hf.2
  rw [dyadicOwnerCoefficientResponse_trace_eq A hA hC0 m θ H]
  have hresponse := singular_observed_response_le H B hB m hm θ hθ
  have he : ((2 ^ m : ℕ) : ℝ) / (2 * θ) = coefficient m θ := by
    simp only [coefficient, Nat.cast_pow, Nat.cast_ofNat]
  rw [he] at htrace
  exact hresponse.trans htrace

end DyadicOwnerCapResponse
end MatrixSpencer
