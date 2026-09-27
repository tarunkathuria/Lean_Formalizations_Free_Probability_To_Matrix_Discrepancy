import MatrixSpencer.RectangularRidgeOwnerFrame
import MatrixSpencer.DyadicOwnerCapResponse

/-! Pointwise response stability under additional concave regularization.
The density, the owned Gram cap, and the actual inverse Hessian all refer to
the same point. No comparison between optimizers of different objectives is
used. The numerical algorithm still has to construct that point and cap. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeResponse
open DyadicSingularResponseTransfer DyadicModelBalancedResponse RectangularRidgeOwnerFrame
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance ridgeResponseLocal1 {j : Type*} [Fintype j] [DecidableEq j] : CStarAlgebra (Matrix j j ℂ) := {}
local instance ridgeResponseLocal2 {j : Type*} [Fintype j] [DecidableEq j] :
    NormedSpace ℝ (selfAdjoint (Matrix j j ℂ)) := inferInstance
local instance ridgeResponseLocal3 : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance ridgeResponseLocal4 : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
set_option maxHeartbeats 1200000

abbrev TangentInverse (n : Type*) [Fintype n] [DecidableEq n] :=
  densityTangent (n := n) ≃L[ℝ] (densityTangent (n := n) →L[ℝ] ℝ)

/-- Extra nonnegative curvature may be present in the actual negative Hessian.
Only domination at this particular density is needed for inverse response. -/
theorem constrained_inverse_response_le_model
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (J : TangentInverse n)
    (hJ : ∀ X : densityTangent (n := n),
      dyadicDensityNegativeHessian H B m θ S X X ≤ J X X)
    (f : selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ) →L[ℝ] ℝ) :
    let P := (krausReducedDensityCLM B).comp (densityTangent (n := n)).subtypeL
    (f.comp P) (J.symm (f.comp P)) ≤
      f ((reducedModelDensityEquiv B m θ hθ S hS).symm f) := by
  dsimp only
  refine bilinear_inverse_pullback_le J (reducedModelDensityEquiv B m θ hθ S hS)
    ((krausReducedDensityCLM B).comp (densityTangent (n := n)).subtypeL) ?_ ?_ ?_ f
  · exact modelDensityBilinear_symmetric (krausReducedFamily B) m (coefficient m θ)
      (coefficient_pos m hθ) (krausReducedDensityCLM B S) (krausCompressedDensity_posDef B hS)
  · exact modelDensityBilinear_nonneg (krausReducedFamily B) m (coefficient m θ)
      (coefficient_pos m hθ) (krausReducedDensityCLM B S) (krausCompressedDensity_posDef B hS)
  · intro X
    exact (modelDensityBilinear_reducedFamily_le H B hB m hm θ hθ S X hS).trans (hJ X)

theorem supported_response_le_whitened
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (J : TangentInverse n)
    (hJ : ∀ X : densityTangent (n := n),
      dyadicDensityNegativeHessian H B m θ S X X ≤ J X X)
    (F : selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ)) :
    let S₀ := krausReducedDensityCLM B S
    let B₀ := krausReducedFamily B
    let Z₀ := transportOptimizer (S₀ : Matrix _ _ ℂ) (krausChannel B₀ (S₀ : Matrix _ _ ℂ))
    let X := hermitianRectangularEmbeddingCLM (krausSupportEmbedding B) F
    densityCenterFunctional X (J.symm (densityCenterFunctional X)) ≤
      ComplexInverseComparison.quadratic (balancedModelWhitenedFull B₀ m (coefficient m θ) S₀ Z₀)⁻¹
        (CFC.sqrt (jordanSuper (balancedDensity S₀ Z₀)) *ᵥ
          matrixVector (CFC.sqrt Z₀ * (F : Matrix _ _ ℂ) * CFC.sqrt Z₀)) := by
  dsimp only
  have h₁ := constrained_inverse_response_le_model H B hB m hm θ hθ S hS J hJ
    (tracePairing (F : Matrix _ _ ℂ))
  have h₂ := modelDensityInverse_le_whitened_inverse (krausReducedFamily B)
    (krausReducedFamily_isHermitian B hB) m (coefficient m θ) (coefficient_pos m hθ)
    (krausReducedDensityCLM B S) F (krausCompressedDensity_posDef B hS)
    (krausReducedFamily_source_posDef B hB hS)
  rw [densityCenterFunctional_supported_pullback B F]
  exact h₁.trans h₂

/-- The observed response is half the sum of the actual constrained inverse
quadratic forms in the Kraus directions. -/
def observedResponse (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian)
    (J : TangentInverse n) : ℝ :=
  2⁻¹ * ∑ a, densityCenterFunctional (hermitianMatrixFamily B hB a)
    (J.symm (densityCenterFunctional (hermitianMatrixFamily B hB a)))

theorem observed_response_le_model [DecidableEq ι]
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (J : TangentInverse n)
    (hJ : ∀ X : densityTangent (n := n),
      dyadicDensityNegativeHessian H B m θ S X X ≤ J X X) :
    let S₀ := krausReducedDensityCLM B S
    let B₀ := krausReducedFamily B
    let Z₀ := transportOptimizer (S₀ : Matrix _ _ ℂ) (krausChannel B₀ (S₀ : Matrix _ _ ℂ))
    observedResponse B hB J ≤
      realTrace (jordanForceFrame (balancedDensity S₀ Z₀) (balancedKraus B₀ Z₀) *
        (balancedModelWhitenedFull B₀ m (coefficient m θ) S₀ Z₀)⁻¹) := by
  dsimp only
  rw [observedResponse, jordanForceFrame_trace_eq_half_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  apply Finset.sum_le_sum
  intro a _
  have h := supported_response_le_whitened H B hB m hm θ hθ S hS J hJ
    (hermitianMatrixFamily (krausReducedFamily B) (krausReducedFamily_isHermitian B hB) a)
  dsimp only at h
  rw [DyadicOwnerCapResponse.hermitianFamily_reduced_embedding B hB a] at h
  exact h

/-- At any positive density of trace at most one, an owned-Gram cap gives the
same dyadic response bound for every dominating actual tangent Hessian. -/
theorem owner_response_le_of_ownedGram_cap [DecidableEq ι]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, ‖A i‖ ≤ 1) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    (m : ℕ) (hm : 1 ≤ m) {θ L : ℝ} (hθ : 0 < θ) (hL : 0 < L)
    (hk : 0 < Fintype.card ι) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (htr : realTrace (S : Matrix n n ℂ) ≤ 1)
    (J : TangentInverse n)
    (hJ : ∀ X : densityTangent (n := n),
      dyadicDensityNegativeHessian H (covarianceKraus A C) m θ S X X ≤ J X X)
    (hcap : ∀ u : EuclideanSpace ℝ ι,
      u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap →
      WithLp.ofLp u ⬝ᵥ (ownedGram A C S *ᵥ WithLp.ofLp u) ≤
        (L / Real.sqrt (Fintype.card ι : ℝ)) * (WithLp.ofLp u ⬝ᵥ WithLp.ofLp u)) :
    observedResponse (covarianceKraus A C) (covarianceKraus_isHermitian A hA C) J ≤
      2 * Real.sqrt (Fintype.card ι : ℝ) +
        (6 * L ^ (1 / (2 : ℝ) ^ m) / (θ * (1 / (2 : ℝ) ^ m))) *
          (Fintype.card ι : ℝ) ^ (1 - 1 / (2 : ℝ) ^ m) := by
  let B := covarianceKraus A C
  let B₀ := krausReducedFamily B
  let S₀ := sourceDensity A C S
  let Z₀ := sourceTransport A C S
  have hS₀ : S₀.PosDef := sourceDensity_posDef A C hS
  have hZ₀ : Z₀.PosDef := sourceTransport_posDef A hA C hS
  have hf := balanced_family_data A hA C hS
  have hbud := three_budgets A hA hN hC hC1 hS htr
  have hgram := balancedGram_cap A hA hC hC1 hS
    (show 0 ≤ L / Real.sqrt (Fintype.card ι : ℝ) by positivity) hcap
  have htrace := DyadicObservedCapResponse.model_response_trace_le m hm
    (balancedKraus B₀ Z₀) hf.1 hθ hS₀ hZ₀ (Nat.cast_pos.mpr hk) hL
    hbud.1 hbud.2.1 hbud.2.2 hgram hf.2
  have he : ((2 ^ m : ℕ) : ℝ) / (2 * θ) = coefficient m θ := by
    simp only [coefficient, Nat.cast_pow, Nat.cast_ofNat]
  rw [he] at htrace
  exact (observed_response_le_model H B (covarianceKraus_isHermitian A hA C)
    m hm θ hθ S hS J hJ).trans htrace

end MatrixSpencer.RectangularRidgeResponse
