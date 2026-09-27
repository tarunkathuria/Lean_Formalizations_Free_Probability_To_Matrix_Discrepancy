import MatrixSpencer.RectangularRidgeActualResponse

/-! The actual response estimate with a live source budget independent of the
original coefficient universe. The cap, source trace, and inverse Hessian all
refer to the same mixed optimizer; the original dyadic tuning stays fixed. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeLiveResponse
open RectangularRidgeOwnerFrame
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance ridgeLiveResponseCStar {j : Type*} [Fintype j] [DecidableEq j] : CStarAlgebra (Matrix j j ℂ) := {}
local instance ridgeLiveResponseSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeLiveResponseTangentGroup : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance ridgeLiveResponseTangentSpace : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
set_option maxHeartbeats 300000
attribute [local irreducible] RectangularRidgePotential.optimizer

/-- All three balanced budgets use only the actual source trace. Their scalar
bound need not equal the number of original coefficient labels. -/
theorem three_budgets_of_source_trace (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {S : Matrix n n ℂ} (hS : S.PosDef)
    (htr : realTrace S ≤ 1) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hsource : realTrace (covarianceSource A C S) ≤ ℓ) :
    realTrace (balancedDensity (sourceDensity A C S) (sourceTransport A C S)) ≤ Real.sqrt ℓ ∧
    realTrace (balancedRoot (sourceDensity A C S) (sourceTransport A C S) *
      balancedRoot (sourceDensity A C S) (sourceTransport A C S)) ≤ ℓ ∧
    realTrace ((sourceTransport A C S)⁻¹ * balancedDensity (sourceDensity A C S) (sourceTransport A C S)) ≤ ℓ := by
  let B := covarianceKraus A C
  let B₀ := krausReducedFamily B
  let S₀ := sourceDensity A C S
  let M := krausChannel B₀ S₀
  let Z := sourceTransport A C S
  have hB : ∀i,(B i).IsHermitian := covarianceKraus_isHermitian A hA C
  have hS₀ : S₀.PosDef := sourceDensity_posDef A C hS
  have hM : M.PosDef := sourceSource_posDef A hA C hS
  have hZ : Z.PosDef := sourceTransport_posDef A hA C hS
  have ht := transportOptimizer_solve hS₀ hM
  have htr₀ : realTrace S₀ ≤ 1 := sourceDensity_trace_le_one A C hS.posSemidef htr
  have hMtrace : realTrace M ≤ ℓ := by
    have hc := realTrace_isometry_compression_le (covarianceSource_posSemidef A hA hC hS.posSemidef)
      (krausSupportEmbedding B) (krausSupportEmbedding_isometry B)
    have he : M = (krausSupportEmbedding B)ᴴ * covarianceSource A C S * krausSupportEmbedding B := by
      dsimp only [M,B₀,S₀,sourceDensity]
      rw [krausReducedFamily_channel _ hB,krausCompressedSource_eq_compression,←covarianceSource_eq_kraus A hA hC]
    rw [he]
    exact hc.trans hsource
  refine ⟨?_,?_,?_⟩
  · change realTrace (balancedDensity S₀ (transportOptimizer S₀ M)) ≤ Real.sqrt ℓ
    rw [realTrace_balancedDensity_actual B₀ hS₀ hM]
    have hs := fidelity_sq_le_trace_mul hS₀.posSemidef hM.posSemidef
    have hp := mul_le_mul_of_nonneg_right htr₀ (realTrace_nonneg hM.posSemidef)
    have hr := Real.sq_sqrt hℓ
    have hn := fidelity_nonneg S₀ M
    nlinarith [Real.sqrt_nonneg ℓ]
  · exact (realTrace_balancedRoot_square_le hS₀.posSemidef hZ ht).trans hMtrace
  · rw [DyadicBalancedModel.realTrace_inverseTransport_balancedDensity hZ ht]
    exact hMtrace

/-- Pointwise rectangular response with the live trace budget supplied by an
actual supported covariance source, at the actual mixed optimizer. -/
theorem owner_response_le_of_source_trace_and_cap [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C≤1)
    (m : ℕ) (hm : 1≤m) {θ κ L ℓ : ℝ} (hθ : 0<θ) (hκ : 0<κ) (hL : 0<L) (hℓ : 0<ℓ)
    (hsource : realTrace (covarianceSource A C
      (RectangularRidgePotential.optimizer (H : Matrix n n ℂ) (covarianceKraus A C) m θ κ)) ≤ ℓ)
    (hcap : ∀u : EuclideanSpace ℝ ι,
      u∈LinearMap.range (Matrix.toEuclideanCLM (𝕜:=ℝ) C).toLinearMap →
      WithLp.ofLp u ⬝ᵥ (ownedGram A C
        (RectangularRidgePotential.optimizer (H : Matrix n n ℂ) (covarianceKraus A C) m θ κ) *ᵥ WithLp.ofLp u) ≤
      (L/Real.sqrt ℓ)*(WithLp.ofLp u ⬝ᵥ WithLp.ofLp u)) :
    realTrace (C*RectangularRidgeCalculus.ownerCoefficientResponse A hA C m θ κ H) ≤
      2*Real.sqrt ℓ+(6*L^(1/(2:ℝ)^m)/(θ*(1/(2:ℝ)^m)))*ℓ^(1-1/(2:ℝ)^m) := by
  let B := covarianceKraus A C
  let S := RectangularRidgeCalculus.hermitianOptimizer (H : Matrix n n ℂ) B m θ κ
  have hS := RectangularRidgeCalculus.hermitianOptimizer_posDef (H : Matrix n n ℂ) B m hm θ κ hθ hκ
  have htr := (RectangularRidgeCalculus.hermitianOptimizer_trace (H : Matrix n n ℂ) B m θ κ).le
  let B₀ := krausReducedFamily B
  let S₀ := sourceDensity A C S
  let Z := sourceTransport A C S
  have hf := balanced_family_data A hA C hS
  have hb := three_budgets_of_source_trace A hA hC hS htr hℓ.le hsource
  have hg := balancedGram_cap A hA hC hC1 hS
    (by positivity : 0≤L/Real.sqrt ℓ) hcap
  have hmodel := DyadicObservedCapResponse.model_response_trace_le m hm
    (balancedKraus B₀ Z) hf.1 hθ (sourceDensity_posDef A C hS)
    (sourceTransport_posDef A hA C hS) hℓ hL hb.1 hb.2.1 hb.2.2 hg hf.2
  have hc : ((2^m : ℕ) : ℝ)/(2*θ)=DyadicSingularResponseTransfer.coefficient m θ := by
    simp only [DyadicSingularResponseTransfer.coefficient,Nat.cast_pow,Nat.cast_ofNat]
  rw [hc] at hmodel
  rw [RectangularRidgeCalculus.ownerCoefficientResponse_trace_eq A hA hC m θ κ H,
    RectangularRidgeCalculus.krausObservedResponse_eq_inverse H B (covarianceKraus_isHermitian A hA C) m hm θ κ hθ hκ]
  exact (RectangularRidgeResponse.observed_response_le_model (H : Matrix n n ℂ) B
    (covarianceKraus_isHermitian A hA C) m hm θ hθ S hS _
    (RectangularRidgeCalculus.tangentHessianEquiv_ge_dyadic (H : Matrix n n ℂ) B m hm θ κ hθ hκ S hS)).trans hmodel

end MatrixSpencer.RectangularRidgeLiveResponse
