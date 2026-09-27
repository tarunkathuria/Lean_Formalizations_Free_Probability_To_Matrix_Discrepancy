import AugmentedHigherRankKS.FourBlockDensityFirstDerivative
import MatrixSpencer.KSOptimizerFloor

/-! Quantitative density and transport floors from the actual nonlinear KKT system. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS Filter Set
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance quantitativeFloorCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}

/-- The source-density derivative contributes nonnegatively in every PSD direction. -/
theorem nonlinearSourceFidelity_fderiv_lower (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (hX : (X : Matrix (FourSpin n) (FourSpin n) ℂ).PosSemidef) :
    realTrace ((SupportedSpin.transport A ((1:ℝ)/2^k) c S)⁻¹ * SupportedSpin.density A X) ≤
      fderiv ℝ (nonlinearSourceFidelity A ((1:ℝ)/2^k) c) S X := by
  rw [nonlinearSourceFidelity_fderiv A hA k hk c hc S X hS]
  apply le_add_of_nonneg_right
  exact realTrace_mul_nonneg (SupportedSpin.transport_posDef A hA hc hS k hk).posSemidef
    ((densitySource_fderiv_posSemidef A k hk c (fun i => (hc i).le) S X hS hX).conjTranspose_mul_mul_same
      (sourceEmbedding A))

theorem nonlinearSourceFidelity_fderiv_nonneg (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (hX : (X : Matrix (FourSpin n) (FourSpin n) ℂ).PosSemidef) :
    0 ≤ fderiv ℝ (nonlinearSourceFidelity A ((1:ℝ)/2^k) c) S X :=
  (realTrace_mul_nonneg (SupportedSpin.transport_posDef A hA hc hS k hk).inv.posSemidef
    (hX.conjTranspose_mul_mul_same (sourceEmbedding A))).trans
    (nonlinearSourceFidelity_fderiv_lower A hA k hk c hc S X hS hX)

theorem nonlinearSourceFidelity_fderiv_radial (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    fderiv ℝ (nonlinearSourceFidelity A ((1:ℝ)/2^k) c) S S =
      nonlinearSourceFidelity A ((1:ℝ)/2^k) c S := by
  rw [nonlinearSourceFidelity_fderiv A hA k hk c hc S S hS,
    densitySource_fderiv_radial A k hk c (fun i => (hc i).le) S hS]
  have hd := SupportedSpin.density_posDef A hS
  have hm := compressedSource_posDef A hA hc hS k hk
  have hz := SupportedSpin.transport_posDef A hA hc hS k hk
  change realTrace ((SupportedSpin.transport A _ c S)⁻¹ * SupportedSpin.density A S) +
    realTrace (SupportedSpin.transport A _ c S * compressedSource A _ c S) = _
  rw [realTrace_mul_comm ((SupportedSpin.transport A _ c S)⁻¹),
    realTrace_mul_comm (SupportedSpin.transport A _ c S)]
  change transportCost (SupportedSpin.density A S) (compressedSource A _ c S)
    (SupportedSpin.transport A _ c S) = _
  rw [transportCost_at_transport hz (SupportedSpin.transport_equation A hA hc hS k hk)]
  change 2 * realTrace (compressedSource A _ c S * transportOptimizer (SupportedSpin.density A S) (compressedSource A _ c S)) = _
  rw [trace_transportOptimizer_eq_fidelity hd hm]
  unfold nonlinearSourceFidelity
  rw [fidelity_source_compression A hA hc hS k hk]
  rfl

/-- Stationarity controls both positive density-gradient contributions together. -/
theorem positive_gradient_pairing_le (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) {θ : ℝ} (hθ : 0 < θ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, objective H A ((1:ℝ)/2^k) c θ T ≤ objective H A ((1:ℝ)/2^k) c θ S)
    (T : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hT : (T : Matrix (FourSpin n) (FourSpin n) ℂ) ∈ densitySet) :
    fderiv ℝ (nonlinearSourceFidelity A ((1:ℝ)/2^k) c) S T +
      θ * realTrace (inverseSqrt S * (T : Matrix (FourSpin n) (FourSpin n) ℂ)) ≤
        objective H A ((1:ℝ)/2^k) c θ S + ‖H‖ := by
  let D : densityTangent (n := FourSpin n) := ⟨T-S, by
    change realTrace ((T : Matrix (FourSpin n) (FourSpin n) ℂ)-(S : Matrix (FourSpin n) (FourSpin n) ℂ)) = 0
    rw [realTrace_sub,hT.2,ht,sub_self]⟩
  have hstat := OptimizerResponse.faithful_maximizer_stationary
    (hermitianObjective H A ((1:ℝ)/2^k) c θ) S hS ht
    ((contDiffAt_hermitianObjective H A hA k hk c hc θ S hS).differentiableAt (by simp))
    (fun U hU => hmax U hU)
  have hz := congrArg (fun L : densityTangent (n := FourSpin n) →L[ℝ] ℝ => L D) hstat
  change fderiv ℝ (hermitianObjective H A ((1:ℝ)/2^k) c θ) S (T-S) = 0 at hz
  rw [map_sub, fderiv_hermitianObjective H A hA k hk c hc θ S hS] at hz
  simp only [ContinuousLinearMap.add_apply, fderiv_tsallisPotential_eq θ S hS] at hz
  change realTrace (H * (T : Matrix (FourSpin n) (FourSpin n) ℂ)) +
      fderiv ℝ (nonlinearSourceFidelity A ((1:ℝ)/2^k) c) S T +
      θ * realTrace (inverseSqrt S * (T : Matrix (FourSpin n) (FourSpin n) ℂ)) -
      (realTrace (H * (S : Matrix (FourSpin n) (FourSpin n) ℂ)) +
        fderiv ℝ (nonlinearSourceFidelity A ((1:ℝ)/2^k) c) S S +
        θ * realTrace (inverseSqrt S * (S : Matrix (FourSpin n) (FourSpin n) ℂ))) = 0 at hz
  rw [nonlinearSourceFidelity_fderiv_radial A hA k hk c hc S hS,
    KSOptimizerFloor.inverseSqrt_mul_self S hS] at hz
  have hHlo := (abs_le.mp (abs_realTrace_mul_density_le_norm hH hT)).1
  have hr := mul_nonneg hθ.le (realTrace_nonneg (CFC.sqrt_nonneg (S : Matrix (FourSpin n) (FourSpin n) ℂ)).posSemidef)
  unfold objective nonlinearSourceFidelity at *
  linarith

/-- An explicit density floor from a cap on the actual optimized objective. -/
theorem maximizer_density_floor (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) {θ B : ℝ} (hθ : 0 < θ) (hB : 0 < B)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, objective H A ((1:ℝ)/2^k) c θ T ≤ objective H A ((1:ℝ)/2^k) c θ S)
    (hcap : objective H A ((1:ℝ)/2^k) c θ S + ‖H‖ ≤ B) :
    (θ/B)^2 • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ (S : Matrix (FourSpin n) (FourSpin n) ℂ) := by
  have hinv : inverseSqrt S ≤ (B/θ) • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) := by
    apply KSOptimizerFloor.le_scalar_of_density_pairings hS.posDef_sqrt.inv.isHermitian
    intro T hT
    let T' : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) := ⟨T,hT.1.isHermitian⟩
    have hp := (positive_gradient_pairing_le H hH A hA k hk c hc hθ S hS ht hmax T' hT).trans hcap
    have hn := nonlinearSourceFidelity_fderiv_nonneg A hA k hk c hc S T' hS hT.1
    apply (le_div_iff₀ hθ).mpr
    change realTrace (inverseSqrt S * T) * θ ≤ B
    linarith
  simpa only [inv_div] using KSOptimizerFloor.floor_of_inverseSqrt_le S hS (div_pos hB hθ) hinv

/-- The same KKT equation bounds the inverse supported transport. -/
theorem maximizer_transport_inverse_le (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) {θ B : ℝ} (hθ : 0 < θ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, objective H A ((1:ℝ)/2^k) c θ T ≤ objective H A ((1:ℝ)/2^k) c θ S)
    (hcap : objective H A ((1:ℝ)/2^k) c θ S + ‖H‖ ≤ B) :
    (SupportedSpin.transport A ((1:ℝ)/2^k) c S)⁻¹ ≤
      B • (1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) := by
  let E := sourceEmbedding A
  let Z := SupportedSpin.transport A ((1:ℝ)/2^k) c S
  have hz : Z.PosDef := SupportedSpin.transport_posDef A hA hc hS k hk
  have hb : E * Z⁻¹ * Eᴴ ≤ B • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) := by
    apply KSOptimizerFloor.le_scalar_of_density_pairings (hz.inv.posSemidef.mul_mul_conjTranspose_same E).isHermitian
    intro T hT
    let T' : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) := ⟨T,hT.1.isHermitian⟩
    have hp := (positive_gradient_pairing_le H hH A hA k hk c hc hθ S hS ht hmax T' hT).trans hcap
    have hlo := nonlinearSourceFidelity_fderiv_lower A hA k hk c hc S T' hS hT.1
    have hr := mul_nonneg hθ.le (realTrace_mul_nonneg hS.posDef_sqrt.inv.posSemidef hT.1)
    change 0 ≤ θ * realTrace (inverseSqrt S * T) at hr
    change realTrace (Z⁻¹ * SupportedSpin.density A T) ≤ _ at hlo
    change fderiv ℝ (nonlinearSourceFidelity A ((1:ℝ)/2^k) c) S T' + θ * realTrace (inverseSqrt S * T) ≤ B at hp
    rw [KSSafeRetirement.realTrace_embedded_mul]
    change realTrace (Z⁻¹ * SupportedSpin.density A T) ≤ B
    linarith
  have hh := (Matrix.le_iff.mp hb).conjTranspose_mul_mul_same E
  apply Matrix.le_iff.mpr
  convert hh using 1
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, ← Matrix.mul_assoc]
  have he : Eᴴ*E=1 := SupportedSpin.embedding_isometry A
  simp only [he, Matrix.one_mul]
  simp only [Matrix.mul_assoc, he, Matrix.mul_one]
  rfl

/-- The supported transport is uniformly positive without a source spectral gap. -/
theorem maximizer_transport_floor (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) {θ B : ℝ} (hθ : 0 < θ) (hB : 0 < B)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, objective H A ((1:ℝ)/2^k) c θ T ≤ objective H A ((1:ℝ)/2^k) c θ S)
    (hcap : objective H A ((1:ℝ)/2^k) c θ S + ‖H‖ ≤ B) :
    B⁻¹ • (1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) ≤
      SupportedSpin.transport A ((1:ℝ)/2^k) c S := by
  have hz := SupportedSpin.transport_posDef A hA hc hS k hk
  have hi := KSOptimizerFloor.inverse_order hz.inv (Matrix.PosDef.one.smul hB)
    (maximizer_transport_inverse_le H hH A hA k hk c hc hθ S hS ht hmax hcap)
  rwa [KSOptimizerFloor.scalar_inverse hB.ne', Matrix.nonsing_inv_nonsing_inv _
    ((SupportedSpin.transport A ((1:ℝ)/2^k) c S).isUnit_iff_isUnit_det.mp hz.isUnit)] at hi

end AugmentedHigherRankKS
