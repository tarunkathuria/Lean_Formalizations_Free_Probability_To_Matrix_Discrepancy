import MatrixSpencer.SingularResponseTransfer
import MatrixSpencer.ObservedResponse

/-!
# Singular-source response in the actual reduced balanced frame

The full reduced density inverse is an actual Hessian inverse. Its normal
equation identifies its variational energy, and the exact balanced Hessian
representation places the singular-source transfer in the observed frame.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
set_option maxHeartbeats 600000
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

local instance singularBalancedCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance singularBalancedNormedSpace {j : Type*} [Fintype j] [DecidableEq j] :
    NormedSpace ℝ (selfAdjoint (Matrix j j ℂ)) := inferInstance
local instance singularBalancedFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

/-- The actual unconstrained inverse solves the normal equation against every test. -/
theorem fullDensityInverse_normal (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (X W : selfAdjoint (Matrix n n ℂ)) :
    densityNegativeHessian H B θ S
      ((fullDensityHessianEquiv H B θ hθ S hS).symm (tracePairing (X : Matrix n n ℂ))) W =
        tracePairing (X : Matrix n n ℂ) W := by
  change fullDensityHessianEquiv H B θ hθ S hS
    ((fullDensityHessianEquiv H B θ hθ S hS).symm (tracePairing (X : Matrix n n ℂ))) W = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- Exact full-inverse energy in the frozen balanced coordinates. -/
theorem fullDensityInverse_balanced_energy (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM)
    let U := (fullDensityHessianEquiv H B θ hθ S hS).symm (tracePairing (X : Matrix n n ℂ))
    let y := matrixVector (G.symm U)
    RCLike.re (star y ⬝ᵥ (balancedFullSuper B θ S Z *ᵥ y)) =
      realTrace ((X : Matrix n n ℂ) * (U : Matrix n n ℂ)) := by
  dsimp only
  rw [← balancedFullSuper_actual_hessian H B hB θ hθ S _ _ hS hM]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  exact fullDensityInverse_normal H B θ hθ S hS X _

/-- The full density inverse attains its response as a balanced variational trial. -/
theorem fullDensityInverse_balanced_trial (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM)
    let U := (fullDensityHessianEquiv H B θ hθ S hS).symm (tracePairing (X : Matrix n n ℂ))
    let y := matrixVector (G.symm U)
    2 * RCLike.re (star (matrixVector (G X)) ⬝ᵥ y) -
      RCLike.re (star y ⬝ᵥ (balancedFullSuper B θ S Z *ᵥ y)) =
      tracePairing (X : Matrix n n ℂ) U := by
  dsimp only
  rw [balanced_force_pairing, fullDensityInverse_balanced_energy H B hB θ hθ S X hS hM]
  rw [tracePairing_apply]
  ring

/-- The actual unconstrained density inverse is bounded by the balanced complex inverse. -/
theorem fullDensityInverse_le_balanced_inverse (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM)
    tracePairing (X : Matrix n n ℂ)
      ((fullDensityHessianEquiv H B θ hθ S hS).symm (tracePairing (X : Matrix n n ℂ))) ≤
      ComplexInverseComparison.quadratic (balancedFullSuper B θ S Z)⁻¹ (matrixVector (G X)) := by
  dsimp only
  rw [← fullDensityInverse_balanced_trial H B hB θ hθ S X hS hM]
  exact ComplexInverseComparison.inverse_variational_le
    (balancedFullSuper_posDef B hB hθ hS (transportOptimizer_posDef hS hM)) _ _

/-- Exact normalization of the full density inverse response in the observed coordinates. -/
theorem fullDensityInverse_le_whitened_inverse (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
    let G := balancedCoordinateEquiv Z (transportOptimizer_posDef hS hM)
    tracePairing (X : Matrix n n ℂ)
      ((fullDensityHessianEquiv H B θ hθ S hS).symm (tracePairing (X : Matrix n n ℂ))) ≤
      ComplexInverseComparison.quadratic (balancedWhitenedFull B θ S Z)⁻¹
        (CFC.sqrt (jordanSuper (balancedDensity S Z)) *ᵥ matrixVector (G X)) := by
  dsimp only
  rw [← balanced_inverse_response_eq_whitened B hB θ hS (transportOptimizer_posDef hS hM)]
  exact fullDensityInverse_le_balanced_inverse H B hB θ hθ S X hS hM


/-- The actual potential response in a supported force is bounded by the faithful
reduced whitened inverse, with no normalization of the compressed density. -/
theorem potential_hessian_supported_le_reduced_whitened [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (θ : ℝ) (hθ : 0 < θ)
    (F : selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ)) :
    let S := hermitianDensityOptimizer (H : Matrix n n ℂ) B θ
    let S₀ := krausReducedDensityCLM B S
    let B₀ := krausReducedFamily B
    let Z₀ := transportOptimizer (S₀ : Matrix _ _ ℂ) (krausChannel B₀ (S₀ : Matrix _ _ ℂ))
    let X := hermitianRectangularEmbeddingCLM (krausSupportEmbedding B) F
    fderiv ℝ (fun K => fderiv ℝ (hermitianDensityPotential B θ) K) H X X ≤
      ComplexInverseComparison.quadratic (balancedWhitenedFull B₀ θ S₀ Z₀)⁻¹
        (CFC.sqrt (jordanSuper (balancedDensity S₀ Z₀)) *ᵥ matrixVector (CFC.sqrt Z₀ * (F : Matrix _ _ ℂ) * CFC.sqrt Z₀)) := by
  dsimp only
  have h₁ := potential_hessian_supported_le_reduced_inverse (n := n) H B hB 0 θ hθ F
  have h₂ := fullDensityInverse_le_whitened_inverse
    (n := Fin (Module.finrank ℂ (krausSupport B))) 0
    (krausReducedFamily B) (krausReducedFamily_isHermitian B hB)
    θ hθ (krausReducedDensityCLM B (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)) F
    (krausCompressedDensity_posDef B (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ))
    (krausReducedFamily_source_posDef B hB
      (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ))
  dsimp only at h₁ h₂
  exact h₁.trans h₂


/-- Every original Hermitian Kraus force is the extension of its actual reduced force. -/
theorem hermitianMatrixFamily_eq_reduced_embedding (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (a : ι) :
    hermitianRectangularEmbeddingCLM (krausSupportEmbedding B)
      (hermitianMatrixFamily (krausReducedFamily B) (krausReducedFamily_isHermitian B hB) a) =
        hermitianMatrixFamily B hB a := by
  apply Subtype.ext
  simp only [hermitianRectangularEmbeddingCLM_coe, hermitianMatrixFamily,
    krausReducedFamily_reconstruct B hB]

/-- The actual observed potential response is bounded by the actual reduced force
frame, at arbitrary source rank and with the original Kraus label set unchanged. -/
theorem singular_observed_response_le [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (θ : ℝ) (hθ : 0 < θ) :
    let S := hermitianDensityOptimizer (H : Matrix n n ℂ) B θ
    let S₀ := krausReducedDensityCLM B S
    let B₀ := krausReducedFamily B
    let Z₀ := transportOptimizer (S₀ : Matrix _ _ ℂ) (krausChannel B₀ (S₀ : Matrix _ _ ℂ))
    krausObservedResponse H B hB θ ≤
      realTrace (jordanForceFrame (balancedDensity S₀ Z₀) (balancedKraus B₀ Z₀) *
        (balancedWhitenedFull B₀ θ S₀ Z₀)⁻¹) := by
  classical
  dsimp only
  rw [krausObservedResponse, jordanForceFrame_trace_eq_half_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  apply Finset.sum_le_sum
  intro a _
  have h := potential_hessian_supported_le_reduced_whitened H B hB θ hθ
    (hermitianMatrixFamily (krausReducedFamily B) (krausReducedFamily_isHermitian B hB) a)
  dsimp only at h
  rw [hermitianMatrixFamily_eq_reduced_embedding B hB a] at h
  exact h

end MatrixSpencer
