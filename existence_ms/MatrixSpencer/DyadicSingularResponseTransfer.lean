import MatrixSpencer.DyadicDensityCalculus
import MatrixSpencer.DyadicCurvatureCompression
import MatrixSpencer.SingularResponseTransfer

/-!
# Actual dyadic density response under physical support compression

The comparison curvature on the reduced space is the inverse of the explicit
inverse model plus the actual reduced free fidelity curvature. It is not
identified with the reduced actual Tsallis Hessian. Full density directions
are retained until the variational comparison; trace constraints only reduce
the final response. Physical support dimension zero is allowed.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

namespace MatrixSpencer
namespace DyadicSingularResponseTransfer
noncomputable section

variable {n k : Type*} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]

local instance dyadicTransferCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance dyadicTransferSpace {j : Type*} [Fintype j] [DecidableEq j] :
    NormedSpace ℝ (selfAdjoint (Matrix j j ℂ)) := inferInstance
local instance dyadicTransferFiniteDimensional {j : Type*} [Fintype j] [DecidableEq j] :
    FiniteDimensional ℝ (selfAdjoint (Matrix j j ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix j j ℂ)))

def coefficient (m : ℕ) (θ : ℝ) : ℝ := (2 ^ m : ℝ) / (2 * θ)

theorem coefficient_pos (m : ℕ) {θ : ℝ} (hθ : 0 < θ) : 0 < coefficient m θ := by
  unfold coefficient
  positivity

/-- This bilinear form is the actual negative second derivative. -/
def regularizerBilinear (m : ℕ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) :=
  -fderiv ℝ (fun X => fderiv ℝ (dyadicTsallisPotential m θ) X) S

theorem regularizerBilinear_apply (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : θ ≠ 0)
    (S X Y : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    regularizerBilinear m θ S X Y =
      realTrace ((negativeDyadicTsallisHessianEquiv m θ hθ S hS X : Matrix n n ℂ) *
        (Y : Matrix n n ℂ)) := by
  change -fderiv ℝ (fun X => fderiv ℝ (dyadicTsallisPotential m θ) X) S X Y = _
  rw [fderiv_fderiv_dyadicTsallisPotential_apply m hm θ hθ S X Y hS, neg_neg]

theorem regularizerBilinear_symmetric (m : ℕ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (X Y : selfAdjoint (Matrix n n ℂ)) :
    regularizerBilinear m θ S X Y = regularizerBilinear m θ S Y X := by
  have h := (contDiffAt_dyadicTsallisPotential m θ S hS).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  exact congrArg Neg.neg (h X Y)

theorem regularizerBilinear_nonneg (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (X : selfAdjoint (Matrix n n ℂ)) : 0 ≤ regularizerBilinear m θ S X X := by
  by_cases hX : X = 0
  · subst X; simp
  · change 0 ≤ -fderiv ℝ (fun X => fderiv ℝ (dyadicTsallisPotential m θ) X) S X X
    exact le_of_lt (neg_pos.mpr (fderiv_fderiv_dyadicTsallisPotential_quadratic_neg m hm θ hθ S X hS hX))

/-- A trial force gives a lower bound on the actual regularizer curvature. -/
theorem regularizer_trial_le (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (F Y : selfAdjoint (Matrix n n ℂ)) :
    2 * realTrace ((F : Matrix n n ℂ) * (Y : Matrix n n ℂ)) -
      realTrace ((F : Matrix n n ℂ) *
        ((negativeDyadicTsallisHessianEquiv m θ hθ.ne' S hS).symm F : Matrix n n ℂ)) ≤
      regularizerBilinear m θ S Y Y := by
  have ht := bilinear_trial_le (regularizerBilinear m θ S)
    (regularizerBilinear_symmetric m θ S hS) (regularizerBilinear_nonneg m hm θ hθ S hS)
    (tracePairing (F : Matrix n n ℂ))
    ((negativeDyadicTsallisHessianEquiv m θ hθ.ne' S hS).symm F) (by
      apply ContinuousLinearMap.ext
      intro Z
      simp only [regularizerBilinear_apply m hm θ hθ.ne' S _ Z hS,
        ContinuousLinearEquiv.apply_symm_apply, tracePairing_apply]) Y
  simp only [tracePairing_apply] at ht
  linarith

/-- The full actual inverse is bounded after embedding the entire supported force. -/
theorem actual_inverse_supported_force_le_model (m : ℕ) (_hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) (F : selfAdjoint (Matrix k k ℂ)) :
    realTrace ((hermitianRectangularEmbeddingCLM V F : Matrix n n ℂ) *
      ((negativeDyadicTsallisHessianEquiv m θ hθ.ne' S hS).symm
        (hermitianRectangularEmbeddingCLM V F) : Matrix n n ℂ)) ≤
      realTrace ((F : Matrix k k ℂ) * DyadicCurvatureCompression.inverseModel m
        (coefficient m θ) (Vᴴ * (S : Matrix n n ℂ) * V) F) := by
  have h := inverse_negativeDyadicTsallisHessian_le_model m θ hθ S
    (hermitianRectangularEmbeddingCLM V F) hS
  have hc := DyadicCurvatureCompression.inverseModel_supported_force_quadratic_le m
    (coefficient_pos m hθ).le hS.posSemidef V hV F.property
  simp only [hermitianRectangularEmbeddingCLM_coe] at h
  simpa only [hermitianRectangularEmbeddingCLM_coe] using h.trans hc

/-- The reduced model curvature is the inverse of its explicit positive inverse model. -/
def modelCurvatureBilinear (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S : Matrix n n ℂ) (hS : S.PosDef) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) :=
  (tracePairing.comp hermitianInclusion).comp
    ((DyadicCurvatureCompression.inverseModelEquiv m c hc S hS).symm :
      selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ))

@[simp] theorem modelCurvatureBilinear_apply (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S : Matrix n n ℂ) (hS : S.PosDef) (X Y : selfAdjoint (Matrix n n ℂ)) :
    modelCurvatureBilinear m c hc S hS X Y =
      realTrace (((DyadicCurvatureCompression.inverseModelEquiv m c hc S hS).symm X : Matrix n n ℂ) *
        (Y : Matrix n n ℂ)) := rfl

theorem modelCurvatureBilinear_symmetric (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S : Matrix n n ℂ) (hS : S.PosDef) (X Y : selfAdjoint (Matrix n n ℂ)) :
    modelCurvatureBilinear m c hc S hS X Y = modelCurvatureBilinear m c hc S hS Y X := by
  let U := DyadicCurvatureCompression.inverseModelEquiv m c hc S hS
  have h := DyadicCurvatureCompression.inverseModel_trace_symmetric m c S
    (U.symm X) (U.symm Y)
  rw [DyadicCurvatureCompression.inverseModelEquiv_symm_solve,
    DyadicCurvatureCompression.inverseModelEquiv_symm_solve] at h
  exact h.trans (realTrace_mul_comm _ _)

theorem modelCurvatureBilinear_pos (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S : Matrix n n ℂ) (hS : S.PosDef) (X : selfAdjoint (Matrix n n ℂ)) (hX : X ≠ 0) :
    0 < modelCurvatureBilinear m c hc S hS X X := by
  let U := DyadicCurvatureCompression.inverseModelEquiv m c hc S hS
  have hY : U.symm X ≠ 0 := by
    intro hy
    apply hX
    exact U.symm.injective (hy.trans (map_zero _).symm)
  have hY' : (U.symm X : Matrix n n ℂ) ≠ 0 := fun h => hY (Subtype.ext h)
  have h := DyadicCurvatureCompression.inverseModel_quadratic_pos m hc hS (U.symm X).property hY'
  rw [DyadicCurvatureCompression.inverseModelEquiv_symm_solve] at h
  exact h

theorem modelCurvatureBilinear_nonneg (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S : Matrix n n ℂ) (hS : S.PosDef) (X : selfAdjoint (Matrix n n ℂ)) :
    0 ≤ modelCurvatureBilinear m c hc S hS X X := by
  by_cases hX : X = 0
  · subst X; simp
  · exact (modelCurvatureBilinear_pos m c hc S hS X hX).le

/-- Full actual curvature dominates the compressed model curvature, retaining every full direction. -/
theorem regularizer_curvature_compression_le (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) (Y : selfAdjoint (Matrix n n ℂ)) :
    modelCurvatureBilinear m (coefficient m θ) (coefficient_pos m hθ)
      (hermitianRectangularCompressionCLM V S) (hermitianCompression_posDef V hV S hS)
      (hermitianRectangularCompressionCLM V Y) (hermitianRectangularCompressionCLM V Y) ≤
      regularizerBilinear m θ S Y Y := by
  let S₀ := hermitianRectangularCompressionCLM V S
  let hS₀ := hermitianCompression_posDef V hV S hS
  let Y₀ := hermitianRectangularCompressionCLM V Y
  let U₀ : selfAdjoint (Matrix k k ℂ) ≃L[ℝ] selfAdjoint (Matrix k k ℂ) :=
    DyadicCurvatureCompression.inverseModelEquiv m (coefficient m θ)
      (coefficient_pos m hθ) (S₀ : Matrix k k ℂ) hS₀
  let F := U₀.symm Y₀
  have hi := actual_inverse_supported_force_le_model m hm θ hθ S hS V hV F
  have ht := regularizer_trial_le m hm θ hθ S hS (hermitianRectangularEmbeddingCLM V F) Y
  have hs : DyadicCurvatureCompression.inverseModel m (coefficient m θ) (S₀ : Matrix k k ℂ) F =
      (Y₀ : Matrix k k ℂ) :=
    DyadicCurvatureCompression.inverseModelEquiv_symm_solve m (coefficient m θ)
      (coefficient_pos m hθ) (S₀ : Matrix k k ℂ) hS₀ Y₀
  change _ ≤ realTrace ((F : Matrix k k ℂ) *
    DyadicCurvatureCompression.inverseModel m (coefficient m θ) (S₀ : Matrix k k ℂ) F) at hi
  rw [hs] at hi
  rw [← hermitianRectangularCompression_trace_adjoint V F Y] at ht
  change realTrace ((F : Matrix k k ℂ) * (Y₀ : Matrix k k ℂ)) ≤ _
  change 2 * realTrace ((F : Matrix k k ℂ) * (Y₀ : Matrix k k ℂ)) - _ ≤ _ at ht
  linarith

variable {ι : Type*} [Fintype ι]

/-- The artificial regularizer curvature plus the actual free fidelity curvature. -/
def modelDensityBilinear (B : ι → Matrix n n ℂ) (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) :=
  -fderiv ℝ (fun X => fderiv ℝ (krausSourceFidelity B) X) S +
    modelCurvatureBilinear m c hc (S : Matrix n n ℂ) hS

@[simp] theorem modelDensityBilinear_apply (B : ι → Matrix n n ℂ)
    (m : ℕ) (c : ℝ) (hc : 0 < c) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (X Y : selfAdjoint (Matrix n n ℂ)) :
    modelDensityBilinear B m c hc S hS X Y =
      -fderiv ℝ (fun X => fderiv ℝ (krausSourceFidelity B) X) S X Y +
        modelCurvatureBilinear m c hc (S : Matrix n n ℂ) hS X Y := rfl

theorem modelDensityBilinear_symmetric (B : ι → Matrix n n ℂ)
    (m : ℕ) (c : ℝ) (hc : 0 < c) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (X Y : selfAdjoint (Matrix n n ℂ)) :
    modelDensityBilinear B m c hc S hS X Y = modelDensityBilinear B m c hc S hS Y X := by
  have h := (contDiffAt_krausSourceFidelity_source_unrestricted B S hS).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [modelDensityBilinear_apply, h X Y,
    modelCurvatureBilinear_symmetric m c hc (S : Matrix n n ℂ) hS X Y]

theorem modelDensityBilinear_pos (B : ι → Matrix n n ℂ)
    (m : ℕ) (c : ℝ) (hc : 0 < c) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (X : selfAdjoint (Matrix n n ℂ)) (hX : X ≠ 0) :
    0 < modelDensityBilinear B m c hc S hS X X := by
  have hf := fderiv_fderiv_krausSourceFidelity_quadratic_nonpos_source_unrestricted B S X hS
  have hm := modelCurvatureBilinear_pos m c hc (S : Matrix n n ℂ) hS X hX
  rw [modelDensityBilinear_apply]
  linarith

theorem modelDensityBilinear_nonneg (B : ι → Matrix n n ℂ)
    (m : ℕ) (c : ℝ) (hc : 0 < c) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (X : selfAdjoint (Matrix n n ℂ)) :
    0 ≤ modelDensityBilinear B m c hc S hS X X := by
  by_cases hX : X = 0
  · subst X; simp
  · exact (modelDensityBilinear_pos B m c hc S hS X hX).le

def modelDensityEquiv (B : ι → Matrix n n ℂ) (m : ℕ) (c : ℝ) (hc : 0 < c)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    selfAdjoint (Matrix n n ℂ) ≃L[ℝ] (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) :=
  positiveBilinearEquiv (modelDensityBilinear B m c hc S hS)
    (modelDensityBilinear_pos B m c hc S hS)

@[simp] theorem modelDensityEquiv_apply (B : ι → Matrix n n ℂ)
    (m : ℕ) (c : ℝ) (hc : 0 < c) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (X : selfAdjoint (Matrix n n ℂ)) :
    modelDensityEquiv B m c hc S hS X = modelDensityBilinear B m c hc S hS X := rfl

/-- Actual free curvature pulls back exactly; the full actual regularizer dominates the model. -/
theorem modelDensityBilinear_reducedFamily_le (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    modelDensityBilinear (krausReducedFamily B) m (coefficient m θ) (coefficient_pos m hθ)
      (krausReducedDensityCLM B S) (krausCompressedDensity_posDef B hS)
      (krausReducedDensityCLM B X) (krausReducedDensityCLM B X) ≤
      dyadicDensityNegativeHessian H B m θ S X X := by
  have ht := regularizer_curvature_compression_le m hm θ hθ S hS
    (krausSupportEmbedding B) (krausSupportEmbedding_isometry B) X
  change modelCurvatureBilinear m (coefficient m θ) (coefficient_pos m hθ)
    (krausReducedDensityCLM B S : Matrix _ _ ℂ) (krausCompressedDensity_posDef B hS)
    (krausReducedDensityCLM B X) (krausReducedDensityCLM B X) ≤
      -fderiv ℝ (fun T => fderiv ℝ (dyadicTsallisPotential m θ) T) S X X at ht
  rw [modelDensityBilinear_apply]
  change _ ≤ -fderiv ℝ (fun T => fderiv ℝ (hermitianDyadicDensityObjective H B m θ) T) S X X
  rw [fderiv_fderiv_hermitianDyadicDensityObjective_apply H B m hm θ S X X hS,
    krausSourceFidelity_hessian_reducedFamily B hB S X X hS]
  linarith

/-- The full inverse of the reduced comparison form; no trace normalization is imposed on its density. -/
def reducedModelDensityEquiv (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ) ≃L[ℝ]
    (selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ) →L[ℝ] ℝ) :=
  modelDensityEquiv (krausReducedFamily B) m (coefficient m θ) (coefficient_pos m hθ)
    (krausReducedDensityCLM B S) (krausCompressedDensity_posDef B hS)

/-- Compression controls the inverse response on the full density space. -/
theorem full_inverse_response_le_model (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (f : selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ) →L[ℝ] ℝ) :
    (f.comp (krausReducedDensityCLM B))
      ((dyadicDensityHessianEquiv H B m hm θ hθ S hS).symm (f.comp (krausReducedDensityCLM B))) ≤
      f ((reducedModelDensityEquiv B m θ hθ S hS).symm f) := by
  refine bilinear_inverse_pullback_le (dyadicDensityHessianEquiv H B m hm θ hθ S hS)
    (reducedModelDensityEquiv B m θ hθ S hS) (krausReducedDensityCLM B) ?_ ?_ ?_ f
  · exact modelDensityBilinear_symmetric (krausReducedFamily B) m (coefficient m θ)
      (coefficient_pos m hθ) (krausReducedDensityCLM B S) (krausCompressedDensity_posDef B hS)
  · exact modelDensityBilinear_nonneg (krausReducedFamily B) m (coefficient m θ)
      (coefficient_pos m hθ) (krausReducedDensityCLM B S) (krausCompressedDensity_posDef B hS)
  · intro X
    exact modelDensityBilinear_reducedFamily_le H B hB m hm θ hθ S X hS

local instance dyadicTransferTangentNormedGroup : NormedAddCommGroup (densityTangent (n := n)) :=
  inferInstance
local instance dyadicTransferTangentSpace : NormedSpace ℝ (densityTangent (n := n)) := inferInstance

/-- The trace constraint can only lower the response to a supported force. -/
theorem constrained_inverse_response_le_model (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (f : selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ) →L[ℝ] ℝ) :
    let P := (krausReducedDensityCLM B).comp (densityTangent (n := n)).subtypeL
    (f.comp P) ((dyadicDensityTangentHessianEquiv H B m hm θ hθ S hS).symm (f.comp P)) ≤
      f ((reducedModelDensityEquiv B m θ hθ S hS).symm f) := by
  dsimp only
  refine bilinear_inverse_pullback_le (E := densityTangent (n := n))
    (F := selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ))
    (dyadicDensityTangentHessianEquiv H B m hm θ hθ S hS)
    (reducedModelDensityEquiv B m θ hθ S hS)
    ((krausReducedDensityCLM B).comp (densityTangent (n := n)).subtypeL) ?_ ?_ ?_ f
  · exact modelDensityBilinear_symmetric (krausReducedFamily B) m (coefficient m θ)
      (coefficient_pos m hθ) (krausReducedDensityCLM B S) (krausCompressedDensity_posDef B hS)
  · exact modelDensityBilinear_nonneg (krausReducedFamily B) m (coefficient m θ)
      (coefficient_pos m hθ) (krausReducedDensityCLM B S) (krausCompressedDensity_posDef B hS)
  · intro X
    exact modelDensityBilinear_reducedFamily_le H B hB m hm θ hθ S X hS

/-- A concrete reduced Hermitian matrix gives exactly the ambient supported trace force. -/
theorem full_supported_force_eq (B : ι → Matrix n n ℂ)
    (F : selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ)) :
    (tracePairing (F : Matrix _ _ ℂ)).comp (krausReducedDensityCLM B) =
      tracePairing (hermitianRectangularEmbeddingCLM (krausSupportEmbedding B) F : Matrix n n ℂ) := by
  ext X
  exact hermitianRectangularCompression_trace_adjoint (krausSupportEmbedding B) F X

end
end DyadicSingularResponseTransfer
end MatrixSpencer
