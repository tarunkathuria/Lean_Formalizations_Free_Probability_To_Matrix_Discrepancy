import MatrixSpencer.KrausCompressionBridge
import MatrixSpencer.SqrtCompression
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import MatrixSpencer.KrausReducedFamily
import MatrixSpencer.SingularDensityCalculus
import MatrixSpencer.OptimizerResponseUnrestricted

/-!
# Actual Tsallis inverse response under physical compression

The full inverse Hessian is applied before compression, so off-block density
directions remain present. Square-root compression then bounds its quadratic
form by the inverse Hessian at the compressed density, with the same parameter.
-/

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MatrixSpencer

noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

local instance singularTransferCStarAlgebra {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance singularTransferNormedSpace {j : Type*} [Fintype j] [DecidableEq j] :
    NormedSpace ℝ (selfAdjoint (Matrix j j ℂ)) := inferInstance

/-- Extension by zero in physical coordinates, as a real Hermitian linear map. -/
def hermitianRectangularEmbeddingCLM (V : Matrix n m ℂ) :
    selfAdjoint (Matrix m m ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  hermitianRectangularCompressionCLM Vᴴ

@[simp] theorem hermitianRectangularEmbeddingCLM_coe (V : Matrix n m ℂ)
    (X : selfAdjoint (Matrix m m ℂ)) :
    (hermitianRectangularEmbeddingCLM V X : Matrix n n ℂ) = V * (X : Matrix m m ℂ) * Vᴴ := by
  simp only [hermitianRectangularEmbeddingCLM, hermitianRectangularCompressionCLM_coe,
    Matrix.conjTranspose_conjTranspose]

theorem hermitianRectangularCompression_embedding (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    (X : selfAdjoint (Matrix m m ℂ)) :
    hermitianRectangularCompressionCLM V (hermitianRectangularEmbeddingCLM V X) = X := by
  apply Subtype.ext
  simp only [hermitianRectangularCompressionCLM_coe, hermitianRectangularEmbeddingCLM_coe]
  calc
    _ = (Vᴴ * V) * (X : Matrix m m ℂ) * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.one_mul, Matrix.mul_one]

theorem hermitianRectangularCompression_surjective (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) :
    Function.Surjective (hermitianRectangularCompressionCLM V) :=
  fun X => ⟨hermitianRectangularEmbeddingCLM V X, hermitianRectangularCompression_embedding V hV X⟩

/-- Compression and extension are adjoints for the real trace pairing. -/
theorem hermitianRectangularCompression_trace_adjoint (V : Matrix n m ℂ)
    (X : selfAdjoint (Matrix m m ℂ)) (Y : selfAdjoint (Matrix n n ℂ)) :
    realTrace ((X : Matrix m m ℂ) * (hermitianRectangularCompressionCLM V Y : Matrix m m ℂ)) =
      realTrace ((hermitianRectangularEmbeddingCLM V X : Matrix n n ℂ) * (Y : Matrix n n ℂ)) := by
  simp only [hermitianRectangularCompressionCLM_coe, hermitianRectangularEmbeddingCLM_coe]
  calc
    _ = realTrace (((X : Matrix m m ℂ) * Vᴴ * (Y : Matrix n n ℂ)) * V) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [realTrace_rectangular_mul_comm]
      simp only [Matrix.mul_assoc]

def compressedTsallisInverse (θ : ℝ) (hθ : θ ≠ 0)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (V : Matrix n m ℂ) : selfAdjoint (Matrix m m ℂ) →L[ℝ] selfAdjoint (Matrix m m ℂ) :=
  (hermitianRectangularCompressionCLM V).comp
    (((negativeTsallisHessianEquiv θ hθ S hS).symm :
      selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ)).comp
        (hermitianRectangularEmbeddingCLM V))

/-- Exact formula obtained by compressing the full inverse, with no block restriction on S. -/
theorem compressedTsallisInverse_apply (θ : ℝ) (hθ : θ ≠ 0)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (V : Matrix n m ℂ) (X : selfAdjoint (Matrix m m ℂ)) :
    (compressedTsallisInverse θ hθ S hS V X : Matrix m m ℂ) =
      θ⁻¹ • ((Vᴴ * (S : Matrix n n ℂ) * V) * (X : Matrix m m ℂ) *
        (Vᴴ * CFC.sqrt (S : Matrix n n ℂ) * V) +
        (Vᴴ * CFC.sqrt (S : Matrix n n ℂ) * V) * (X : Matrix m m ℂ) *
          (Vᴴ * (S : Matrix n n ℂ) * V)) := by
  change (hermitianRectangularCompressionCLM V
    ((negativeTsallisHessianEquiv θ hθ S hS).symm (hermitianRectangularEmbeddingCLM V X)) :
      Matrix m m ℂ) = _
  rw [hermitianRectangularCompressionCLM_coe, negativeTsallisHessianEquiv_symm_apply,
    hermitianRectangularEmbeddingCLM_coe]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

omit [DecidableEq m] in
theorem realTrace_symmetric_sandwich (X P Q : Matrix m m ℂ) :
    realTrace (X * (P * X * Q + Q * X * P)) = 2 * realTrace (X * P * X * Q) := by
  rw [Matrix.mul_add, realTrace_add]
  have h : realTrace (X * (Q * X * P)) = realTrace (X * P * X * Q) := by
    calc
      _ = realTrace ((X * Q) * (X * P)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [realTrace_mul_comm]; simp only [Matrix.mul_assoc]
  rw [h]
  simp only [← Matrix.mul_assoc]
  ring

theorem hermitianCompression_posDef (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    (hermitianRectangularCompressionCLM V S : Matrix m m ℂ).PosDef := by
  rw [hermitianRectangularCompressionCLM_coe]
  exact posDef_isometry_compression V hV hS

/-- The actual full Tsallis inverse quadratic form is bounded by the reduced inverse form. -/
theorem tsallisInverse_compression_quadratic_le (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) (X : selfAdjoint (Matrix m m ℂ)) :
    realTrace ((X : Matrix m m ℂ) * (compressedTsallisInverse θ hθ.ne' S hS V X : Matrix m m ℂ)) ≤
      realTrace ((X : Matrix m m ℂ) *
        ((negativeTsallisHessianEquiv θ hθ.ne' (hermitianRectangularCompressionCLM V S)
          (hermitianCompression_posDef V hV S hS)).symm X : Matrix m m ℂ)) := by
  rw [compressedTsallisInverse_apply, negativeTsallisHessianEquiv_symm_apply]
  simp only [hermitianRectangularCompressionCLM_coe, Matrix.mul_smul, realTrace_smul,
    realTrace_symmetric_sandwich]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hθ.le)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  have hXX : ((X : Matrix m m ℂ) * (Vᴴ * (S : Matrix n n ℂ) * V) *
      (X : Matrix m m ℂ)).PosSemidef := by
    simpa only [show (X : Matrix m m ℂ)ᴴ = X from X.property] using
      (hS.posSemidef.conjTranspose_mul_mul_same V).conjTranspose_mul_mul_same (X : Matrix m m ℂ)
  exact realTrace_mul_mono hXX (sqrt_isometry_compression_le hS.posSemidef V hV)

/-- The exact nonnegative gap in the inverse comparison, retaining the original scale. -/
theorem tsallisInverse_compression_gap (θ : ℝ) (hθ : θ ≠ 0)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) (X : selfAdjoint (Matrix m m ℂ)) :
    realTrace ((X : Matrix m m ℂ) *
        ((negativeTsallisHessianEquiv θ hθ (hermitianRectangularCompressionCLM V S)
          (hermitianCompression_posDef V hV S hS)).symm X : Matrix m m ℂ)) -
      realTrace ((X : Matrix m m ℂ) * (compressedTsallisInverse θ hθ S hS V X : Matrix m m ℂ)) =
      (2 / θ) * realTrace (((X : Matrix m m ℂ) * (Vᴴ * (S : Matrix n n ℂ) * V) *
        (X : Matrix m m ℂ)) * (CFC.sqrt (Vᴴ * (S : Matrix n n ℂ) * V) -
          Vᴴ * CFC.sqrt (S : Matrix n n ℂ) * V)) := by
  rw [compressedTsallisInverse_apply, negativeTsallisHessianEquiv_symm_apply]
  simp only [hermitianRectangularCompressionCLM_coe, Matrix.mul_smul, realTrace_smul,
    realTrace_symmetric_sandwich, Matrix.mul_sub, realTrace_sub, div_eq_mul_inv]
  ring

/-- The same comparison stated directly for the full supported force and full inverse. -/
theorem tsallisInverse_supported_force_quadratic_le (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) (X : selfAdjoint (Matrix m m ℂ)) :
    realTrace ((hermitianRectangularEmbeddingCLM V X : Matrix n n ℂ) *
      ((negativeTsallisHessianEquiv θ hθ.ne' S hS).symm
        (hermitianRectangularEmbeddingCLM V X) : Matrix n n ℂ)) ≤
      realTrace ((X : Matrix m m ℂ) *
        ((negativeTsallisHessianEquiv θ hθ.ne' (hermitianRectangularCompressionCLM V S)
          (hermitianCompression_posDef V hV S hS)).symm X : Matrix m m ℂ)) := by
  calc
    _ = realTrace ((X : Matrix m m ℂ) *
        (compressedTsallisInverse θ hθ.ne' S hS V X : Matrix m m ℂ)) :=
      (hermitianRectangularCompression_trace_adjoint V X
        ((negativeTsallisHessianEquiv θ hθ.ne' S hS).symm
          (hermitianRectangularEmbeddingCLM V X))).symm
    _ ≤ _ := tsallisInverse_compression_quadratic_le θ hθ S hS V hV X

/-- Specialization to the actual constructed Kraus support, including the zero support. -/
theorem tsallisInverse_kraus_supported_force_quadratic_le {ι : Type*} [Fintype ι]
    (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (X : selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ)) :
    realTrace ((hermitianRectangularEmbeddingCLM (krausSupportEmbedding B) X : Matrix n n ℂ) *
      ((negativeTsallisHessianEquiv θ hθ.ne' S hS).symm
        (hermitianRectangularEmbeddingCLM (krausSupportEmbedding B) X) : Matrix n n ℂ)) ≤
      realTrace ((X : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ) *
        ((negativeTsallisHessianEquiv θ hθ.ne'
          (hermitianRectangularCompressionCLM (krausSupportEmbedding B) S)
          (hermitianCompression_posDef (krausSupportEmbedding B)
            (krausSupportEmbedding_isometry B) S hS)).symm X : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ)) :=
  tsallisInverse_supported_force_quadratic_le θ hθ S hS
    (krausSupportEmbedding B) (krausSupportEmbedding_isometry B) X


section BilinearComparison

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Completing the square for a nonnegative symmetric real bilinear form. -/
theorem bilinear_trial_le (A : E →L[ℝ] (E →L[ℝ] ℝ))
    (hSym : ∀ x y, A x y = A y x) (hPos : ∀ x, 0 ≤ A x x)
    (f : E →L[ℝ] ℝ) (x : E) (hx : A x = f) (y : E) :
    2 * f y - A y y ≤ f x := by
  have hp := hPos (y - x)
  simp only [map_sub, ContinuousLinearMap.sub_apply, hx] at hp
  rw [hSym y x, hx] at hp
  linarith

/-- Curvature domination implies inverse-response domination, including a
non-surjective map from a constrained tangent space. -/
theorem bilinear_inverse_pullback_le
    (A : E ≃L[ℝ] (E →L[ℝ] ℝ)) (B : F ≃L[ℝ] (F →L[ℝ] ℝ))
    (P : E →L[ℝ] F)
    (hSym : ∀ x y, B x y = B y x) (hPos : ∀ x, 0 ≤ B x x)
    (hEnergy : ∀ x, B (P x) (P x) ≤ A x x) (f : F →L[ℝ] ℝ) :
    (f.comp P) (A.symm (f.comp P)) ≤ f (B.symm f) := by
  let x := A.symm (f.comp P)
  have hx : A x = f.comp P := A.apply_symm_apply _
  have he := hEnergy x
  rw [hx] at he
  have ht := bilinear_trial_le (B : F →L[ℝ] (F →L[ℝ] ℝ)) hSym hPos
    f (B.symm f) (B.apply_symm_apply _) (P x)
  change 2 * f (P x) - B (P x) (P x) ≤ f (B.symm f) at ht
  change f (P x) ≤ _
  change B (P x) (P x) ≤ f (P x) at he
  linarith

end BilinearComparison

/-- The bilinear form of the actual negative Tsallis Hessian. -/
def negativeTsallisBilinear (θ : ℝ) (hθ : θ ≠ 0)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) :=
  (tracePairing.comp hermitianInclusion).comp
    (negativeTsallisHessianEquiv θ hθ S hS :
      selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ))

@[simp] theorem negativeTsallisBilinear_apply (θ : ℝ) (hθ : θ ≠ 0)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (X Y : selfAdjoint (Matrix n n ℂ)) :
    negativeTsallisBilinear θ hθ S hS X Y =
      realTrace ((negativeTsallisHessianEquiv θ hθ S hS X : Matrix n n ℂ) *
        (Y : Matrix n n ℂ)) := rfl

theorem negativeTsallisBilinear_symmetric (θ : ℝ) (hθ : θ ≠ 0)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (X Y : selfAdjoint (Matrix n n ℂ)) :
    negativeTsallisBilinear θ hθ S hS X Y = negativeTsallisBilinear θ hθ S hS Y X := by
  have h := (contDiffAt_tsallisPotential θ S hS).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  have he := h X Y
  rw [fderiv_fderiv_tsallisPotential_apply θ hθ S X Y hS,
    fderiv_fderiv_tsallisPotential_apply θ hθ S Y X hS] at he
  simpa only [neg_inj] using he

theorem negativeTsallisBilinear_nonneg (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (X : selfAdjoint (Matrix n n ℂ)) : 0 ≤ negativeTsallisBilinear θ hθ.ne' S hS X X := by
  by_cases hx : X = 0
  · subst X
    simp
  · rw [negativeTsallisBilinear_apply, realTrace_mul_comm]
    exact (negativeTsallisHessian_quadratic_pos θ hθ S X hS hx).le

/-- Variational lower bound for actual Tsallis curvature at an arbitrary direction. -/
theorem tsallis_curvature_trial_le (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (F Y : selfAdjoint (Matrix n n ℂ)) :
    2 * realTrace ((F : Matrix n n ℂ) * (Y : Matrix n n ℂ)) -
      realTrace ((F : Matrix n n ℂ) *
        ((negativeTsallisHessianEquiv θ hθ.ne' S hS).symm F : Matrix n n ℂ)) ≤
      negativeTsallisBilinear θ hθ.ne' S hS Y Y := by
  have ht := bilinear_trial_le (negativeTsallisBilinear θ hθ.ne' S hS)
    (negativeTsallisBilinear_symmetric θ hθ.ne' S hS)
    (negativeTsallisBilinear_nonneg θ hθ S hS)
    (tracePairing (F : Matrix n n ℂ))
    ((negativeTsallisHessianEquiv θ hθ.ne' S hS).symm F) (by
      apply ContinuousLinearMap.ext
      intro Z
      simp only [negativeTsallisBilinear_apply, ContinuousLinearEquiv.apply_symm_apply,
        tracePairing_apply]) Y
  simp only [tracePairing_apply] at ht
  linarith

/-- The actual full Tsallis curvature dominates the reduced curvature of the
compressed direction, including all off-support components of the direction. -/
theorem tsallis_curvature_compression_le (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) (Y : selfAdjoint (Matrix n n ℂ)) :
    negativeTsallisBilinear θ hθ.ne' (hermitianRectangularCompressionCLM V S)
      (hermitianCompression_posDef V hV S hS)
      (hermitianRectangularCompressionCLM V Y) (hermitianRectangularCompressionCLM V Y) ≤
        negativeTsallisBilinear θ hθ.ne' S hS Y Y := by
  let S₀ := hermitianRectangularCompressionCLM V S
  let hS₀ := hermitianCompression_posDef V hV S hS
  let Y₀ := hermitianRectangularCompressionCLM V Y
  let A₀ := negativeTsallisHessianEquiv θ hθ.ne' S₀ hS₀
  let X := A₀ Y₀
  have hi := tsallisInverse_supported_force_quadratic_le θ hθ S hS V hV X
  have ht := tsallis_curvature_trial_le θ hθ S hS (hermitianRectangularEmbeddingCLM V X) Y
  have hs : (negativeTsallisHessianEquiv θ hθ.ne' S₀ hS₀).symm X = Y₀ :=
    A₀.symm_apply_apply Y₀
  change realTrace ((hermitianRectangularEmbeddingCLM V X : Matrix n n ℂ) *
      ((negativeTsallisHessianEquiv θ hθ.ne' S hS).symm
        (hermitianRectangularEmbeddingCLM V X) : Matrix n n ℂ)) ≤
    realTrace ((X : Matrix m m ℂ) * ((negativeTsallisHessianEquiv θ hθ.ne' S₀ hS₀).symm X :
      Matrix m m ℂ)) at hi
  rw [hs] at hi
  rw [← hermitianRectangularCompression_trace_adjoint V X Y] at ht
  change realTrace ((X : Matrix m m ℂ) * (Y₀ : Matrix m m ℂ)) ≤ _
  change 2 * realTrace ((X : Matrix m m ℂ) * (Y₀ : Matrix m m ℂ)) - _ ≤ _ at ht
  linarith


section ActualSourceComparison

set_option maxHeartbeats 600000

variable {ι : Type*} [Fintype ι]

/-- Exact equality of the two joint fidelity directions under the actual support reduction. -/
theorem krausReducedPair_eq_reducedFamily (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (X : selfAdjoint (Matrix n n ℂ)) :
    krausReducedPairCLM B X =
      krausSourceJoint (krausReducedFamily B) (krausReducedDensityCLM B X) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (krausReducedSourceCLM B X : Matrix _ _ ℂ) =
      krausChannel (krausReducedFamily B) (krausReducedDensityCLM B X : Matrix _ _ ℂ)
    rw [krausReducedSourceCLM_coe, krausReducedDensityCLM_coe,
      krausReducedFamily_channel B hB]

/-- The free curvature of the original singular-source objective is exactly the
pullback of the faithful reduced-family curvature, in every Hermitian direction. -/
theorem krausSourceFidelity_hessian_reducedFamily (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (S X Y : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (fun A => fderiv ℝ (krausSourceFidelity B) A) S X Y =
      fderiv ℝ (fun A => fderiv ℝ (krausSourceFidelity (krausReducedFamily B)) A)
        (krausReducedDensityCLM B S) (krausReducedDensityCLM B X)
        (krausReducedDensityCLM B Y) := by
  rw [fderiv_fderiv_krausSourceFidelity_apply_source_unrestricted B S X Y hS,
    fderiv_fderiv_krausSourceFidelity_apply (krausReducedFamily B)
      (krausReducedDensityCLM B S) (krausReducedDensityCLM B X) (krausReducedDensityCLM B Y)
      (krausCompressedDensity_posDef B hS) (krausReducedFamily_source_posDef B hB hS)]
  simp only [krausReducedPair_eq_reducedFamily B hB]

/-- Full actual density curvature dominates the reduced actual density curvature.
The linear density term may differ freely, since it has zero second derivative. -/
theorem densityNegativeHessian_reducedFamily_le (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian)
    (H₀ : Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S X : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    densityNegativeHessian H₀ (krausReducedFamily B) θ (krausReducedDensityCLM B S)
      (krausReducedDensityCLM B X) (krausReducedDensityCLM B X) ≤
      densityNegativeHessian H B θ S X X := by
  have ht := tsallis_curvature_compression_le θ hθ S hS
    (krausSupportEmbedding B) (krausSupportEmbedding_isometry B) X
  change -fderiv ℝ (fun A => fderiv ℝ
    (hermitianDensityObjective H₀ (krausReducedFamily B) θ) A)
    (krausReducedDensityCLM B S) (krausReducedDensityCLM B X) (krausReducedDensityCLM B X) ≤
      -fderiv ℝ (fun A => fderiv ℝ (hermitianDensityObjective H B θ) A) S X X
  rw [fderiv_fderiv_hermitianDensityObjective_apply_source_unrestricted,
    fderiv_fderiv_hermitianDensityObjective_apply_source_unrestricted,
    krausSourceFidelity_hessian_reducedFamily B hB S X X hS,
    fderiv_fderiv_tsallisPotential_apply θ hθ.ne' _ _ _ (krausCompressedDensity_posDef B hS),
    fderiv_fderiv_tsallisPotential_apply θ hθ.ne' S X X hS]
  · change negativeTsallisBilinear θ hθ.ne' (krausReducedDensityCLM B S)
      (krausCompressedDensity_posDef B hS) (krausReducedDensityCLM B X)
        (krausReducedDensityCLM B X) ≤ negativeTsallisBilinear θ hθ.ne' S hS X X at ht
    simp only [negativeTsallisBilinear_apply] at ht
    linarith
  · exact hS
  · exact krausCompressedDensity_posDef B hS

local instance singularTransferFiniteDimensional {j : Type*} [Fintype j] [DecidableEq j] :
    FiniteDimensional ℝ (selfAdjoint (Matrix j j ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix j j ℂ)))

/-- The unconstrained actual negative density Hessian, with arbitrary source rank. -/
def fullDensityHessianEquiv (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    selfAdjoint (Matrix n n ℂ) ≃L[ℝ] (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) :=
  positiveBilinearEquiv (densityNegativeHessian H B θ S)
    (fun X hX => negativeDensityHessian_quadratic_pos_source_unrestricted H B θ hθ S X hS hX)

@[simp] theorem fullDensityHessianEquiv_apply (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (X : selfAdjoint (Matrix n n ℂ)) :
    fullDensityHessianEquiv H B θ hθ S hS X = densityNegativeHessian H B θ S X := rfl

theorem densityNegativeHessian_symmetric_source_unrestricted (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (X Y : selfAdjoint (Matrix n n ℂ)) :
    densityNegativeHessian H B θ S X Y = densityNegativeHessian H B θ S Y X := by
  have h := (contDiffAt_hermitianDensityObjective_source_unrestricted H B θ S hS).isSymmSndFDerivAt
    (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)
  exact congrArg Neg.neg (h X Y)

theorem densityNegativeHessian_nonneg_source_unrestricted (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (X : selfAdjoint (Matrix n n ℂ)) :
    0 ≤ densityNegativeHessian H B θ S X X := by
  by_cases hx : X = 0
  · subst X; simp
  · exact (negativeDensityHessian_quadratic_pos_source_unrestricted H B θ hθ S X hS hx).le

local instance singularTransferTangentNormedGroup : NormedAddCommGroup (densityTangent (n := n)) :=
  inferInstance
local instance singularTransferTangentNormedSpace : NormedSpace ℝ (densityTangent (n := n)) :=
  inferInstance

/-- The actual constrained inverse response at a singular source is bounded by the
unconstrained inverse response of the faithful reduced family. No trace-one
assumption is imposed on the compressed density, and the parameter θ is unchanged. -/
theorem singular_constrained_inverse_response_le (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian)
    (H₀ : Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef)
    (f : selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ) →L[ℝ] ℝ) :
    let P := (krausReducedDensityCLM B).comp (densityTangent (n := n)).subtypeL
    (f.comp P) ((densityTangentHessianEquiv_source_unrestricted H B θ hθ S hS).symm
      (f.comp P)) ≤
      f ((fullDensityHessianEquiv H₀ (krausReducedFamily B) θ hθ (krausReducedDensityCLM B S)
        (krausCompressedDensity_posDef B hS)).symm f) := by
  dsimp only
  refine bilinear_inverse_pullback_le (E := densityTangent (n := n))
    (F := selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ))
    (densityTangentHessianEquiv_source_unrestricted H B θ hθ S hS)
    (fullDensityHessianEquiv H₀ (krausReducedFamily B) θ hθ (krausReducedDensityCLM B S)
      (krausCompressedDensity_posDef B hS))
    ((krausReducedDensityCLM B).comp (densityTangent (n := n)).subtypeL) ?_ ?_ ?_ f
  · exact densityNegativeHessian_symmetric_source_unrestricted H₀ (krausReducedFamily B) θ
      (krausReducedDensityCLM B S) (krausCompressedDensity_posDef B hS)
  · exact densityNegativeHessian_nonneg_source_unrestricted H₀ (krausReducedFamily B) θ hθ
      (krausReducedDensityCLM B S) (krausCompressedDensity_posDef B hS)
  · intro X
    exact densityNegativeHessian_reducedFamily_le H B hB H₀ θ hθ S X hS


/-- The actual tangent force functional is exactly the pullback of a supported force. -/
theorem densityCenterFunctional_supported_pullback (B : ι → Matrix n n ℂ)
    (F : selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ)) :
    densityCenterFunctional (hermitianRectangularEmbeddingCLM (krausSupportEmbedding B) F) =
      (tracePairing (F : Matrix _ _ ℂ)).comp
        ((krausReducedDensityCLM B).comp (densityTangent (n := n)).subtypeL) := by
  apply ContinuousLinearMap.ext
  intro X
  exact (hermitianRectangularCompression_trace_adjoint (krausSupportEmbedding B) F X).symm

/-- Transfer of the actual optimizer derivative for any supported force. -/
theorem densityResponseDerivative_supported_le_reduced_inverse (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian)
    (H₀ : Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef)
    (F : selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ)) :
    let X := hermitianRectangularEmbeddingCLM (krausSupportEmbedding B) F
    realTrace ((densityResponseDerivative_source_unrestricted H B θ hθ S hS X : Matrix n n ℂ) *
      (X : Matrix n n ℂ)) ≤
      tracePairing (F : Matrix _ _ ℂ)
        ((fullDensityHessianEquiv H₀ (krausReducedFamily B) θ hθ (krausReducedDensityCLM B S)
          (krausCompressedDensity_posDef B hS)).symm (tracePairing (F : Matrix _ _ ℂ))) := by
  dsimp only
  rw [realTrace_mul_comm]
  change densityCenterFunctional (hermitianRectangularEmbeddingCLM (krausSupportEmbedding B) F)
    ((densityTangentHessianEquiv_source_unrestricted H B θ hθ S hS).symm
      (densityCenterFunctional (hermitianRectangularEmbeddingCLM (krausSupportEmbedding B) F))) ≤ _
  simp only [densityCenterFunctional_supported_pullback B F]
  have ht := singular_constrained_inverse_response_le (n := n) (ι := ι) H B hB H₀ θ hθ S hS
    (tracePairing (F : Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ))
  dsimp only at ht
  exact ht

/-- The Hessian of the actual attained potential transfers to the faithful reduced
unconstrained density response, even when the original source is singular. -/
theorem potential_hessian_supported_le_reduced_inverse [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian)
    (H₀ : Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ)
    (θ : ℝ) (hθ : 0 < θ)
    (F : selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ)) :
    let S := hermitianDensityOptimizer (H : Matrix n n ℂ) B θ
    let X := hermitianRectangularEmbeddingCLM (krausSupportEmbedding B) F
    fderiv ℝ (fun K => fderiv ℝ (hermitianDensityPotential B θ) K) H X X ≤
      tracePairing (F : Matrix _ _ ℂ)
        ((fullDensityHessianEquiv H₀ (krausReducedFamily B) θ hθ (krausReducedDensityCLM B S)
          (krausCompressedDensity_posDef B (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ))).symm
            (tracePairing (F : Matrix _ _ ℂ))) := by
  dsimp only
  rw [fderiv_fderiv_hermitianDensityPotential_apply_source_unrestricted H _ _ B hθ]
  exact densityResponseDerivative_supported_le_reduced_inverse (n := n) (ι := ι) (H : Matrix n n ℂ) B hB H₀ θ hθ
    (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)
      (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ) F

end ActualSourceComparison

end
end MatrixSpencer
