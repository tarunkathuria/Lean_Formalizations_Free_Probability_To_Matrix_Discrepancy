import MatrixSpencer.KrausSupport
import MatrixSpencer.FidelityCompression
import MatrixSpencer.DensityHessian

/-!
# The actual Kraus compression in rectangular matrix coordinates

The embedding comes from the fixed support basis. All identities refer to the
concrete source and its constructed compression, rather than an assumed support
factorization.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Filter Topology

namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

noncomputable local instance krausBridgeEuclideanInner : InnerProductSpace ℂ (EuclideanSpace ℂ n) :=
  PiLp.innerProductSpace (fun _ : n => ℂ)

/-- Columns are the orthonormal basis vectors of the actual fixed source support. -/
noncomputable def krausSupportEmbedding (B : ι → Matrix n n ℂ) :
    Matrix n (Fin (Module.finrank ℂ (krausSupport B))) ℂ :=
  fun j i => (krausSupportBasis B i : EuclideanSpace ℂ n) j

/-- The constructed rectangular embedding is an isometry, including empty support. -/
theorem krausSupportEmbedding_isometry (B : ι → Matrix n n ℂ) :
    (krausSupportEmbedding B)ᴴ * krausSupportEmbedding B = 1 := by
  ext i j
  calc
    _ = inner ℂ (krausSupportBasis B i) (krausSupportBasis B j) := by
      simp only [krausSupportEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Submodule.coe_inner, PiLp.inner_apply, RCLike.inner_apply]
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _
    _ = _ := by rw [(krausSupportBasis B).inner_eq_ite, Matrix.one_apply]

/-- Matrix multiplication by the embedding realizes support-basis synthesis. -/
theorem krausSupportEmbedding_mulVec_repr (B : ι → Matrix n n ℂ) (x : krausSupport B) :
    krausSupportEmbedding B *ᵥ WithLp.ofLp ((krausSupportBasis B).repr x) =
      WithLp.ofLp (x : EuclideanSpace ℂ n) := by
  ext j
  let p : krausSupport B →ₗ[ℂ] ℂ :=
    (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : n => ℂ) j).comp (krausSupport B).subtype
  have h := congrArg p ((krausSupportBasis B).sum_repr x)
  simp only [map_sum, map_smul] at h
  change (∑ i, (krausSupportBasis B).repr x i * (krausSupportBasis B i : EuclideanSpace ℂ n) j) =
    (x : EuclideanSpace ℂ n) j at h
  simpa only [krausSupportEmbedding, Matrix.mulVec, dotProduct, PiLp.ofLp_apply, mul_comm] using h

/-- The adjoint embedding gives the coordinates of the actual orthogonal projection. -/
theorem krausSupportEmbedding_adjoint_mulVec (B : ι → Matrix n n ℂ)
    (x : EuclideanSpace ℂ n) :
    (krausSupportEmbedding B)ᴴ *ᵥ WithLp.ofLp x =
      WithLp.ofLp ((krausSupportBasis B).repr ((krausSupport B).orthogonalProjection x)) := by
  ext i
  simp only [PiLp.ofLp_apply]
  rw [(krausSupportBasis B).repr_apply_apply,
    Submodule.inner_orthogonalProjection_eq_of_mem_left]
  simp only [krausSupportEmbedding, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    PiLp.inner_apply, RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The already constructed compressed matrix is exactly rectangular matrix compression. -/
theorem krausCompressedSource_eq_compression (B : ι → Matrix n n ℂ) (S : Matrix n n ℂ) :
    krausCompressedSource B S =
      (krausSupportEmbedding B)ᴴ * krausChannel B S * krausSupportEmbedding B := by
  rw [Matrix.mul_assoc]
  ext i j
  unfold krausCompressedSource
  rw [LinearMap.toMatrix_apply]
  change (krausSupportBasis B).repr (krausSupportOperator B S (krausSupportBasis B j)) i = _
  rw [(krausSupportBasis B).repr_apply_apply]
  change inner ℂ (krausSupportBasis B i)
    ((krausSupport B).orthogonalProjection
      (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S)
        (krausSupportBasis B j : EuclideanSpace ℂ n))) = _
  rw [Submodule.inner_orthogonalProjection_eq_of_mem_left,
    EuclideanSpace.inner_eq_star_dotProduct]
  change (krausChannel B S *ᵥ WithLp.ofLp (krausSupportBasis B j : EuclideanSpace ℂ n)) ⬝ᵥ
    star (WithLp.ofLp (krausSupportBasis B i : EuclideanSpace ℂ n)) = _
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, krausSupportEmbedding,
    Matrix.conjTranspose_apply, Pi.star_apply, PiLp.ofLp_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- At a faithful input the constructed embedding reconstructs the full actual source. -/
theorem krausCompressedSource_reconstruct_posDef (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    krausSupportEmbedding B * krausCompressedSource B S * (krausSupportEmbedding B)ᴴ =
      krausChannel B S := by
  apply (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).injective
  apply ContinuousLinearMap.ext
  intro x
  apply WithLp.ofLp_injective
  change (krausSupportEmbedding B * krausCompressedSource B S * (krausSupportEmbedding B)ᴴ) *ᵥ
    WithLp.ofLp x = krausChannel B S *ᵥ WithLp.ofLp x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    krausSupportEmbedding_adjoint_mulVec]
  have hcoords := (krausSupportOperator B S).toLinearMap.toMatrix_mulVec_repr
    (krausSupportBasis B).toBasis (krausSupportBasis B).toBasis
    ((krausSupport B).orthogonalProjection x)
  change krausCompressedSource B S *ᵥ
      WithLp.ofLp ((krausSupportBasis B).repr ((krausSupport B).orthogonalProjection x)) =
    WithLp.ofLp ((krausSupportBasis B).repr
      (krausSupportOperator B S ((krausSupport B).orthogonalProjection x))) at hcoords
  rw [hcoords, krausSupportEmbedding_mulVec_repr]
  have h := congrArg (fun T : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n => T x)
    (krausSupportOperator_reconstruct B hS)
  exact congrArg WithLp.ofLp h

/-- The source compression depends continuously on the full physical matrix. -/
theorem continuous_krausCompressedSource (B : ι → Matrix n n ℂ) :
    Continuous (krausCompressedSource B) := by
  change Continuous (fun S => krausCompressedSource B S)
  simp_rw [krausCompressedSource_eq_compression]
  exact (continuous_const.matrix_mul (continuous_krausChannel B)).matrix_mul continuous_const

/-- Exact reconstruction also holds at singular input densities. -/
theorem krausCompressedSource_reconstruct (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    krausSupportEmbedding B * krausCompressedSource B S * (krausSupportEmbedding B)ᴴ =
      krausChannel B S := by
  have hl := (((continuous_const : Continuous (fun _ : Matrix n n ℂ => krausSupportEmbedding B)).matrix_mul
    (continuous_krausCompressedSource B)).matrix_mul
    (continuous_const : Continuous (fun _ : Matrix n n ℂ => (krausSupportEmbedding B)ᴴ))).tendsto S
  have hl' := hl.comp (regularize_tendsto S)
  have hr := ((continuous_krausChannel B).tendsto S).comp (regularize_tendsto S)
  apply tendsto_nhds_unique hl'
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with r hrpos
  exact (krausCompressedSource_reconstruct_posDef B (regularize_posDef hS hrpos)).symm

/-- The density argument compressed to the same fixed physical support. -/
noncomputable def krausCompressedDensity (B : ι → Matrix n n ℂ) (S : Matrix n n ℂ) :
    Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ :=
  (krausSupportEmbedding B)ᴴ * S * krausSupportEmbedding B

theorem krausCompressedDensity_posDef (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) : (krausCompressedDensity B S).PosDef :=
  posDef_isometry_compression (krausSupportEmbedding B) (krausSupportEmbedding_isometry B) hS

/-- The actual fidelity equals fidelity of the two actual compressed matrices. -/
theorem fidelity_kraus_support_compression (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    fidelity S (krausChannel B S) =
      fidelity (krausCompressedDensity B S) (krausCompressedSource B S) := by
  rw [← krausCompressedSource_reconstruct B hS]
  exact fidelity_isometry_compression (krausSupportEmbedding B) (krausSupportEmbedding_isometry B)
    hS (krausCompressedSource_posSemidef B hS)

/-- Both compressed fidelity arguments are faithful at every faithful physical input,
without any nonzero-support assumption. -/
theorem kraus_compressed_pair_posDef (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    (krausCompressedDensity B S).PosDef ∧ (krausCompressedSource B S).PosDef :=
  ⟨krausCompressedDensity_posDef B hS, krausCompressedSource_posDef B hS⟩

/-- Rectangular compression as a real continuous linear map on Hermitian matrices. -/
noncomputable def hermitianRectangularCompressionCLM {m : Type*} [Fintype m]
    [DecidableEq m] (V : Matrix n m ℂ) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix m m ℂ) := by
  letI : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
    inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
  let L : selfAdjoint (Matrix n n ℂ) →ₗ[ℝ] selfAdjoint (Matrix m m ℂ) :=
    { toFun := fun X => ⟨Vᴴ * (X : Matrix n n ℂ) * V,
        Matrix.isHermitian_conjTranspose_mul_mul V X.property⟩
      map_add' := by
        intro X Y
        apply Subtype.ext
        change Vᴴ * ((X : Matrix n n ℂ) + (Y : Matrix n n ℂ)) * V = _
        simp only [Matrix.mul_add, Matrix.add_mul]
        rfl
      map_smul' := by
        intro r X
        apply Subtype.ext
        change Vᴴ * (r • (X : Matrix n n ℂ)) * V = _
        simp only [Matrix.mul_smul, Matrix.smul_mul]
        rfl }
  exact L.toContinuousLinearMap

@[simp] theorem hermitianRectangularCompressionCLM_coe {m : Type*} [Fintype m]
    [DecidableEq m] (V : Matrix n m ℂ) (S : selfAdjoint (Matrix n n ℂ)) :
    (hermitianRectangularCompressionCLM V S : Matrix m m ℂ) =
      Vᴴ * (S : Matrix n n ℂ) * V := rfl

/-- The actual first reduced argument, with its real Hermitian linear structure. -/
noncomputable def krausReducedDensityCLM (B : ι → Matrix n n ℂ) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ]
      selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
        (Fin (Module.finrank ℂ (krausSupport B))) ℂ) :=
  hermitianRectangularCompressionCLM (krausSupportEmbedding B)

/-- The actual second reduced argument, with its real Hermitian linear structure. -/
noncomputable def krausReducedSourceCLM (B : ι → Matrix n n ℂ) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ]
      selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
        (Fin (Module.finrank ℂ (krausSupport B))) ℂ) :=
  (hermitianRectangularCompressionCLM (krausSupportEmbedding B)).comp (hermitianKrausChannel B)

@[simp] theorem krausReducedDensityCLM_coe (B : ι → Matrix n n ℂ)
    (S : selfAdjoint (Matrix n n ℂ)) :
    (krausReducedDensityCLM B S : Matrix _ _ ℂ) =
      krausCompressedDensity B (S : Matrix n n ℂ) := rfl

@[simp] theorem krausReducedSourceCLM_coe (B : ι → Matrix n n ℂ)
    (S : selfAdjoint (Matrix n n ℂ)) :
    (krausReducedSourceCLM B S : Matrix _ _ ℂ) =
      krausCompressedSource B (S : Matrix n n ℂ) :=
  (krausCompressedSource_eq_compression B (S : Matrix n n ℂ)).symm

/-- The two reduced inputs as one continuous linear pullback for joint fidelity. -/
noncomputable def krausReducedPairCLM (B : ι → Matrix n n ℂ) :=
  (krausReducedDensityCLM B).prod (krausReducedSourceCLM B)

end MatrixSpencer
