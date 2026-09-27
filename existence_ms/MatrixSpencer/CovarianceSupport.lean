import MatrixSpencer.CovarianceSource
import MatrixSpencer.KrausCompressionBridge

/-!
# A fixed physical support while the positive covariance varies

Invertible real mixing preserves the common kernel of the physical matrices.
The embedding below therefore depends only on the original Hermitian family,
not on the covariance or density being differentiated.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Filter Topology

namespace MatrixSpencer

noncomputable section

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

local instance covarianceSupportEuclideanInner : InnerProductSpace ℂ (EuclideanSpace ℂ n) :=
  PiLp.innerProductSpace (fun _ : n => ℂ)

omit [Fintype n] [DecidableEq ι] [DecidableEq n] in
theorem mixedKraus_comp (A : ι → Matrix n n ℂ) (R Q : Matrix ι ι ℝ) :
    mixedKraus (mixedKraus A R) Q = mixedKraus A (R * Q) := by
  funext a
  simp only [mixedKraus, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

omit [Fintype n] [DecidableEq n] in
theorem mixedKraus_one (A : ι → Matrix n n ℂ) : mixedKraus A (1 : Matrix ι ι ℝ) = A := by
  funext a
  simp [mixedKraus, Matrix.one_apply]

omit [DecidableEq ι] [DecidableEq n] in
theorem mixedKraus_mulVec_eq_zero (A : ι → Matrix n n ℂ) (R : Matrix ι ι ℝ)
    (x : n → ℂ) (hx : ∀ i, A i *ᵥ x = 0) : ∀ a, mixedKraus A R a *ᵥ x = 0 := by
  intro a
  simp only [mixedKraus, Matrix.sum_mulVec, Matrix.smul_mulVec, hx,
    smul_zero, Finset.sum_const_zero]

omit [DecidableEq n] in
/-- Invertible coefficient mixing does not change the common physical kernel. -/
theorem mixedKraus_common_kernel_iff (A : ι → Matrix n n ℂ) {R : Matrix ι ι ℝ}
    (hR : IsUnit R) (x : n → ℂ) :
    (∀ a, mixedKraus A R a *ᵥ x = 0) ↔ ∀ i, A i *ᵥ x = 0 := by
  constructor
  · intro hx
    have h := mixedKraus_mulVec_eq_zero (mixedKraus A R) R⁻¹ x hx
    rwa [mixedKraus_comp, Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp hR),
      mixedKraus_one] at h
  · exact mixedKraus_mulVec_eq_zero A R x

omit [DecidableEq n] in
/-- The kernel of the actual covariance source is independent of both faithful inputs. -/
theorem covarianceSource_mulVec_eq_zero_iff (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosDef)
    {S : Matrix n n ℂ} (hS : S.PosDef) (x : n → ℂ) :
    covarianceSource A C S *ᵥ x = 0 ↔ ∀ i, A i *ᵥ x = 0 := by
  rw [covarianceSource_eq_kraus A hA hC.posSemidef,
    krausChannel_mulVec_eq_zero_iff _ hS]
  simp only [covarianceKraus, fun i => (mixedKraus_isHermitian A (CFC.sqrt C) hA i).eq]
  exact mixedKraus_common_kernel_iff A hC.posDef_sqrt.isUnit x

theorem covarianceSource_ker_eq_identity (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosDef)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    LinearMap.ker (covarianceSource A C S).mulVecLin =
      LinearMap.ker (krausChannel A 1).mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply,
    covarianceSource_mulVec_eq_zero_iff A hA hC hS,
    krausChannel_mulVec_eq_zero_iff A Matrix.PosDef.one, fun i => (hA i).eq]

theorem covarianceSource_euclidean_ker_eq_identity (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosDef)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    LinearMap.ker (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
      (covarianceSource A C S)).toLinearMap =
      LinearMap.ker (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
        (krausChannel A 1)).toLinearMap := by
  ext x
  have he (M : Matrix n n ℂ) :
      Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M x = 0 ↔ M *ᵥ WithLp.ofLp x = 0 := by
    constructor
    · intro h
      simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_zero] using congrArg WithLp.ofLp h
    · intro h
      apply WithLp.ofLp_injective
      simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_zero] using h
  change Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (covarianceSource A C S) x = 0 ↔
    Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel A 1) x = 0
  simp only [he, covarianceSource_mulVec_eq_zero_iff A hA hC hS,
    krausChannel_mulVec_eq_zero_iff A Matrix.PosDef.one, fun i => (hA i).eq]

/-- This range uses the support chosen from the original family at identity covariance. -/
theorem covarianceSource_range_eq_support (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosDef)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    LinearMap.range (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
      (covarianceSource A C S)).toLinearMap = krausSupport A := by
  have hsym := isHermitian_toEuclideanCLM_symmetric
    (covarianceSource_posSemidef A hA hC.posSemidef hS.posSemidef).isHermitian
  have hI := isHermitian_toEuclideanCLM_symmetric
    (krausChannel_posSemidef A Matrix.PosSemidef.one).isHermitian
  have hk := covarianceSource_euclidean_ker_eq_identity A hA hC hS
  exact le_antisymm
    ((ContinuousLinearMap.ker_le_ker_iff_range_le_range hsym hI).mp hk.ge)
    ((ContinuousLinearMap.ker_le_ker_iff_range_le_range hI hsym).mp hk.le)

theorem covarianceSource_ker_eq_support_orthogonal (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosDef)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    LinearMap.ker (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
      (covarianceSource A C S)).toLinearMap = (krausSupport A)ᗮ := by
  rw [covarianceSource_euclidean_ker_eq_identity A hA hC hS]
  exact krausChannel_ker_eq_support_orthogonal A Matrix.PosDef.one

omit [DecidableEq ι] in
/-- The matrix of the fixed support projection in physical coordinates. -/
theorem krausSupportEmbedding_projection (A : ι → Matrix n n ℂ) :
    Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
      (krausSupportEmbedding A * (krausSupportEmbedding A)ᴴ) =
      (krausSupport A).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  apply WithLp.ofLp_injective
  rw [Matrix.ofLp_toEuclideanCLM, ← Matrix.mulVec_mulVec,
    krausSupportEmbedding_adjoint_mulVec, krausSupportEmbedding_mulVec_repr]
  rfl

theorem covarianceSource_fixed_projection_left (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosDef)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    (krausSupportEmbedding A * (krausSupportEmbedding A)ᴴ) * covarianceSource A C S =
      covarianceSource A C S := by
  apply (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).injective
  rw [map_mul]
  change Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
      (krausSupportEmbedding A * (krausSupportEmbedding A)ᴴ) *
      Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (covarianceSource A C S) =
      Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (covarianceSource A C S)
  rw [krausSupportEmbedding_projection]
  apply ContinuousLinearMap.ext
  intro x
  change (krausSupport A).starProjection
      (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (covarianceSource A C S) x) = _
  apply Submodule.starProjection_eq_self_iff.mpr
  rw [← covarianceSource_range_eq_support A hA hC hS]
  exact LinearMap.mem_range_self _ x

theorem covarianceSource_fixed_projection_right (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosDef)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    covarianceSource A C S * (krausSupportEmbedding A * (krausSupportEmbedding A)ᴴ) =
      covarianceSource A C S := by
  have h := congrArg Matrix.conjTranspose (covarianceSource_fixed_projection_left A hA hC hS)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (covarianceSource_posSemidef A hA hC.posSemidef hS.posSemidef).isHermitian.eq] using h

/-- Compression uses a single embedding fixed from the original physical family. -/
def covarianceCompressedSource (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ)
    (S : Matrix n n ℂ) :
    Matrix (Fin (Module.finrank ℂ (krausSupport A)))
      (Fin (Module.finrank ℂ (krausSupport A))) ℂ :=
  (krausSupportEmbedding A)ᴴ * covarianceSource A C S * krausSupportEmbedding A

theorem covarianceCompressedSource_posSemidef (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    (covarianceCompressedSource A C S).PosSemidef :=
  (covarianceSource_posSemidef A hA hC hS).conjTranspose_mul_mul_same (krausSupportEmbedding A)

/-- Positive covariance and density give a faithful source on this one fixed support. -/
theorem covarianceCompressedSource_posDef (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosDef)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    (covarianceCompressedSource A C S).PosDef := by
  apply (covarianceCompressedSource_posSemidef A hA hC.posSemidef hS.posSemidef).posDef_iff_isUnit.mpr
  apply Matrix.mulVec_injective_iff_isUnit.mp
  change Function.Injective (covarianceCompressedSource A C S).mulVecLin
  apply LinearMap.ker_eq_bot.mp
  apply Matrix.ker_mulVecLin_eq_bot_iff.mpr
  intro x hx
  have hform : star (krausSupportEmbedding A *ᵥ x) ⬝ᵥ
      (covarianceSource A C S *ᵥ (krausSupportEmbedding A *ᵥ x)) = 0 := by
    calc
      _ = star x ⬝ᵥ (covarianceCompressedSource A C S *ᵥ x) := by
        simp only [covarianceCompressedSource, star_mulVec, dotProduct_mulVec, vecMul_vecMul]
      _ = 0 := by rw [hx, dotProduct_zero]
  have hpsd := covarianceSource_posSemidef A hA hC.posSemidef hS.posSemidef
  have hz := (hpsd.dotProduct_mulVec_zero_iff (krausSupportEmbedding A *ᵥ x)).mp hform
  have hAz := (covarianceSource_mulVec_eq_zero_iff A hA hC hS _).mp hz
  have hIz : krausChannel A S *ᵥ (krausSupportEmbedding A *ᵥ x) = 0 := by
    apply (krausChannel_mulVec_eq_zero_iff A hS _).mpr
    simpa only [fun i => (hA i).eq] using hAz
  have hcompressed : krausCompressedSource A S *ᵥ x = 0 := by
    rw [krausCompressedSource_eq_compression, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hIz, Matrix.mulVec_zero]
  apply Matrix.mulVec_injective_of_isUnit (krausCompressedSource_posDef A hS).isUnit
  simpa only [Matrix.mulVec_zero] using hcompressed

/-- Exact reconstruction uses an embedding independent of both faithful arguments. -/
theorem covarianceCompressedSource_reconstruct (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosDef)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    krausSupportEmbedding A * covarianceCompressedSource A C S * (krausSupportEmbedding A)ᴴ =
      covarianceSource A C S := by
  calc
    _ = (krausSupportEmbedding A * (krausSupportEmbedding A)ᴴ) * covarianceSource A C S *
        (krausSupportEmbedding A * (krausSupportEmbedding A)ᴴ) := by
      simp only [covarianceCompressedSource, Matrix.mul_assoc]
    _ = _ := by rw [covarianceSource_fixed_projection_left A hA hC hS,
      covarianceSource_fixed_projection_right A hA hC hS]

/-- Fidelity of the actual source has a fixed-support formula as covariance varies. -/
theorem fidelity_covariance_support_compression (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosDef)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    fidelity S (covarianceSource A C S) =
      fidelity (krausCompressedDensity A S) (covarianceCompressedSource A C S) := by
  rw [← covarianceCompressedSource_reconstruct A hA hC hS]
  exact fidelity_isometry_compression (krausSupportEmbedding A) (krausSupportEmbedding_isometry A)
    hS.posSemidef (covarianceCompressedSource_posDef A hA hC hS).posSemidef

theorem covariance_compressed_pair_posDef (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosDef)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    (krausCompressedDensity A S).PosDef ∧ (covarianceCompressedSource A C S).PosDef :=
  ⟨krausCompressedDensity_posDef A hS, covarianceCompressedSource_posDef A hA hC hS⟩

omit [DecidableEq ι] in
theorem continuous_covarianceCompressedSource (A : ι → Matrix n n ℂ) :
    Continuous (fun p : Matrix ι ι ℝ × Matrix n n ℂ => covarianceCompressedSource A p.1 p.2) := by
  unfold covarianceCompressedSource
  exact (continuous_const.matrix_mul (continuous_covarianceSource A)).matrix_mul continuous_const

/-- Reconstruction persists at the boundary, still with the same original embedding. -/
theorem covarianceCompressedSource_reconstruct_posSemidef (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    krausSupportEmbedding A * covarianceCompressedSource A C S * (krausSupportEmbedding A)ᴴ =
      covarianceSource A C S := by
  have hct : Tendsto (fun r : ℝ => C + r • (1 : Matrix ι ι ℝ))
      (𝓝[Set.Ioi 0] 0) (𝓝 C) := by
    have hc : Continuous (fun r : ℝ => C + r • (1 : Matrix ι ι ℝ)) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using (hc.tendsto 0).mono_left inf_le_left
  have hp := hct.prodMk_nhds (regularize_tendsto S)
  have hl := (((continuous_const : Continuous
      (fun _ : Matrix ι ι ℝ × Matrix n n ℂ => krausSupportEmbedding A)).matrix_mul
      (continuous_covarianceCompressedSource A)).matrix_mul
      (continuous_const : Continuous
        (fun _ : Matrix ι ι ℝ × Matrix n n ℂ => (krausSupportEmbedding A)ᴴ))).tendsto (C, S)
  have hl' := hl.comp hp
  have hr := ((continuous_covarianceSource A).tendsto (C, S)).comp hp
  apply tendsto_nhds_unique hl'
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with r hrpos
  exact (covarianceCompressedSource_reconstruct A hA
    (Matrix.PosDef.posSemidef_add hC (Matrix.PosDef.one.smul hrpos))
    (regularize_posDef hS hrpos)).symm

theorem fidelity_covariance_support_compression_posSemidef (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    fidelity S (covarianceSource A C S) =
      fidelity (krausCompressedDensity A S) (covarianceCompressedSource A C S) := by
  rw [← covarianceCompressedSource_reconstruct_posSemidef A hA hC hS]
  exact fidelity_isometry_compression (krausSupportEmbedding A) (krausSupportEmbedding_isometry A)
    hS (covarianceCompressedSource_posSemidef A hA hC hS)

end
end MatrixSpencer
