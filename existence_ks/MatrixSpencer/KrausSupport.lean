import MatrixSpencer.DensityPotential
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The fixed support of a Kraus source

For a positive definite input, the kernel of the source is precisely the common
kernel of the adjoints of its Kraus matrices. Thus singularity of the output has
a fixed geometric cause, independent of the input density.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

noncomputable local instance krausSupportEuclideanInner : InnerProductSpace ℂ (EuclideanSpace ℂ n) :=
  PiLp.innerProductSpace (fun _ : n => ℂ)

omit [DecidableEq n] in
/-- The quadratic form of the source is a sum of positive input quadratic forms. -/
theorem krausChannel_quadratic (B : ι → Matrix n n ℂ) (S : Matrix n n ℂ) (x : n → ℂ) :
    (star x ⬝ᵥ (krausChannel B S *ᵥ x)).re =
      ∑ i, (star ((B i)ᴴ *ᵥ x) ⬝ᵥ (S *ᵥ ((B i)ᴴ *ᵥ x))).re := by
  simp only [krausChannel, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← Matrix.mulVec_mulVec, star_mulVec, dotProduct_mulVec,
    vecMul_vecMul, Matrix.conjTranspose_conjTranspose]

omit [DecidableEq n] in
/-- The exact kernel criterion, with no assumption on the rank of the Kraus family. -/
theorem krausChannel_mulVec_eq_zero_iff (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) (x : n → ℂ) :
    krausChannel B S *ᵥ x = 0 ↔ ∀ i, (B i)ᴴ *ᵥ x = 0 := by
  constructor
  · intro hx i
    have hsum : (∑ j, (star ((B j)ᴴ *ᵥ x) ⬝ᵥ (S *ᵥ ((B j)ᴴ *ᵥ x))).re) = 0 := by
      rw [← krausChannel_quadratic, hx, dotProduct_zero, Complex.zero_re]
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hS.posSemidef.re_dotProduct_nonneg
        ((B j)ᴴ *ᵥ x))).mp hsum i (Finset.mem_univ i)
    by_contra hne
    have hp := hS.re_dotProduct_pos hne
    rw [hi] at hp
    exact (lt_irrefl 0) hp
  · intro hx
    simp only [krausChannel, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec]
    simp only [hx, Matrix.mulVec_zero, Finset.sum_const_zero]

omit [DecidableEq n] in
/-- The kernel as an actual submodule of the coefficient vector space. -/
theorem krausChannel_ker_mulVecLin (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    LinearMap.ker (krausChannel B S).mulVecLin =
      ⨅ i, LinearMap.ker ((B i)ᴴ).mulVecLin := by
  ext x
  simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_iInf] using
    krausChannel_mulVec_eq_zero_iff B hS x

/-- In particular, the source kernel equals its value at the identity input. -/
theorem krausChannel_ker_eq_identity (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    LinearMap.ker (krausChannel B S).mulVecLin =
      LinearMap.ker (krausChannel B 1).mulVecLin := by
  rw [krausChannel_ker_mulVecLin B hS, krausChannel_ker_mulVecLin B Matrix.PosDef.one]

/-- The same fixed-kernel statement in the Euclidean operator representation. -/
theorem krausChannel_euclidean_ker_eq_identity (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    LinearMap.ker (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S)).toLinearMap =
      LinearMap.ker (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B 1)).toLinearMap := by
  ext x
  have he (A : Matrix n n ℂ) :
      Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x = 0 ↔ A *ᵥ WithLp.ofLp x = 0 := by
    constructor
    · intro h
      simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_zero] using congrArg WithLp.ofLp h
    · intro h
      apply WithLp.ofLp_injective
      simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_zero] using h
  change Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S) x = 0 ↔
    Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B 1) x = 0
  rw [he, he, krausChannel_mulVec_eq_zero_iff B hS,
    krausChannel_mulVec_eq_zero_iff B Matrix.PosDef.one]

/-- A Hermitian matrix yields a symmetric Euclidean operator. -/
theorem isHermitian_toEuclideanCLM_symmetric {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).toLinearMap.IsSymmetric := by
  have h : IsSelfAdjoint A := hA
  exact (h.map (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))).isSymmetric

/-- The actual source range is independent of its positive definite input. -/
theorem krausChannel_euclidean_range_eq_identity (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    LinearMap.range (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S)).toLinearMap =
      LinearMap.range (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B 1)).toLinearMap := by
  have hA := isHermitian_toEuclideanCLM_symmetric (krausChannel_posSemidef B hS.posSemidef).isHermitian
  have hI := isHermitian_toEuclideanCLM_symmetric
    (krausChannel_posSemidef B Matrix.PosSemidef.one).isHermitian
  have hk := krausChannel_euclidean_ker_eq_identity B hS
  exact le_antisymm
    ((ContinuousLinearMap.ker_le_ker_iff_range_le_range hA hI).mp hk.ge)
    ((ContinuousLinearMap.ker_le_ker_iff_range_le_range hI hA).mp hk.le)

/-- The fixed physical output support, defined from the identity input alone. -/
noncomputable def krausSupport (B : ι → Matrix n n ℂ) : Submodule ℂ (EuclideanSpace ℂ n) :=
  LinearMap.range (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B 1)).toLinearMap

theorem krausChannel_range_eq_support (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    LinearMap.range (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S)).toLinearMap =
      krausSupport B :=
  krausChannel_euclidean_range_eq_identity B hS

theorem krausChannel_ker_eq_support_orthogonal (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    LinearMap.ker (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S)).toLinearMap =
      (krausSupport B)ᗮ := by
  have hsym := isHermitian_toEuclideanCLM_symmetric
    (krausChannel_posSemidef B hS.posSemidef).isHermitian
  rw [← hsym.orthogonal_range, krausChannel_range_eq_support B hS]

/-- Every output lies in the fixed support. -/
theorem krausChannel_apply_mem_support (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) (x : EuclideanSpace ℂ n) :
    Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S) x ∈ krausSupport B := by
  rw [← krausChannel_range_eq_support B hS]
  exact LinearMap.mem_range_self _ x

/-- Orthogonal compression onto the constructed support; it is defined for every input. -/
noncomputable def krausSupportOperator (B : ι → Matrix n n ℂ) (S : Matrix n n ℂ) :
    krausSupport B →L[ℂ] krausSupport B :=
  (krausSupport B).orthogonalProjection ∘L
    Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S) ∘L
      (krausSupport B).subtypeL

/-- On faithful inputs the compression is exactly the restricted source action. -/
theorem krausSupportOperator_coe_apply (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) (x : krausSupport B) :
    (krausSupportOperator B S x : EuclideanSpace ℂ n) =
      Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S) (x : EuclideanSpace ℂ n) := by
  change (krausSupport B).starProjection
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S) x) = _
  exact Submodule.starProjection_eq_self_iff.mpr (krausChannel_apply_mem_support B hS x)

/-- The compressed source is positive on the actual support Hilbert space. -/
theorem krausSupportOperator_isPositive (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) : (krausSupportOperator B S).IsPositive := by
  have h : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S)).IsPositive := by
    apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
    exact Matrix.isPositive_toEuclideanLin_iff.mpr (krausChannel_posSemidef B hS)
  exact h.orthogonalProjection_comp (krausSupport B)

/-- The source restricted to its fixed range has no remaining kernel. -/
theorem krausSupportOperator_injective (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) : Function.Injective (krausSupportOperator B S) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  apply Subtype.ext
  have hzero : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S)
      (x : EuclideanSpace ℂ n) = 0 := by
    rw [← krausSupportOperator_coe_apply B hS x]
    exact congrArg Subtype.val hx
  have hker : (x : EuclideanSpace ℂ n) ∈ (krausSupport B)ᗮ := by
    rw [← krausChannel_ker_eq_support_orthogonal B hS]
    exact hzero
  have hz : (x : EuclideanSpace ℂ n) ∈ krausSupport B ⊓ (krausSupport B)ᗮ := ⟨x.property, hker⟩
  rw [(krausSupport B).inf_orthogonal_eq_bot] at hz
  exact (Submodule.mem_bot ℂ).mp hz

/-- An orthonormal coordinate system chosen once for this fixed output support. -/
noncomputable def krausSupportBasis (B : ι → Matrix n n ℂ) :
    OrthonormalBasis (Fin (Module.finrank ℂ (krausSupport B))) ℂ (krausSupport B) :=
  stdOrthonormalBasis ℂ (krausSupport B)

/-- The concrete compressed source matrix in the fixed support basis. -/
noncomputable def krausCompressedSource (B : ι → Matrix n n ℂ) (S : Matrix n n ℂ) :
    Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ :=
  (krausSupportOperator B S).toLinearMap.toMatrix
    (krausSupportBasis B).toBasis (krausSupportBasis B).toBasis

theorem krausCompressedSource_posSemidef (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) : (krausCompressedSource B S).PosSemidef := by
  exact (LinearMap.posSemidef_toMatrix_iff (krausSupportBasis B)).mpr
    (krausSupportOperator_isPositive B hS).toLinearMap

/-- Compression removes precisely the forced source kernel. The zero-dimensional case
is included: positivity there is vacuous, with no fictitious nonzero support assumed. -/
theorem krausCompressedSource_posDef (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) : (krausCompressedSource B S).PosDef := by
  apply (krausCompressedSource_posSemidef B hS.posSemidef).posDef_iff_isUnit.mpr
  apply (LinearMap.isUnit_toMatrix_iff (v₁ := (krausSupportBasis B).toBasis)).mpr
  exact (LinearMap.isUnit_iff_ker_eq_bot _).mpr
    (LinearMap.ker_eq_bot.mpr (krausSupportOperator_injective B hS))

/-- The support projection fixes every source output. -/
theorem krausChannel_starProjection_left (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    (krausSupport B).starProjection ∘L
      Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S) =
        Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S) := by
  apply ContinuousLinearMap.ext
  intro x
  exact Submodule.starProjection_eq_self_iff.mpr (krausChannel_apply_mem_support B hS x)

/-- The source vanishes on the orthogonal complement of the constructed support. -/
theorem krausChannel_starProjection_right (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S) ∘L
      (krausSupport B).starProjection =
        Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S) := by
  apply ContinuousLinearMap.ext
  intro x
  have hx := (krausSupport B).sub_starProjection_mem_orthogonal x
  rw [← krausChannel_ker_eq_support_orthogonal B hS] at hx
  change Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S)
    (x - (krausSupport B).starProjection x) = 0 at hx
  rw [map_sub] at hx
  exact (sub_eq_zero.mp hx).symm

/-- Extending the compressed operator by zero exactly recovers the original source. -/
theorem krausSupportOperator_reconstruct (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    (krausSupport B).subtypeL ∘L krausSupportOperator B S ∘L
      (krausSupport B).orthogonalProjection =
        Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (krausChannel B S) := by
  apply ContinuousLinearMap.ext
  intro x
  change (krausSupportOperator B S ((krausSupport B).orthogonalProjection x) :
    EuclideanSpace ℂ n) = _
  rw [krausSupportOperator_coe_apply B hS]
  exact congrArg (fun T : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n => T x)
    (krausChannel_starProjection_right B hS)

/-- Zero fixed support means the full physical source is zero. -/
theorem krausChannel_eq_zero_of_support_eq_bot (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) (hzero : krausSupport B = ⊥) :
    krausChannel B S = 0 := by
  apply (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).injective
  rw [map_zero]
  have h := krausChannel_starProjection_left B hS
  rw [hzero, Submodule.starProjection_bot, ContinuousLinearMap.zero_comp] at h
  exact h.symm

end MatrixSpencer
