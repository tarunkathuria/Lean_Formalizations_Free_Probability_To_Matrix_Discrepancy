import MatrixSpencer.CovarianceFaceDomination
import MatrixSpencer.CovarianceCompactChart

/-!
# A fixed coordinate frame for each coefficient support subspace

The frame is chosen from the subspace alone using `stdOrthonormalBasis`.
It does not use a current covariance's eigenvectors. Thus the chosen frame
and its coordinate type stay literally unchanged while the support stays fixed.
-/

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace MatrixSpencer
namespace CoefficientSupportFrame

variable {ι : Type*} [Fintype ι]

abbrev FrameIndex (K : Submodule ℝ (EuclideanSpace ℝ ι)) := Fin (Module.finrank ℝ K)

def frame (K : Submodule ℝ (EuclideanSpace ℝ ι)) : Matrix ι (FrameIndex K) ℝ :=
  fun i a => (stdOrthonormalBasis ℝ K a : EuclideanSpace ℝ ι) i

def frameIsometry (K : Submodule ℝ (EuclideanSpace ℝ ι)) :
    EuclideanSpace ℝ (FrameIndex K) →ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  K.subtypeₗᵢ.comp (stdOrthonormalBasis ℝ K).repr.symm.toLinearIsometry

/-- Rectangular continuous Euclidean realization of the frame matrix. -/
def frameCLM (K : Submodule ℝ (EuclideanSpace ℝ ι)) :
    EuclideanSpace ℝ (FrameIndex K) →L[ℝ] EuclideanSpace ℝ ι :=
  (Matrix.toEuclideanLin (frame K)).toContinuousLinearMap

lemma frame_isometry (K : Submodule ℝ (EuclideanSpace ℝ ι)) :
    (frame K)ᵀ * frame K = 1 := by
  ext a b
  have h := (stdOrthonormalBasis ℝ K).inner_eq_ite b a
  simpa only [frame, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
    Submodule.coe_inner, PiLp.inner_apply, RCLike.inner_apply, star_trivial, eq_comm] using h

lemma frameCLM_eq_isometry (K : Submodule ℝ (EuclideanSpace ℝ ι)) :
    frameCLM K = (frameIsometry K).toContinuousLinearMap := by
  ext v i
  change (frame K *ᵥ WithLp.ofLp v) i =
    ((stdOrthonormalBasis ℝ K).repr.symm v : EuclideanSpace ℝ ι) i
  rw [← (stdOrthonormalBasis ℝ K).sum_repr_symm v]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  change (frame K *ᵥ WithLp.ofLp v) i =
    (PiLp.projₗ (𝕜 := ℝ) (β := fun _ : ι => ℝ) 2 i)
      (∑ a, v a • (stdOrthonormalBasis ℝ K a : EuclideanSpace ℝ ι))
  rw [map_sum]
  simp [frame, Matrix.mulVec, dotProduct, mul_comm]

lemma frameCLM_mem (K : Submodule ℝ (EuclideanSpace ℝ ι))
    (v : EuclideanSpace ℝ (FrameIndex K)) : frameCLM K v ∈ K := by
  rw [frameCLM_eq_isometry]
  exact ((stdOrthonormalBasis ℝ K).repr.symm v).property

lemma frameCLM_range (K : Submodule ℝ (EuclideanSpace ℝ ι)) :
    LinearMap.range (frameCLM K).toLinearMap = K := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact frameCLM_mem K v
  · intro u hu
    refine ⟨(stdOrthonormalBasis ℝ K).repr ⟨u, hu⟩, ?_⟩
    rw [frameCLM_eq_isometry]
    change (((stdOrthonormalBasis ℝ K).repr.symm
      ((stdOrthonormalBasis ℝ K).repr ⟨u, hu⟩) : K) : EuclideanSpace ℝ ι) = u
    simp

lemma frameCLM_norm (K : Submodule ℝ (EuclideanSpace ℝ ι))
    (v : EuclideanSpace ℝ (FrameIndex K)) : ‖frameCLM K v‖ = ‖v‖ := by
  rw [frameCLM_eq_isometry]
  exact (frameIsometry K).norm_map v

lemma frameCLM_ofLp (K : Submodule ℝ (EuclideanSpace ℝ ι))
    (v : EuclideanSpace ℝ (FrameIndex K)) :
    WithLp.ofLp (frameCLM K v) = frame K *ᵥ WithLp.ofLp v := rfl

/-- Compression in the fixed frame of the given support. -/
def reduced (K : Submodule ℝ (EuclideanSpace ℝ ι)) (C : Matrix ι ι ℝ) :
    Matrix (FrameIndex K) (FrameIndex K) ℝ := (frame K)ᵀ * C * frame K

lemma reduced_posSemidef (K : Submodule ℝ (EuclideanSpace ℝ ι))
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) : (reduced K C).PosSemidef :=
  covarianceFace_compress_posSemidef (frame K) hC

lemma reduced_hermitian (K : Submodule ℝ (EuclideanSpace ℝ ι))
    {C : Matrix ι ι ℝ} (hC : C.IsHermitian) : (reduced K C).IsHermitian := by
  simpa only [reduced, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_conjTranspose_mul_mul (frame K) hC

lemma reduced_mono (K : Submodule ℝ (EuclideanSpace ℝ ι))
    {C D : Matrix ι ι ℝ} (hCD : C ≤ D) : reduced K C ≤ reduced K D := by
  simpa only [reduced, covarianceLift, Matrix.transpose_transpose] using
    covarianceLift_mono (frame K)ᵀ hCD

variable [DecidableEq ι]

lemma reduced_one (K : Submodule ℝ (EuclideanSpace ℝ ι)) :
    reduced K (1 : Matrix ι ι ℝ) = 1 := by
  simp only [reduced, Matrix.mul_one, frame_isometry]

lemma reduced_le_one (K : Submodule ℝ (EuclideanSpace ℝ ι))
    {C : Matrix ι ι ℝ} (hC : C ≤ 1) : reduced K C ≤ 1 := by
  simpa only [reduced_one] using reduced_mono K hC

omit [DecidableEq ι] in
lemma projection_mulVec_of_mem (K : Submodule ℝ (EuclideanSpace ℝ ι))
    {u : EuclideanSpace ℝ ι} (hu : u ∈ K) :
    (frame K * (frame K)ᵀ) *ᵥ WithLp.ofLp u = WithLp.ofLp u := by
  have hu' : u ∈ LinearMap.range (frameCLM K).toLinearMap := by rwa [frameCLM_range]
  obtain ⟨v, rfl⟩ := hu'
  change (frame K * (frame K)ᵀ) *ᵥ WithLp.ofLp (frameCLM K v) = WithLp.ofLp (frameCLM K v)
  rw [frameCLM_ofLp, Matrix.mulVec_mulVec, Matrix.mul_assoc, frame_isometry, Matrix.mul_one]

lemma projection_mul_of_range (K : Submodule ℝ (EuclideanSpace ℝ ι)) {C : Matrix ι ι ℝ}
    (hRange : LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap ≤ K) :
    (frame K * (frame K)ᵀ) * C = C := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec]
  apply projection_mulVec_of_mem K
  apply hRange
  exact ⟨WithLp.toLp 2 (Pi.single j 1), rfl⟩

/-- Every Hermitian matrix whose actual range lies in the support is reconstructed exactly. -/
lemma reconstruct_of_range (K : Submodule ℝ (EuclideanSpace ℝ ι))
    {C : Matrix ι ι ℝ} (hC : C.IsHermitian)
    (hRange : LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap ≤ K) :
    covarianceLift (frame K) (reduced K C) = C := by
  have hleft := projection_mul_of_range K hRange
  have hCt : Cᵀ = C := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hC.eq
  have hright : C * (frame K * (frame K)ᵀ) = C := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hCt] using
      congrArg Matrix.transpose hleft
  calc
    _ = (frame K * (frame K)ᵀ) * C * (frame K * (frame K)ᵀ) := by
      simp only [covarianceLift, reduced, Matrix.mul_assoc]
    _ = C := by rw [hleft, hright]

omit [DecidableEq ι] in
lemma reduced_quadratic (K : Submodule ℝ (EuclideanSpace ℝ ι)) (C : Matrix ι ι ℝ)
    (x : FrameIndex K → ℝ) :
    x ⬝ᵥ (reduced K C *ᵥ x) = (frame K *ᵥ x) ⬝ᵥ (C *ᵥ (frame K *ᵥ x)) := by
  simp only [reduced, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma reduced_inner (K : Submodule ℝ (EuclideanSpace ℝ ι)) (C : Matrix ι ι ℝ)
    (v : EuclideanSpace ℝ (FrameIndex K)) :
    inner ℝ v (Matrix.toEuclideanCLM (n := FrameIndex K) (𝕜 := ℝ) (reduced K C) v) =
      inner ℝ (frameCLM K v) (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C (frameCLM K v)) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, Matrix.ofLp_toEuclideanCLM,
    frameCLM_ofLp]
  rw [dotProduct_comm (reduced K C *ᵥ WithLp.ofLp v),
    dotProduct_comm (C *ᵥ (frame K *ᵥ WithLp.ofLp v)), reduced_quadratic]

/-- A Euclidean quadratic floor on the actual fixed support becomes a matrix floor in coordinates. -/
lemma reduced_floor_of_quadratic (K : Submodule ℝ (EuclideanSpace ℝ ι))
    {C : Matrix ι ι ℝ} (hC : C.IsHermitian) {δ : ℝ}
    (hfloor : ∀ u ∈ K,
      δ * ‖u‖ ^ 2 ≤ inner ℝ u (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C u)) :
    δ • (1 : Matrix (FrameIndex K) (FrameIndex K) ℝ) ≤ reduced K C := by
  apply Matrix.le_iff.mpr
  refine ⟨(reduced_hermitian K hC).sub ?_, fun x => ?_⟩
  · exact IsSelfAdjoint.smul (show IsSelfAdjoint δ from rfl) Matrix.isHermitian_one
  · have h := hfloor (frameCLM K (WithLp.toLp 2 x)) (frameCLM_mem K _)
    rw [frameCLM_norm, ← reduced_inner] at h
    have hnorm : ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
        (real_inner_self_eq_norm_sq (WithLp.toLp 2 x : EuclideanSpace ℝ (FrameIndex K))).symm
    rw [hnorm] at h
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      Matrix.ofLp_toEuclideanCLM] at h
    change δ * (x ⬝ᵥ x) ≤ (reduced K C *ᵥ x) ⬝ᵥ x at h
    rw [dotProduct_comm (reduced K C *ᵥ x) x] at h
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul]
    exact sub_nonneg.mpr h

lemma projectionMatrix_mulVec_of_mem (K : Submodule ℝ (EuclideanSpace ℝ ι))
    {u : EuclideanSpace ℝ ι} (hu : u ∈ K) :
    euclideanProjectionMatrix K *ᵥ WithLp.ofLp u = WithLp.ofLp u := by
  have h : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (euclideanProjectionMatrix K) u = u := by
    rw [toEuclideanCLM_projectionMatrix]
    exact K.starProjection_eq_self_iff.mpr hu
  exact congrArg WithLp.ofLp h

lemma projectionMatrix_mul_frame (K : Submodule ℝ (EuclideanSpace ℝ ι)) :
    euclideanProjectionMatrix K * frame K = frame K := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec]
  exact projectionMatrix_mulVec_of_mem K (frameCLM_mem K (WithLp.toLp 2 (Pi.single j 1)))

lemma reduced_projection (K : Submodule ℝ (EuclideanSpace ℝ ι)) :
    reduced K (euclideanProjectionMatrix K) = 1 := by
  rw [reduced, Matrix.mul_assoc, projectionMatrix_mul_frame, frame_isometry]

omit [DecidableEq ι] in
lemma reduced_smul (K : Submodule ℝ (EuclideanSpace ℝ ι)) (a : ℝ) (C : Matrix ι ι ℝ) :
    reduced K (a • C) = a • reduced K C := by
  simp only [reduced, Matrix.mul_smul, Matrix.smul_mul]

lemma reduced_floor (K : Submodule ℝ (EuclideanSpace ℝ ι))
    {C : Matrix ι ι ℝ} {δ : ℝ} (hfloor : δ • euclideanProjectionMatrix K ≤ C) :
    δ • (1 : Matrix (FrameIndex K) (FrameIndex K) ℝ) ≤ reduced K C := by
  simpa only [reduced_smul, reduced_projection] using reduced_mono K hfloor

lemma reduced_posDef_of_floor (K : Submodule ℝ (EuclideanSpace ℝ ι))
    {C : Matrix ι ι ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hfloor : δ • euclideanProjectionMatrix K ≤ C) : (reduced K C).PosDef :=
  CovarianceCompactChart.posDef_of_scalar_floor hδ (reduced_floor K hfloor)

lemma reduced_posDef_of_quadratic_floor (K : Submodule ℝ (EuclideanSpace ℝ ι))
    {C : Matrix ι ι ℝ} (hC : C.IsHermitian) {δ : ℝ} (hδ : 0 < δ)
    (hfloor : ∀ u ∈ K,
      δ * ‖u‖ ^ 2 ≤ inner ℝ u (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C u)) :
    (reduced K C).PosDef :=
  CovarianceCompactChart.posDef_of_scalar_floor hδ (reduced_floor_of_quadratic K hC hfloor)

omit [DecidableEq ι] in
/-- A PSD covariance is strictly positive on nonzero vectors of its actual range. -/
lemma positive_on_range {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {y : ι → ℝ}
    (hy : y ∈ LinearMap.range C.mulVecLin) (hne : y ≠ 0) :
    0 < y ⬝ᵥ (C *ᵥ y) := by
  have hn : 0 ≤ y ⬝ᵥ (C *ᵥ y) := by simpa only [star_trivial] using hC.2 y
  by_contra hnot
  have hq : y ⬝ᵥ (C *ᵥ y) = 0 := le_antisymm (le_of_not_gt hnot) hn
  have hzero : C *ᵥ y = 0 :=
    (hC.dotProduct_mulVec_zero_iff y).mp (by simpa only [star_trivial] using hq)
  obtain ⟨v, hv⟩ := hy
  have hCt : Cᵀ = C := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hC.isHermitian.eq
  have hvec : y ᵥ* C = 0 := by rw [← hCt, Matrix.vecMul_transpose, hzero]
  have hyy : y ⬝ᵥ y = 0 := by
    calc
      _ = y ⬝ᵥ (C *ᵥ v) := by rw [show C *ᵥ v = y from hv]
      _ = (y ᵥ* C) ⬝ᵥ v := Matrix.dotProduct_mulVec _ _ _
      _ = 0 := by rw [hvec, zero_dotProduct]
  have hp : 0 < y ⬝ᵥ y := by simpa only [star_trivial] using
    (dotProduct_star_self_pos_iff.mpr hne)
  rw [hyy] at hp
  exact lt_irrefl 0 hp

/-- Exact support gives a positive definite reduced covariance without assuming a floor. -/
lemma reduced_posDef_of_range (K : Submodule ℝ (EuclideanSpace ℝ ι))
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (hRange : LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap = K) :
    (reduced K C).PosDef := by
  refine ⟨reduced_hermitian K hC.isHermitian, fun x hx => ?_⟩
  simp only [star_trivial, reduced_quadratic]
  have hyK := frameCLM_mem K (WithLp.toLp 2 x)
  have hyR : frameCLM K (WithLp.toLp 2 x) ∈
      LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap := by
    rwa [hRange]
  have hy : frame K *ᵥ x ∈ LinearMap.range C.mulVecLin := by
    obtain ⟨v, hv⟩ := hyR
    exact ⟨WithLp.ofLp v, congrArg WithLp.ofLp hv⟩
  apply positive_on_range hC hy
  intro hz
  apply hx
  apply covarianceIsometry_mulVec_injective (frame K) (frame_isometry K)
  simpa only [Matrix.mulVec_zero] using hz

end CoefficientSupportFrame
end MatrixSpencer
