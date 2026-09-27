import SimpleMS.LegalSpace
import MatrixSpencer.MSManuscriptNumericalEpochShort
import MatrixSpencer.SupportShaving

/-! The canonical movement projection is computed by scalar shorting of
the high spectral projection. This connects the geometric definition to
the already counted, finite constraint scan. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace SimpleMS.ProjectionComputation
open MatrixSpencer MSManuscriptNumericalEpochShort
variable {N : ℕ}

lemma projection_mul_of_range (W : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    {B : Matrix (Fin N) (Fin N) ℝ}
    (hB : LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) B).toLinearMap ≤ W) :
    euclideanProjectionMatrix W * B = B := by
  apply (Matrix.toEuclideanCLM (𝕜 := ℝ)).injective
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanProjectionMatrix W * B) =
    Matrix.toEuclideanCLM (𝕜 := ℝ) B
  rw [map_mul]
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanProjectionMatrix W) *
    Matrix.toEuclideanCLM (𝕜 := ℝ) B = Matrix.toEuclideanCLM (𝕜 := ℝ) B
  rw [toEuclideanCLM_projectionMatrix]
  apply ContinuousLinearMap.ext
  intro x
  exact W.starProjection_eq_self_iff.mpr (hB ⟨x,rfl⟩)

lemma contraction_le_projection {B : Matrix (Fin N) (Fin N) ℝ}
    (hB : B.IsHermitian) (hB1 : B ≤ 1)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (hRange : LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) B).toLinearMap ≤ W) :
    B ≤ euclideanProjectionMatrix W := by
  let P := euclideanProjectionMatrix W
  have hP := euclideanProjectionMatrix_isStarProjection W
  have hPc : Pᴴ = P := (euclideanProjectionMatrix_posSemidef W).isHermitian.eq
  have hPid : P * P = P := hP.isIdempotentElem.eq
  have hleft : P * B = B := projection_mul_of_range W hRange
  have hright : B * P = B := by
    simpa only [Matrix.conjTranspose_mul,hB.eq,hPc] using
      congrArg Matrix.conjTranspose hleft
  have hp := (Matrix.le_iff.mp hB1).mul_mul_conjTranspose_same P
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub,Matrix.mul_one,Matrix.sub_mul,
    hPc,hPid,hleft,hright] using hp

lemma projection_annihilates_orthogonal
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (u : EuclideanSpace ℝ (Fin N)) (hu : u ∈ Wᗮ) :
    euclideanProjectionMatrix W *ᵥ WithLp.ofLp u = 0 := by
  have h : W.starProjection u = 0 := (W.starProjection_apply_eq_zero_iff).mpr hu
  rw [← toEuclideanCLM_projectionMatrix] at h
  exact congrArg WithLp.ofLp h

lemma projection_legal_frozen (W : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hW : W ≤ legalSpace F x) (i : Fin N) (hi : i ∈ F) :
    euclideanProjectionMatrix W *ᵥ Pi.single i 1 = 0 := by
  apply projection_annihilates_orthogonal W (EuclideanSpace.single i 1)
  rw [Submodule.mem_orthogonal']
  intro u hu
  simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using
    ((mem_legalSpace F x u).mp (hW hu)).1 i hi

lemma projection_legal_radial (W : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hW : W ≤ legalSpace F x) :
    euclideanProjectionMatrix W *ᵥ WithLp.ofLp x = 0 := by
  apply projection_annihilates_orthogonal W x
  rw [Submodule.mem_orthogonal']
  intro u hu
  exact ((mem_legalSpace F x u).mp (hW hu)).2

lemma range_legal_of_annihilators {B : Matrix (Fin N) (Fin N) ℝ}
    (hB : B.IsHermitian) (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hF : ∀ i ∈ F, B *ᵥ Pi.single i 1 = 0)
    (hx : B *ᵥ WithLp.ofLp x = 0) :
    LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) B).toLinearMap ≤ legalSpace F x := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) B
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (IsSelfAdjoint.map (show IsSelfAdjoint B from hB)
      (Matrix.toEuclideanCLM (𝕜 := ℝ)))
  have hLx : L x = 0 := by
    apply (WithLp.equiv 2 (Fin N → ℝ)).injective
    exact hx
  rintro _ ⟨y,rfl⟩
  apply (mem_legalSpace F x _).mpr
  constructor
  · intro i hi
    have he : L (EuclideanSpace.single i 1) = 0 := by
      apply (WithLp.equiv 2 (Fin N → ℝ)).injective
      exact hF i hi
    have h := hs (EuclideanSpace.single i 1) y
    change inner ℝ (L (EuclideanSpace.single i 1)) y =
      inner ℝ (EuclideanSpace.single i 1) (L y) at h
    simpa only [he,inner_zero_left,EuclideanSpace.inner_single_left,
      map_one,one_mul] using h.symm
  · have h := hs x y
    change inner ℝ (L x) y = inner ℝ x (L y) at h
    simpa only [hLx,inner_zero_left] using h.symm

theorem projection_eq_epoch_high (C : Matrix (Fin N) (Fin N) ℝ)
    (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    euclideanProjectionMatrix (movementSpace C (legalSpace F x)) =
      epoch (highProjection C) F x := by
  let P := highProjection C
  let W := movementSpace C (legalSpace F x)
  have hP : IsStarProjection P := by
    by_cases hC : C.IsHermitian
    · exact highProjection_isStarProjection C hC
    · simp [P,highProjection,hC,isStarProjection_iff']
  have hEP := epoch_posSemidef P hP.nonneg.posSemidef F x
  have hE_le := epoch_le P hP.nonneg.posSemidef F x
  apply le_antisymm
  · apply epoch_maximal P (euclideanProjectionMatrix W) hP.nonneg.posSemidef
      (euclideanProjectionMatrix_posSemidef W)
      (projectionMatrix_le_of_range hP W inf_le_left)
    · exact projection_legal_frozen W F x inf_le_right
    · exact projection_legal_radial W F x inf_le_right
  · apply contraction_le_projection hEP.isHermitian (hE_le.trans hP.le_one) W
    apply le_inf
    · exact posSemidef_range_le_of_le hEP hP.nonneg.posSemidef hE_le
    · exact range_legal_of_annihilators hEP.isHermitian F x
        (epoch_frozen P hP.nonneg.posSemidef F x)
        (epoch_radial P hP.nonneg.posSemidef F x)

theorem flatCovariance_eq_half_epoch_high (C : Matrix (Fin N) (Fin N) ℝ)
    (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    flatCovariance C (legalSpace F x) = (1/2 : ℝ) • epoch (highProjection C) F x := by
  rw [flatCovariance,projection_eq_epoch_high C]

end SimpleMS.ProjectionComputation
