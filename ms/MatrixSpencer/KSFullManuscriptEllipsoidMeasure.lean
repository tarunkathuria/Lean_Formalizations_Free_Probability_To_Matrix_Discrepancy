import MatrixSpencer.KSFullManuscriptEllipsoidRun
import MatrixSpencer.KSFullManuscriptEllipsoidVolume
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Affine ellipsoid measure and actual central-cut contraction

This connects the computed affine factors to ordinary Haar/Lebesgue volume.
The normalized determinant factor is proved from its actual coordinate
matrix, rather than supplied as an assumption about the update.
-/

open Matrix Set MeasureTheory
open scoped BigOperators InnerProductSpace ENNReal
noncomputable section
namespace MatrixSpencer.KSFullManuscriptEllipsoidMeasure

open KSFullManuscriptEllipsoidAffine KSFullManuscriptEllipsoidFactor
variable {ℓ : ℕ}
abbrev Space (ℓ : ℕ) := EuclideanSpace ℝ (Fin ℓ)

def axialMatrix (p q : ℝ) (a : Space ℓ) : Matrix (Fin ℓ) (Fin ℓ) ℝ :=
  p • 1 + (q - p) • (Matrix.replicateCol Unit (fun i => a i) *
    Matrix.replicateRow Unit (fun i => a i))

theorem toMatrix_factorCLM (r : ℝ) (a : Space ℓ) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin ℓ) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin ℓ) ℝ).toBasis (factorCLM r a).toLinearMap =
      axialMatrix (transverse r) (axial r) a := by
  ext i j
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, factorCLM_apply, factor, axialMap,
    EuclideanSpace.inner_single_right, axialMatrix, Matrix.mul_apply,
    Matrix.replicateCol_apply, Matrix.replicateRow_apply, Matrix.one_apply,
    EuclideanSpace.single_apply, eq_comm]
  ring

theorem axialMatrix_det (p q : ℝ) (hp : p ≠ 0) (a : Space ℓ) (ha : ‖a‖ = 1) :
    (axialMatrix p q a).det = p ^ ℓ * (q / p) := by
  have hs : ∑ i, a i ^ 2 = 1 := by
    have hh := EuclideanSpace.norm_sq_eq a
    simpa only [ha, one_pow, Real.norm_eq_abs, sq_abs] using hh.symm
  have hid : axialMatrix p q a = p • (1 +
      Matrix.replicateCol Unit (fun i => (q / p - 1) * a i) *
        Matrix.replicateRow Unit (fun i => a i)) := by
    ext i j
    simp [axialMatrix, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply]
    field_simp
  have hd : (fun i => a i) ⬝ᵥ (fun i => (q / p - 1) * a i) = q / p - 1 := by
    unfold dotProduct
    calc
      _ = ∑ i, (q / p - 1) * (a i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [← Finset.mul_sum, hs, mul_one]
  rw [hid, Matrix.det_smul, Fintype.card_fin,
    Matrix.det_one_add_replicateCol_mul_replicateRow, hd]
  ring

theorem factor_det (hℓ : 1 < ℓ) (a : Space ℓ) (ha : ‖a‖ = 1) :
    LinearMap.det (factorCLM (ℓ : ℝ) a).toLinearMap =
      transverse (ℓ : ℝ) ^ (ℓ - 1) * axial (ℓ : ℝ) := by
  have hr : (1 : ℝ) < ℓ := by exact_mod_cast hℓ
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin ℓ) ℝ).toBasis,
    toMatrix_factorCLM, axialMatrix_det _ _ (ne_of_gt (transverse_pos hr)) a ha]
  have he : ℓ = (ℓ - 1) + 1 := by omega
  conv_lhs => arg 1; rw [he, pow_succ]
  rw [← he]
  field_simp [ne_of_gt (transverse_pos hr)]

theorem factor_det_eq_sqrt_shape_det (hℓ : 1 < ℓ) (a : Space ℓ) (ha : ‖a‖ = 1) :
    LinearMap.det (factorCLM (ℓ : ℝ) a).toLinearMap =
      Real.sqrt (KSFullManuscriptEllipsoidVolume.shapeMatrix a).det := by
  have hr : (1 : ℝ) < ℓ := by exact_mod_cast hℓ
  have ht := transverse_pos hr
  have ha' := axial_pos hr
  rw [factor_det hℓ a ha]
  symm
  apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (mul_pos (pow_pos ht _) ha')).mpr
  rw [KSFullManuscriptEllipsoidVolume.shapeMatrix_det_axes hℓ a ha]
  have hp : transverse (ℓ : ℝ) ^ 2 = KSFullManuscriptEllipsoidVolume.transverseScale ℓ := by
    apply Real.sq_sqrt
    exact (KSFullManuscriptEllipsoidVolume.transverseScale_pos hℓ).le
  rw [← sq, mul_pow, ← pow_mul, mul_comm (ℓ - 1) 2, pow_mul, hp]
  rfl

theorem body_volume (s : State (Space ℓ)) :
    volume (body s) = ENNReal.ofReal |LinearMap.det s.factor.toLinearMap| *
      volume (Metric.closedBall (0 : Space ℓ) 1) := by
  have he : body s = (fun y => s.center + y) ''
      (s.factor '' Metric.closedBall (0 : Space ℓ) 1) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨s.factor z, ⟨z, by simpa using hz, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, by simpa using hz, rfl⟩
  rw [he, image_add_left, measure_preimage_add,
    Measure.addHaar_image_continuousLinearMap]

theorem update_volume (r : ℝ) (s : State (Space ℓ)) (g : Space ℓ) :
    volume (body (update r s g)) =
      ENNReal.ofReal |LinearMap.det (factorCLM r (cutNormal s g)).toLinearMap| * volume (body s) := by
  rw [body_volume, body_volume]
  change ENNReal.ofReal |LinearMap.det
    (s.factor.toLinearMap.comp (factorCLM r (cutNormal s g)).toLinearMap)| * _ = _
  rw [LinearMap.det_comp, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  ac_rfl


theorem update_volume_le (hℓ : 1 < ℓ) (s : State (Space ℓ))
    (hs : Function.Surjective s.factor) {g : Space ℓ} (hg : g ≠ 0) :
    volume (body (update (ℓ : ℝ) s g)) ≤
      ENNReal.ofReal (Real.exp (-1 / (2 * ((ℓ : ℝ) + 1)))) * volume (body s) := by
  have ha := cutNormal_norm s (cutVector_ne_zero s hs hg)
  rw [update_volume, factor_det_eq_sqrt_shape_det hℓ _ ha,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal
    (KSFullManuscriptEllipsoidVolume.sqrt_det_le_exp hℓ _ ha)) _

end MatrixSpencer.KSFullManuscriptEllipsoidMeasure
