import MatrixSpencer.KSFullManuscriptEllipsoid
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exact determinant and contraction of the central-cut shape

The normalized shape matrix is the concrete rank-one update in Part II.5.
Its determinant and square-root determinant satisfy the stated exponential
contraction. This is determinant accounting; a finite feasibility procedure
and its maintained containment invariant are separate remaining work.
-/

open Matrix
open scoped BigOperators InnerProductSpace
noncomputable section
namespace MatrixSpencer.KSFullManuscriptEllipsoidVolume

variable {ℓ : ℕ}

def transverseScale (ℓ : ℕ) : ℝ := (ℓ : ℝ) ^ 2 / ((ℓ : ℝ) ^ 2 - 1)
def axialScale (ℓ : ℕ) : ℝ := (ℓ : ℝ) / ((ℓ : ℝ) + 1)

def shapeMatrix (a : EuclideanSpace ℝ (Fin ℓ)) : Matrix (Fin ℓ) (Fin ℓ) ℝ :=
  transverseScale ℓ • (1 +
    Matrix.replicateCol Unit (fun i => -(2 / ((ℓ : ℝ) + 1)) * a i) *
      Matrix.replicateRow Unit (fun i => a i))

theorem shapeMatrix_det (a : EuclideanSpace ℝ (Fin ℓ)) (ha : ‖a‖ = 1) :
    (shapeMatrix a).det = transverseScale ℓ ^ ℓ * (((ℓ : ℝ) - 1) / ((ℓ : ℝ) + 1)) := by
  have hs : ∑ i, a i ^ 2 = 1 := by
    have hh := EuclideanSpace.norm_sq_eq a
    simpa only [ha, one_pow, Real.norm_eq_abs, sq_abs] using hh.symm
  have hd : (fun i => a i) ⬝ᵥ (fun i => -(2 / ((ℓ : ℝ) + 1)) * a i) =
      -(2 / ((ℓ : ℝ) + 1)) := by
    unfold dotProduct
    calc
      _ = ∑ i, -(2 / ((ℓ : ℝ) + 1)) * (a i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [← Finset.mul_sum, hs, mul_one]
  rw [shapeMatrix, Matrix.det_smul, Fintype.card_fin,
    Matrix.det_one_add_replicateCol_mul_replicateRow, hd]
  congr 1
  have hp : (ℓ : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem transverseScale_pos (hℓ : 1 < ℓ) : 0 < transverseScale ℓ := by
  have hr : (1 : ℝ) < ℓ := by exact_mod_cast hℓ
  exact div_pos (by positivity) (by nlinarith)

theorem axialScale_pos (hℓ : 1 < ℓ) : 0 < axialScale ℓ := by
  have hr : (0 : ℝ) < ℓ := Nat.cast_pos.mpr (by omega)
  exact div_pos hr (by positivity)

theorem shapeMatrix_det_axes (hℓ : 1 < ℓ)
    (a : EuclideanSpace ℝ (Fin ℓ)) (ha : ‖a‖ = 1) :
    (shapeMatrix a).det = transverseScale ℓ ^ (ℓ - 1) * axialScale ℓ ^ 2 := by
  have hr : (1 : ℝ) < ℓ := by exact_mod_cast hℓ
  have he : ℓ = (ℓ - 1) + 1 := by omega
  rw [shapeMatrix_det a ha]
  conv_lhs => arg 1; rw [he, pow_succ]
  rw [← he]
  have hid : transverseScale ℓ * (((ℓ : ℝ) - 1) / ((ℓ : ℝ) + 1)) = axialScale ℓ ^ 2 := by
    unfold transverseScale axialScale
    have hm : (ℓ : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have hp : (ℓ : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [mul_assoc, hid]

theorem log_shapeMatrix_det_le (hℓ : 1 < ℓ)
    (a : EuclideanSpace ℝ (Fin ℓ)) (ha : ‖a‖ = 1) :
    Real.log (shapeMatrix a).det ≤ -1 / ((ℓ : ℝ) + 1) := by
  have hr : (1 : ℝ) < ℓ := by exact_mod_cast hℓ
  have ht := transverseScale_pos hℓ
  have hx := axialScale_pos hℓ
  have hc : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]
  rw [shapeMatrix_det_axes hℓ a ha,
    Real.log_mul (ne_of_gt (pow_pos ht _)) (ne_of_gt (sq_pos_of_pos hx)),
    Real.log_pow, Real.log_pow, hc]
  have hu := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos ht)
    (show 0 ≤ (ℓ : ℝ) - 1 by linarith)
  have hv := Real.log_le_sub_one_of_pos hx
  have hid : ((ℓ : ℝ) - 1) * (transverseScale ℓ - 1) +
      2 * (axialScale ℓ - 1) = -1 / ((ℓ : ℝ) + 1) := by
    unfold transverseScale axialScale
    have hm : (ℓ : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have hp : (ℓ : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  nlinarith


theorem sqrt_det_le_exp (hℓ : 1 < ℓ)
    (a : EuclideanSpace ℝ (Fin ℓ)) (ha : ‖a‖ = 1) :
    Real.sqrt (shapeMatrix a).det ≤ Real.exp (-1 / (2 * ((ℓ : ℝ) + 1))) := by
  have hp : 0 < (shapeMatrix a).det := by
    rw [shapeMatrix_det_axes hℓ a ha]
    exact mul_pos (pow_pos (transverseScale_pos hℓ) _) (sq_pos_of_pos (axialScale_pos hℓ))
  apply (Real.log_le_iff_le_exp (Real.sqrt_pos.mpr hp)).mp
  rw [Real.log_sqrt hp.le]
  have h := log_shapeMatrix_det_le hℓ a ha
  calc
    _ ≤ (-1 / ((ℓ : ℝ) + 1)) / 2 := div_le_div_of_nonneg_right h (by norm_num)
    _ = _ := by field_simp

end MatrixSpencer.KSFullManuscriptEllipsoidVolume
