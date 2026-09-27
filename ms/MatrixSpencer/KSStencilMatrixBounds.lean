import MatrixSpencer.KSStencilMagnitudeBounds
import MatrixSpencer.KSFullManuscriptQueries

/-! Entry magnitudes from uniform bounds at actual finite query points.
These lemmas apply equally to the original finite solvers and the explicitly
named convex-solver variants. -/

open Matrix
noncomputable section
namespace MatrixSpencer.KSStencilMatrixBounds
open KSNumericalHessian (Space coordinate)
open KSFullManuscriptQueries
variable {m : ℕ}

theorem query_norm {t R : ℝ} (ht : 0 ≤ t) (hR : 2*t ≤ R)
    (w : Space m) (hw : ‖w‖ ≤ 2) : ‖t • w‖ ≤ R := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  exact (mul_le_mul_of_nonneg_left hw ht).trans (by linarith)

theorem mixedStencil_abs (report : Space m → ℝ) {t R V : ℝ}
    (ht : 0 ≤ t) (hR : 2*t ≤ R)
    (hreport : ∀ z : Space m, ‖z‖ ≤ R → |report z| ≤ V) (i j : Fin m) :
    |KSFourthDifference.mixedStencil report 0 (coordinate i) (coordinate j) t| ≤ V/t^2 := by
  have hp := query_norm ht hR _ (coordinate_add_norm_le_two i j)
  have hm := query_norm ht hR _ (coordinate_sub_norm_le_two i j)
  have hpp := hreport (t • (coordinate i + coordinate j)) hp
  have hpm := hreport (t • (coordinate i - coordinate j)) hm
  have hmp := hreport (-(t • (coordinate i - coordinate j))) (by simpa only [norm_neg] using hm)
  have hmm := hreport (-(t • (coordinate i + coordinate j))) (by simpa only [norm_neg] using hp)
  simpa only [KSFourthDifference.mixedStencil, zero_add, zero_sub] using
    KSStencilMagnitudeBounds.four_value_bound (t := t) hpp hpm hmp hmm

theorem full_matrixReport_abs (report : Space m → ℝ) {t R V : ℝ}
    (ht : 0 ≤ t) (hR : 2*t ≤ R) (hV : 0 ≤ V)
    (hreport : ∀ z : Space m, ‖z‖ ≤ R → |report z| ≤ V) (i j : Fin m) :
    |KSFullManuscriptHessian.matrixReport report 0 t i j| ≤ 4*V/t^2 := by
  by_cases hij : i = j
  · subst j
    have hi := query_norm ht hR (coordinate i) (by rw [coordinate_norm]; norm_num)
    have hp := hreport (t • coordinate i) hi
    have hm := hreport (-(t • coordinate i)) (by simpa only [norm_neg] using hi)
    have hz := hreport 0 (by rw [norm_zero]; linarith)
    simpa only [KSFullManuscriptHessian.matrixReport, if_pos rfl,
      KSFourthDifference.directionalSecond, zero_add, zero_sub] using
        KSStencilMagnitudeBounds.three_value_bound (t := t) hp hz hm
  · rw [KSFullManuscriptHessian.matrixReport, if_neg hij]
    exact (mixedStencil_abs report ht hR hreport i j).trans
      (div_le_div_of_nonneg_right (by linarith) (sq_nonneg t))

theorem eighth_matrixReport_abs (report : Space m → ℝ) {t R V : ℝ}
    (ht : 0 ≤ t) (hR : 2*t ≤ R)
    (hreport : ∀ z : Space m, ‖z‖ ≤ R → |report z| ≤ V) (i j : Fin m) :
    |KSNumericalHessian.matrixReport report 0 t i j| ≤ V/t^2 :=
  mixedStencil_abs report ht hR hreport i j

theorem weighted_abs (w : Fin m → ℝ) (hw : ∀ i, |w i| ≤ 1)
    (A : Matrix (Fin m) (Fin m) ℝ) {V : ℝ} (hV : 0 ≤ V)
    (hA : ∀ i j, |A i j| ≤ V) (i j : Fin m) :
    |KSFullManuscriptHessian.weighted w A i j| ≤ V := by
  rw [KSFullManuscriptHessian.weighted, abs_div, abs_mul, abs_mul]
  have h : |w i| * |A i j| * |w j| ≤ 1*V*1 :=
    mul_le_mul (mul_le_mul (hw i) (hA i j) (abs_nonneg _) (by norm_num))
      (hw j) (abs_nonneg _) (by simpa using hV)
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2), one_mul, mul_one] at h ⊢
  linarith

theorem symmetrize_abs (A : Matrix (Fin m) (Fin m) ℝ) {V : ℝ}
    (hA : ∀ i j, |A i j| ≤ V) (i j : Fin m) :
    |KSMatrixEntryAccuracy.symmetrize A i j| ≤ V := by
  have h1 := abs_le.mp (hA i j)
  have h2 := abs_le.mp (hA j i)
  rw [KSMatrixEntryAccuracy.symmetrize, abs_le]
  constructor <;> linarith

theorem half_smul_abs (A : Matrix (Fin m) (Fin m) ℝ) {V : ℝ}
    (hV : 0 ≤ V) (hA : ∀ i j, |A i j| ≤ V) (i j : Fin m) :
    |((1/2 : ℝ) • A) i j| ≤ V := by
  simp only [Matrix.smul_apply, smul_eq_mul, abs_mul]
  norm_num
  linarith [hA i j]

theorem reciprocal_scaled_abs (A : Matrix (Fin m) (Fin m) ℝ) {V κ K : ℝ}
    (hV : 0 ≤ V) (hA : ∀ i j, |A i j| ≤ V)
    (hκ : 0 ≤ κ) (hK : κ⁻¹ ≤ K) (i j : Fin m) :
    |((-κ⁻¹) • A) i j| ≤ K*V := by
  simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_neg,
    abs_of_nonneg (inv_nonneg.mpr hκ)]
  exact mul_le_mul hK (hA i j) (abs_nonneg _) (le_trans (inv_nonneg.mpr hκ) hK)

end MatrixSpencer.KSStencilMatrixBounds
