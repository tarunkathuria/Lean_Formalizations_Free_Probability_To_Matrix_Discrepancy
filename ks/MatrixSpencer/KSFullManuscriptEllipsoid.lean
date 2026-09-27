import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic



open scoped InnerProductSpace
noncomputable section
namespace MatrixSpencer.KSFullManuscriptEllipsoid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def center (ℓ : ℝ) (a : E) : E := -(1 / (ℓ + 1)) • a


def inverseAction (ℓ : ℝ) (a v : E) : E :=
  ((ℓ ^ 2 - 1) / ℓ ^ 2) • (v + (2 / (ℓ - 1) * ⟪a, v⟫_ℝ) • a)


def shapeAction (ℓ : ℝ) (a v : E) : E :=
  (ℓ ^ 2 / (ℓ ^ 2 - 1)) • (v - (2 / (ℓ + 1) * ⟪a, v⟫_ℝ) • a)

def inverseQuadratic (ℓ : ℝ) (a v : E) : ℝ :=
  ((ℓ ^ 2 - 1) / ℓ ^ 2) *
    (‖v‖ ^ 2 + 2 / (ℓ - 1) * ⟪a, v⟫_ℝ ^ 2)

def ellipsoid (ℓ : ℝ) (a : E) : Set E :=
  {y | inverseQuadratic ℓ a (y - center ℓ a) ≤ 1}

theorem inner_inverseAction (ℓ : ℝ) (a v : E) :
    ⟪v, inverseAction ℓ a v⟫_ℝ = inverseQuadratic ℓ a v := by
  simp only [inverseAction, inverseQuadratic, inner_smul_right, inner_add_right,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm v a]
  ring

theorem shape_inverseAction {ℓ : ℝ} (hℓ : 1 < ℓ) {a : E}
    (ha : ‖a‖ = 1) (v : E) :
    shapeAction ℓ a (inverseAction ℓ a v) = v := by
  have hℓ0 : ℓ ≠ 0 := by linarith
  have hℓ1 : ℓ - 1 ≠ 0 := by linarith
  have hℓp : ℓ + 1 ≠ 0 := by linarith
  have hsq : ℓ ^ 2 - 1 ≠ 0 := by nlinarith
  have hip : ⟪a, inverseAction ℓ a v⟫_ℝ =
      ((ℓ ^ 2 - 1) / ℓ ^ 2) * (1 + 2 / (ℓ - 1)) * ⟪a, v⟫_ℝ := by
    simp only [inverseAction, inner_smul_right, inner_add_right,
      real_inner_self_eq_norm_sq, ha, one_pow, mul_one]
    ring
  have hc : 2 / (ℓ + 1) *
      (((ℓ ^ 2 - 1) / ℓ ^ 2) * (1 + 2 / (ℓ - 1)) * ⟪a, v⟫_ℝ) =
      ((ℓ ^ 2 - 1) / ℓ ^ 2) * (2 / (ℓ - 1) * ⟪a, v⟫_ℝ) := by
    field_simp
    ring
  have hd : (ℓ ^ 2 / (ℓ ^ 2 - 1)) * ((ℓ ^ 2 - 1) / ℓ ^ 2) = 1 := by
    field_simp
  rw [shapeAction, hip, hc, inverseAction, smul_add, smul_smul,
    add_sub_cancel_right, smul_smul, hd, one_smul]

theorem inverseQuadratic_pos {ℓ : ℝ} (hℓ : 1 < ℓ) (a : E)
    {v : E} (hv : v ≠ 0) : 0 < inverseQuadratic ℓ a v := by
  have hsq : 1 < ℓ ^ 2 := by nlinarith
  have hn : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  unfold inverseQuadratic
  exact mul_pos (div_pos (by linarith) (by linarith))
    (add_pos_of_pos_of_nonneg hn
      (mul_nonneg (div_nonneg (by norm_num) (by linarith)) (sq_nonneg _)))

theorem shifted_quadratic {ℓ : ℝ} (hℓ : 1 < ℓ) {a : E} (ha : ‖a‖ = 1) (y : E) :
    inverseQuadratic ℓ a (y - center ℓ a) =
      ((ℓ ^ 2 - 1) / ℓ ^ 2) * ‖y‖ ^ 2 + 1 / ℓ ^ 2 +
        (2 * (ℓ + 1) / ℓ ^ 2) * ⟪a, y⟫_ℝ * (⟪a, y⟫_ℝ + 1) := by
  have hℓ0 : ℓ ≠ 0 := by linarith
  have hℓ1 : ℓ - 1 ≠ 0 := by linarith
  have hℓp : ℓ + 1 ≠ 0 := by linarith
  have hshift : y - center ℓ a = y + (1 / (ℓ + 1)) • a := by
    simp [center]
  rw [hshift]
  unfold inverseQuadratic
  rw [norm_add_sq_real]
  simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, ha,
    norm_smul, Real.norm_eq_abs, mul_one, one_pow, sq_abs]
  rw [real_inner_comm y a]
  field_simp
  ring

/-- Every point in the retained unit half-ball is in the explicitly
defined new ellipsoid. The normal is the actual unit cut direction. -/
theorem halfBall_subset_ellipsoid {ℓ : ℝ} (hℓ : 1 < ℓ) {a : E}
    (ha : ‖a‖ = 1) :
    {y : E | ‖y‖ ≤ 1 ∧ ⟪a, y⟫_ℝ ≤ 0} ⊆ ellipsoid ℓ a := by
  intro y hy
  have habs : |⟪a, y⟫_ℝ| ≤ 1 := by
    calc
      _ ≤ ‖a‖ * ‖y‖ := abs_real_inner_le_norm a y
      _ ≤ 1 := by simpa only [ha, one_mul] using hy.1
  have ht : -1 ≤ ⟪a, y⟫_ℝ := (abs_le.mp habs).1
  have hprod : ⟪a, y⟫_ℝ * (⟪a, y⟫_ℝ + 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hy.2 (by linarith)
  have hnorm : ‖y‖ ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg y) hy.1 2
  have hsq : 1 < ℓ ^ 2 := by nlinarith
  have hcoef : 0 ≤ (ℓ ^ 2 - 1) / ℓ ^ 2 :=
    div_nonneg (sub_nonneg.mpr hsq.le) (sq_nonneg _)
  have hcoef' : 0 ≤ 2 * (ℓ + 1) / ℓ ^ 2 := by positivity
  have hb := mul_le_mul_of_nonneg_left hnorm hcoef
  have hc := mul_nonpos_of_nonneg_of_nonpos hcoef' hprod
  have he : (ℓ ^ 2 - 1) / ℓ ^ 2 + 1 / ℓ ^ 2 = 1 := by
    field_simp
    ring
  change inverseQuadratic ℓ a (y - center ℓ a) ≤ 1
  rw [shifted_quadratic hℓ ha]
  nlinarith

end MatrixSpencer.KSFullManuscriptEllipsoid
