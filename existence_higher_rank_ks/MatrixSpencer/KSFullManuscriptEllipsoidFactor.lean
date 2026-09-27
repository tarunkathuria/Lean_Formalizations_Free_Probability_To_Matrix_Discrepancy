import MatrixSpencer.KSFullManuscriptEllipsoid
import Mathlib.Analysis.SpecialFunctions.Sqrt



open scoped InnerProductSpace
noncomputable section
namespace MatrixSpencer.KSFullManuscriptEllipsoidFactor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def axialMap (p q : ℝ) (a v : E) : E := p • v + ((q - p) * ⟪a, v⟫_ℝ) • a

theorem axialMap_comp (p q r s : ℝ) {a : E} (ha : ‖a‖ = 1) (v : E) :
    axialMap p q a (axialMap r s a v) = axialMap (p * r) (q * s) a v := by
  have hi : ⟪a, axialMap r s a v⟫_ℝ = s * ⟪a, v⟫_ℝ := by
    simp only [axialMap, inner_add_right, inner_smul_right,
      real_inner_self_eq_norm_sq, ha, one_pow, mul_one]
    ring
  rw [axialMap, hi, axialMap, axialMap]
  simp only [smul_add, smul_smul]
  module

theorem axialMap_one (a v : E) : axialMap 1 1 a v = v := by simp [axialMap]

theorem axialMap_inverse {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    {a : E} (ha : ‖a‖ = 1) (v : E) :
    axialMap p q a (axialMap p⁻¹ q⁻¹ a v) = v := by
  rw [axialMap_comp p q _ _ ha, mul_inv_cancel₀ hp, mul_inv_cancel₀ hq, axialMap_one]

theorem axialMap_norm_sq (p q : ℝ) {a : E} (ha : ‖a‖ = 1) (v : E) :
    ‖axialMap p q a v‖ ^ 2 =
      p ^ 2 * ‖v‖ ^ 2 + (q ^ 2 - p ^ 2) * ⟪a, v⟫_ℝ ^ 2 := by
  rw [axialMap, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ha, mul_one,
    real_inner_smul_left, inner_smul_right]
  rw [real_inner_comm v a]
  ring

def transverse (ℓ : ℝ) : ℝ := Real.sqrt (ℓ ^ 2 / (ℓ ^ 2 - 1))
def axial (ℓ : ℝ) : ℝ := ℓ / (ℓ + 1)
def factor (ℓ : ℝ) (a v : E) : E := axialMap (transverse ℓ) (axial ℓ) a v
def inverseFactor (ℓ : ℝ) (a v : E) : E := axialMap (transverse ℓ)⁻¹ (axial ℓ)⁻¹ a v

theorem transverse_pos {ℓ : ℝ} (hℓ : 1 < ℓ) : 0 < transverse ℓ := by
  apply Real.sqrt_pos.mpr
  exact div_pos (by positivity) (by nlinarith)

theorem axial_pos {ℓ : ℝ} (hℓ : 1 < ℓ) : 0 < axial ℓ :=
  div_pos (by linarith) (by linarith)

theorem factor_inverseFactor {ℓ : ℝ} (hℓ : 1 < ℓ) {a : E} (ha : ‖a‖ = 1) (v : E) :
    factor ℓ a (inverseFactor ℓ a v) = v :=
  axialMap_inverse (ne_of_gt (transverse_pos hℓ)) (ne_of_gt (axial_pos hℓ)) ha v

theorem inverseFactor_norm_sq {ℓ : ℝ} (hℓ : 1 < ℓ) {a : E} (ha : ‖a‖ = 1) (v : E) :
    ‖inverseFactor ℓ a v‖ ^ 2 = KSFullManuscriptEllipsoid.inverseQuadratic ℓ a v := by
  have hℓ0 : ℓ ≠ 0 := by linarith
  have hℓ1 : ℓ - 1 ≠ 0 := by linarith
  have hℓp : ℓ + 1 ≠ 0 := by linarith
  have hsq : ℓ ^ 2 - 1 ≠ 0 := by nlinarith
  have hratio : 0 ≤ ℓ ^ 2 / (ℓ ^ 2 - 1) :=
    div_nonneg (sq_nonneg _) (by nlinarith)
  rw [inverseFactor, axialMap_norm_sq _ _ ha]
  simp only [transverse, inv_pow, Real.sq_sqrt hratio, axial,
    KSFullManuscriptEllipsoid.inverseQuadratic]
  field_simp
  ring

/-- The proved quadratic ellipsoid has an explicit unit-ball parameterization.
The witness is the actual inverse factor applied to the shifted point. -/
theorem mem_ellipsoid_iff {ℓ : ℝ} (hℓ : 1 < ℓ) {a : E} (ha : ‖a‖ = 1) (y : E) :
    y ∈ KSFullManuscriptEllipsoid.ellipsoid ℓ a ↔
      ∃ z : E, ‖z‖ ≤ 1 ∧ y = KSFullManuscriptEllipsoid.center ℓ a + factor ℓ a z := by
  constructor
  · intro hy
    refine ⟨inverseFactor ℓ a (y - KSFullManuscriptEllipsoid.center ℓ a), ?_, ?_⟩
    · have hnorm : ‖inverseFactor ℓ a (y - KSFullManuscriptEllipsoid.center ℓ a)‖ ^ 2 ≤ 1 := by
        rw [inverseFactor_norm_sq hℓ ha]
        exact hy
      nlinarith [norm_nonneg (inverseFactor ℓ a (y - KSFullManuscriptEllipsoid.center ℓ a))]
    · rw [factor_inverseFactor hℓ ha]
      abel
  · rintro ⟨z, hz, rfl⟩
    change KSFullManuscriptEllipsoid.inverseQuadratic ℓ a
      (KSFullManuscriptEllipsoid.center ℓ a + factor ℓ a z - KSFullManuscriptEllipsoid.center ℓ a) ≤ 1
    rw [add_sub_cancel_left, ← inverseFactor_norm_sq hℓ ha]
    have hi : inverseFactor ℓ a (factor ℓ a z) = z := by
      change axialMap (transverse ℓ)⁻¹ (axial ℓ)⁻¹ a
        (axialMap (transverse ℓ) (axial ℓ) a z) = z
      rw [axialMap_comp _ _ _ _ ha,
        inv_mul_cancel₀ (ne_of_gt (transverse_pos hℓ)),
        inv_mul_cancel₀ (ne_of_gt (axial_pos hℓ)), axialMap_one]
    rw [hi]
    simpa using pow_le_pow_left₀ (norm_nonneg z) hz 2

end MatrixSpencer.KSFullManuscriptEllipsoidFactor
