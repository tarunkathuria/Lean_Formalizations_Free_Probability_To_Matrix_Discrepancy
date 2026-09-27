import SeamlessKS.SourceCalculus
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
Explicit third and fourth derivatives of the seamless source.  Their bounds
are polynomial in the reciprocal smoothing scale and hold on the entire
real line. These are bounds for the input source, not an assumed regularity
certificate for the optimized matrix potential.
-/
noncomputable section
namespace SeamlessKS
namespace Source

/-- Third derivative of the smooth source. -/
def third (u ζ x : ℝ) : ℝ :=
  3 * u * ζ ^ 2 * x / (Real.sqrt (x ^ 2 + ζ ^ 2)) ^ 5

/-- Fourth derivative of the smooth source. -/
def fourth (u ζ x : ℝ) : ℝ :=
  3 * u * ζ ^ 2 * (ζ ^ 2 - 4 * x ^ 2) / (Real.sqrt (x ^ 2 + ζ ^ 2)) ^ 7

theorem hasDerivAt_curvature {ζ : ℝ} (hζ : 0 < ζ) (u x : ℝ) :
    HasDerivAt (curvature u ζ) (third u ζ x) x := by
  have ht : 0 < Real.sqrt (x ^ 2 + ζ ^ 2) := Real.sqrt_pos.mpr (radicand_pos hζ x)
  have hden := (hasDerivAt_radialRoot hζ x).pow 3
  have hquot := (hasDerivAt_const x (u * ζ ^ 2)).div hden (pow_ne_zero 3 ht.ne')
  have h := (hasDerivAt_const x (-2 * u)).sub hquot
  convert h using 1
  unfold third
  dsimp
  field_simp
  ring

@[simp] theorem deriv_curvature {ζ : ℝ} (hζ : 0 < ζ) (u x : ℝ) :
    deriv (curvature u ζ) x = third u ζ x := (hasDerivAt_curvature hζ u x).deriv

theorem hasDerivAt_third {ζ : ℝ} (hζ : 0 < ζ) (u x : ℝ) :
    HasDerivAt (third u ζ) (fourth u ζ x) x := by
  have ht : 0 < Real.sqrt (x ^ 2 + ζ ^ 2) := Real.sqrt_pos.mpr (radicand_pos hζ x)
  have ht2 := Real.sq_sqrt (radicand_pos hζ x).le
  have hden := (hasDerivAt_radialRoot hζ x).pow 5
  have hnum := (hasDerivAt_id x).const_mul (3 * u * ζ ^ 2)
  have h := hnum.div hden (pow_ne_zero 5 ht.ne')
  convert h using 1
  unfold fourth
  dsimp
  field_simp
  ring_nf
  rw [Real.sq_sqrt (by positivity : 0 ≤ ζ ^ 2 + x ^ 2)]
  ring

@[simp] theorem deriv_third {ζ : ℝ} (hζ : 0 < ζ) (u x : ℝ) :
    deriv (third u ζ) x = fourth u ζ x := (hasDerivAt_third hζ u x).deriv

theorem iteratedDeriv_two_weight {ζ : ℝ} (hζ : 0 < ζ) (u : ℝ) :
    iteratedDeriv 2 (weight u ζ) = curvature u ζ := by
  funext x
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  exact second_deriv_weight hζ u x

theorem iteratedDeriv_three_weight {ζ : ℝ} (hζ : 0 < ζ) (u : ℝ) :
    iteratedDeriv 3 (weight u ζ) = third u ζ := by
  rw [iteratedDeriv_succ, iteratedDeriv_two_weight hζ]
  exact funext (deriv_curvature hζ u)

theorem iteratedDeriv_four_weight {ζ : ℝ} (hζ : 0 < ζ) (u : ℝ) :
    iteratedDeriv 4 (weight u ζ) = fourth u ζ := by
  rw [iteratedDeriv_succ, iteratedDeriv_three_weight hζ]
  exact funext (deriv_third hζ u)

lemma smoothing_le_root {ζ : ℝ} (hζ : 0 ≤ ζ) (x : ℝ) :
    ζ ≤ Real.sqrt (x ^ 2 + ζ ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg x])

theorem abs_curvature_le {u ζ : ℝ} (hu : 0 ≤ u) (hζ : 0 < ζ) (x : ℝ) :
    |curvature u ζ x| ≤ 2 * u + u / ζ := by
  let t := Real.sqrt (x ^ 2 + ζ ^ 2)
  have ht : 0 < t := Real.sqrt_pos.mpr (radicand_pos hζ x)
  have hζt : ζ ≤ t := smoothing_le_root hζ.le x
  have hpow : ζ ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ hζ.le hζt 3
  have hq : u * ζ ^ 2 / t ^ 3 ≤ u / ζ := by
    calc
      _ ≤ u * ζ ^ 2 / ζ ^ 3 := div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
      _ = u / ζ := by field_simp
  have hnonpos : curvature u ζ x ≤ 0 := (curvature_upper hu x).trans (by nlinarith)
  rw [abs_of_nonpos hnonpos]
  change -(-2 * u - u * ζ ^ 2 / t ^ 3) ≤ _
  linarith

theorem abs_third_le {u ζ : ℝ} (hu : 0 ≤ u) (hζ : 0 < ζ) (x : ℝ) :
    |third u ζ x| ≤ 3 * u / ζ ^ 2 := by
  let t := Real.sqrt (x ^ 2 + ζ ^ 2)
  have ht : 0 < t := Real.sqrt_pos.mpr (radicand_pos hζ x)
  have hζt : ζ ≤ t := smoothing_le_root hζ.le x
  have hxt : |x| ≤ t := Real.abs_le_sqrt (by nlinarith [sq_nonneg ζ])
  have hζt2 : ζ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hζ.le hζt 2
  have hnum : ζ ^ 2 * |x| ≤ t ^ 3 := by
    calc
      _ ≤ t ^ 2 * t := mul_le_mul hζt2 hxt (abs_nonneg x) (sq_nonneg t)
      _ = _ := by ring
  have habs : |third u ζ x| = (3 * u) * (ζ ^ 2 * |x|) / t ^ 5 := by
    simp only [third, abs_div, abs_mul, abs_of_nonneg hu, abs_pow,
      abs_of_nonneg hζ.le, abs_of_pos ht, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), t]
    ring
  rw [habs]
  calc
    _ ≤ (3 * u) * t ^ 3 / t ^ 5 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by positivity)) (by positivity)
    _ = 3 * u / t ^ 2 := by field_simp
    _ ≤ 3 * u / ζ ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hζt2

theorem abs_fourth_le {u ζ : ℝ} (hu : 0 ≤ u) (hζ : 0 < ζ) (x : ℝ) :
    |fourth u ζ x| ≤ 12 * u / ζ ^ 3 := by
  let t := Real.sqrt (x ^ 2 + ζ ^ 2)
  have ht : 0 < t := Real.sqrt_pos.mpr (radicand_pos hζ x)
  have ht2 : t ^ 2 = x ^ 2 + ζ ^ 2 := Real.sq_sqrt (radicand_pos hζ x).le
  have hζt : ζ ≤ t := smoothing_le_root hζ.le x
  have hζt2 : ζ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hζ.le hζt 2
  have hζt3 : ζ ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ hζ.le hζt 3
  have hinner : |ζ ^ 2 - 4 * x ^ 2| ≤ 4 * t ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg ζ]
  have hnum : ζ ^ 2 * |ζ ^ 2 - 4 * x ^ 2| ≤ 4 * t ^ 4 := by
    calc
      _ ≤ t ^ 2 * (4 * t ^ 2) :=
        mul_le_mul hζt2 hinner (abs_nonneg _) (sq_nonneg t)
      _ = _ := by ring
  have habs : |fourth u ζ x| = (3 * u) * (ζ ^ 2 * |ζ ^ 2 - 4 * x ^ 2|) / t ^ 7 := by
    simp only [fourth, abs_div, abs_mul, abs_of_nonneg hu, abs_pow,
      abs_of_nonneg hζ.le, abs_of_pos ht, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), t]
    ring
  rw [habs]
  calc
    _ ≤ (3 * u) * (4 * t ^ 4) / t ^ 7 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by positivity)) (by positivity)
    _ = 12 * u / t ^ 3 := by field_simp; ring
    _ ≤ 12 * u / ζ ^ 3 := div_le_div_of_nonneg_left (by positivity) (by positivity) hζt3

theorem iteratedDeriv_four_weight_le {u ζ : ℝ} (hu : 0 ≤ u) (hζ : 0 < ζ) (x : ℝ) :
    |iteratedDeriv 4 (weight u ζ) x| ≤ 12 * u / ζ ^ 3 := by
  rw [iteratedDeriv_four_weight hζ]
  exact abs_fourth_le hu hζ x


/-- Exact fourth derivative along an arbitrary real affine coordinate line. -/
theorem iteratedDeriv_four_line {ζ : ℝ} (hζ : 0 < ζ) (u x v : ℝ) :
    iteratedDeriv 4 (fun t : ℝ => weight u ζ (x + v * t)) =
      fun t => v ^ 4 * fourth u ζ (x + v * t) := by
  have hshift : ContDiff ℝ 4 (fun s : ℝ => weight u ζ (x + s)) :=
    (weight_contDiff hζ u 4).comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_comp_const_mul hshift v,
    iteratedDeriv_comp_const_add, iteratedDeriv_four_weight hζ]

/-- Polynomial fourth derivative bound along every unit-coordinate direction. -/
theorem iteratedDeriv_four_line_le {u ζ v : ℝ} (hu : 0 ≤ u) (hζ : 0 < ζ)
    (hv : |v| ≤ 1) (x t : ℝ) :
    |iteratedDeriv 4 (fun s : ℝ => weight u ζ (x + v * s)) t| ≤ 12 * u / ζ ^ 3 := by
  rw [iteratedDeriv_four_line hζ, abs_mul, abs_pow]
  have hv4 : |v| ^ 4 ≤ 1 := by simpa using pow_le_pow_left₀ (abs_nonneg v) hv 4
  calc
    _ ≤ 1 * (12 * u / ζ ^ 3) := mul_le_mul hv4 (abs_fourth_le hu hζ _)
      (abs_nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- The corresponding bound for directions bounded by two, used by stencil queries. -/
theorem iteratedDeriv_four_line_le_two {u ζ v : ℝ} (hu : 0 ≤ u) (hζ : 0 < ζ)
    (hv : |v| ≤ 2) (x t : ℝ) :
    |iteratedDeriv 4 (fun s : ℝ => weight u ζ (x + v * s)) t| ≤ 192 * u / ζ ^ 3 := by
  rw [iteratedDeriv_four_line hζ, abs_mul, abs_pow]
  have hv4 : |v| ^ 4 ≤ 16 := by
    have h := pow_le_pow_left₀ (abs_nonneg v) hv 4
    norm_num at h
    exact h
  calc
    _ ≤ 16 * (12 * u / ζ ^ 3) := mul_le_mul hv4 (abs_fourth_le hu hζ _)
      (abs_nonneg _) (by norm_num)
    _ = _ := by ring

end Source
end SeamlessKS
