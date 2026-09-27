import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The positive-real seed for the compact resolvent square-root integral

The rational kernel is integrated using an explicit arctangent primitive.
No matrix spectral statement or assumed integral identity enters this proof.
-/

open MeasureTheory
open scoped Interval
noncomputable section
namespace MatrixSpencer.KSScalarRootIntegral

def kernel (x a : ℝ) : ℝ := x / (a ^ 2 + (1 - a) ^ 2 * x)

def primitive (x a : ℝ) : ℝ :=
  Real.sqrt x * Real.arctan ((a * (1 + x) - x) / Real.sqrt x)

theorem denominator_pos {x : ℝ} (hx : 0 < x) (a : ℝ) :
    0 < a ^ 2 + (1 - a) ^ 2 * x := by
  by_cases ha : a = 0
  · simpa only [ha, zero_pow (by norm_num : 2 ≠ 0), sub_zero, one_pow, one_mul, zero_add] using hx
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (mul_nonneg (sq_nonneg _) hx.le)

theorem kernel_continuous {x : ℝ} (hx : 0 < x) : Continuous (kernel x) :=
  continuous_const.div
    ((continuous_id.pow 2).add ((continuous_const.sub continuous_id).pow 2 |>.mul continuous_const))
    (fun a => (denominator_pos hx a).ne')

theorem hasDerivAt_primitive {x : ℝ} (hx : 0 < x) (a : ℝ) :
    HasDerivAt (primitive x) (kernel x a) a := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hd := (((hasDerivAt_id a).mul_const (1 + x)).sub_const x).div_const (Real.sqrt x)
  have h := hd.arctan.const_mul (Real.sqrt x)
  convert h using 1
  dsimp only [kernel, id_eq]
  have hden_eq : 1 + ((a * (1 + x) - x) / Real.sqrt x) ^ 2 =
      (1 + x) * (a ^ 2 + (1 - a) ^ 2 * x) / x := by
    rw [div_pow, hsq]
    field_simp [hx.ne']
    ring
  rw [hden_eq]
  have hp : 1 + x ≠ 0 := by positivity
  field_simp [hx.ne', hs.ne', hp, (denominator_pos hx a).ne']

theorem primitive_endpoint_difference {x : ℝ} (hx : 0 < x) :
    primitive x 1 - primitive x 0 = Real.pi / 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hdiv : x / Real.sqrt x = Real.sqrt x := by
    apply (div_eq_iff hs.ne').mpr
    nlinarith [Real.sq_sqrt hx.le]
  simp only [primitive, one_mul, add_sub_cancel_right, zero_mul, zero_sub, neg_div,
    hdiv, Real.arctan_neg, one_div, Real.arctan_inv_of_pos hs]
  ring

/-- The rational kernel integrates to `π sqrt(x) / 2` for every positive real x. -/
theorem integral_kernel {x : ℝ} (hx : 0 < x) :
    (∫ a in (0 : ℝ)..1, kernel x a) = Real.pi / 2 * Real.sqrt x := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun a _ => hasDerivAt_primitive hx a) ((kernel_continuous hx).intervalIntegrable 0 1)]
  exact primitive_endpoint_difference hx

/-- Normalization yields the positive square root itself. -/
theorem normalized_integral {x : ℝ} (hx : 0 < x) :
    (2 / Real.pi) * (∫ a in (0 : ℝ)..1, x / (a ^ 2 + (1 - a) ^ 2 * x)) = Real.sqrt x := by
  change (2 / Real.pi) * (∫ a in (0 : ℝ)..1, kernel x a) = _
  rw [integral_kernel hx]
  field_simp [Real.pi_ne_zero]

/-- The same seed identity in the complex scalar algebra. -/
theorem normalized_complex_integral {x : ℝ} (hx : 0 < x) :
    (2 / (Real.pi : ℂ)) *
      (∫ a in (0 : ℝ)..1, (x : ℂ) / ((a : ℂ) ^ 2 + (1 - (a : ℂ)) ^ 2 * (x : ℂ))) =
      (Real.sqrt x : ℂ) := by
  have h := congrArg Complex.ofReal (normalized_integral hx)
  push_cast at h
  rw [← intervalIntegral.integral_ofReal] at h
  simpa only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one] using h

end MatrixSpencer.KSScalarRootIntegral
