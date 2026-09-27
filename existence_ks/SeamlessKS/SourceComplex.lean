import SeamlessKS.Source
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.MeanValue

/-! An actual holomorphic extension of the smooth scalar source. -/
noncomputable section
namespace SeamlessKS
namespace Source

/-- Principal square root of the complex smoothed square. -/
def complexRoot (ζ : ℝ) (w : ℂ) : ℂ :=
  (w ^ 2 + (ζ : ℂ) ^ 2) ^ (2⁻¹ : ℂ)

/-- Holomorphic extension of the scalar source in the strip `|im w| < ζ`. -/
def complexWeight (u ζ : ℝ) (w : ℂ) : ℂ :=
  (u : ℂ) * (1 - w ^ 2 + (Real.sqrt (1 + ζ ^ 2) : ℂ) - complexRoot ζ w)

theorem complexRoot_sq (ζ : ℝ) (w : ℂ) :
    complexRoot ζ w ^ 2 = w ^ 2 + (ζ : ℂ) ^ 2 := by
  unfold complexRoot
  exact Complex.cpow_ofNat_inv_pow _ 2

theorem complexRoot_real {ζ : ℝ} (hζ : 0 < ζ) (x : ℝ) :
    complexRoot ζ (x : ℂ) = (Real.sqrt (x ^ 2 + ζ ^ 2) : ℂ) := by
  have ht : 0 < Real.sqrt (x ^ 2 + ζ ^ 2) := Real.sqrt_pos.mpr (radicand_pos hζ x)
  have he : (Real.sqrt (x ^ 2 + ζ ^ 2) : ℂ) ^ 2 = (x : ℂ) ^ 2 + (ζ : ℂ) ^ 2 := by
    exact_mod_cast Real.sq_sqrt (radicand_pos hζ x).le
  unfold complexRoot
  rw [← he]
  exact Complex.sq_cpow_two_inv ht

@[simp] theorem complexWeight_real {ζ : ℝ} (hζ : 0 < ζ) (u x : ℝ) :
    complexWeight u ζ (x : ℂ) = (weight u ζ x : ℂ) := by
  simp only [complexWeight, complexRoot_real hζ, weight, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow]

theorem complex_radicand_re_pos {ζ : ℝ} (hζ : 0 < ζ) {w : ℂ} (hw : |w.im| < ζ) :
    0 < (w ^ 2 + (ζ : ℂ) ^ 2).re := by
  have hs : w.im ^ 2 < ζ ^ 2 := by
    nlinarith [sq_abs w.im, mul_pos (sub_pos.mpr hw)
      (show 0 < ζ + |w.im| by positivity)]
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [sq_nonneg w.re]

theorem complexRoot_analyticAt {ζ : ℝ} (hζ : 0 < ζ) {w : ℂ} (hw : |w.im| < ζ) :
    AnalyticAt ℂ (complexRoot ζ) w := by
  have harg : AnalyticAt ℂ (fun z : ℂ => z ^ 2 + (ζ : ℂ) ^ 2) w :=
    (analyticAt_id.pow 2).add analyticAt_const
  exact harg.cpow analyticAt_const
    (Complex.mem_slitPlane_iff.mpr (Or.inl (complex_radicand_re_pos hζ hw)))

theorem complexWeight_analyticAt {ζ : ℝ} (hζ : 0 < ζ) (u : ℝ)
    {w : ℂ} (hw : |w.im| < ζ) : AnalyticAt ℂ (complexWeight u ζ) w :=
  analyticAt_const.mul (((analyticAt_const.sub (analyticAt_id.pow 2)).add analyticAt_const).sub
    (complexRoot_analyticAt hζ hw))

/-- Absolute control of the complex root does not require a spectral margin. -/
theorem norm_complexRoot_le {ζ : ℝ} (hζ : 0 ≤ ζ) (w : ℂ) :
    ‖complexRoot ζ w‖ ≤ ‖w‖ + ζ := by
  have he : ‖complexRoot ζ w‖ ^ 2 = ‖w ^ 2 + (ζ : ℂ) ^ 2‖ := by
    rw [← norm_pow, complexRoot_sq]
  have hn := norm_add_le (w ^ 2) ((ζ : ℂ) ^ 2)
  rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hζ] at hn
  nlinarith [norm_nonneg (complexRoot ζ w), norm_nonneg w]

/-- A conservative source coefficient budget on the complex neighborhood. -/
theorem norm_complexWeight_le {u ζ : ℝ} (hu : 0 ≤ u) (hζ : 0 ≤ ζ)
    (hζone : ζ ≤ 1) {w : ℂ} (hw : ‖w‖ ≤ 3) :
    ‖complexWeight u ζ w‖ ≤ 16 * u := by
  have hs : Real.sqrt (1 + ζ ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hroot := norm_complexRoot_le hζ w
  have hbracket : ‖1 - w ^ 2 + (Real.sqrt (1 + ζ ^ 2) : ℂ) - complexRoot ζ w‖ ≤ 16 := by
    have h₁ := norm_sub_le (1 : ℂ) (w ^ 2)
    have h₂ := norm_add_le (1 - w ^ 2) (Real.sqrt (1 + ζ ^ 2) : ℂ)
    have h₃ := norm_sub_le (1 - w ^ 2 + (Real.sqrt (1 + ζ ^ 2) : ℂ)) (complexRoot ζ w)
    rw [norm_one, norm_pow] at h₁
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h₂
    nlinarith [norm_nonneg w]
  unfold complexWeight
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  have hm := mul_le_mul_of_nonneg_left hbracket hu
  nlinarith


/-- The principal root is nonzero throughout the holomorphic strip. -/
theorem complexRoot_ne_zero {ζ : ℝ} (hζ : 0 < ζ) {w : ℂ} (hw : |w.im| < ζ) :
    complexRoot ζ w ≠ 0 := by
  intro he
  have hs := complexRoot_sq ζ w
  rw [he, zero_pow (by norm_num : 2 ≠ 0)] at hs
  have hr := complex_radicand_re_pos hζ hw
  rw [← hs] at hr
  norm_num at hr

theorem hasDerivAt_complexRoot {ζ : ℝ} (hζ : 0 < ζ) {w : ℂ} (hw : |w.im| < ζ) :
    HasDerivAt (complexRoot ζ) (w / complexRoot ζ w) w := by
  have hd := (complexRoot_analyticAt hζ hw).differentiableAt.hasDerivAt
  have hs := hd.pow 2
  have hsqfun : (fun z : ℂ => complexRoot ζ z ^ 2) = fun z => z ^ 2 + (ζ : ℂ) ^ 2 :=
    funext (complexRoot_sq ζ)
  change HasDerivAt (fun z : ℂ => complexRoot ζ z ^ 2)
    (2 * complexRoot ζ w ^ (2 - 1) * deriv (complexRoot ζ) w) w at hs
  rw [hsqfun] at hs
  have ha : HasDerivAt (fun z : ℂ => z ^ 2 + (ζ : ℂ) ^ 2) (2 * w) w := by
    convert ((hasDerivAt_id w).pow 2).add_const ((ζ : ℂ) ^ 2) using 1 <;> simp
  have he := hs.unique ha
  simp only [Nat.cast_ofNat, pow_one, Nat.reduceSub] at he
  convert hd using 1
  field_simp [complexRoot_ne_zero hζ hw]
  linear_combination -he / 2

/-- On the half strip the smoothed square root derivative has norm at most one. -/
theorem norm_self_le_complexRoot {ζ : ℝ} (hζ : 0 < ζ) {w : ℂ}
    (hw : |w.im| ≤ ζ / 2) : ‖w‖ ≤ ‖complexRoot ζ w‖ := by
  have hi : w.im ^ 2 ≤ ζ ^ 2 / 4 := by
    have hs := pow_le_pow_left₀ (abs_nonneg w.im) hw 2
    rw [sq_abs] at hs
    nlinarith
  have hid : ‖w ^ 2 + (ζ : ℂ) ^ 2‖ ^ 2 - (‖w‖ ^ 2) ^ 2 =
      2 * ζ ^ 2 * w.re ^ 2 - 2 * ζ ^ 2 * w.im ^ 2 + ζ ^ 4 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, pow_two, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hnonneg : 0 ≤ 2 * ζ ^ 2 * w.re ^ 2 - 2 * ζ ^ 2 * w.im ^ 2 + ζ ^ 4 := by
    have h₁ : 0 ≤ ζ ^ 2 - 2 * w.im ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg ζ) h₁,
      mul_nonneg (sq_nonneg ζ) (sq_nonneg w.re)]
  have hr : ‖w‖ ^ 2 ≤ ‖w ^ 2 + (ζ : ℂ) ^ 2‖ := by
    nlinarith [norm_nonneg (w ^ 2 + (ζ : ℂ) ^ 2), sq_nonneg ‖w‖]
  have hs : ‖complexRoot ζ w‖ ^ 2 = ‖w ^ 2 + (ζ : ℂ) ^ 2‖ := by
    rw [← norm_pow, complexRoot_sq]
  nlinarith [norm_nonneg w, norm_nonneg (complexRoot ζ w)]

def complexSlope (u ζ : ℝ) (w : ℂ) : ℂ :=
  -(u : ℂ) * (2 * w + w / complexRoot ζ w)

theorem hasDerivAt_complexWeight {ζ : ℝ} (hζ : 0 < ζ) (u : ℝ) {w : ℂ}
    (hw : |w.im| < ζ) : HasDerivAt (complexWeight u ζ) (complexSlope u ζ w) w := by
  have hpow : HasDerivAt (fun z : ℂ => z ^ 2) (2 * w) w := by
    convert (hasDerivAt_id w).pow 2 using 1 <;> simp
  have h := (((hasDerivAt_const w (1 : ℂ)).sub hpow).add_const
    (Real.sqrt (1 + ζ ^ 2) : ℂ)).sub (hasDerivAt_complexRoot hζ hw)
  convert h.const_mul (u : ℂ) using 1 <;> simp [complexSlope] <;> ring

theorem norm_complexSlope_le {u ζ : ℝ} (hu : 0 ≤ u) (hζ : 0 < ζ) {w : ℂ}
    (hw : |w.im| ≤ ζ / 2) (hwnorm : ‖w‖ ≤ 3) : ‖complexSlope u ζ w‖ ≤ 7 * u := by
  have hroot := norm_self_le_complexRoot hζ hw
  have hquot : ‖w / complexRoot ζ w‖ ≤ 1 := by
    rw [norm_div]
    exact div_le_one_of_le₀ hroot (norm_nonneg _)
  have hsum := norm_add_le (2 * w) (w / complexRoot ζ w)
  rw [norm_mul] at hsum
  norm_num only [Complex.norm_ofNat] at hsum
  unfold complexSlope
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  have hm := mul_le_mul_of_nonneg_left (show ‖2 * w + w / complexRoot ζ w‖ ≤ 7 by linarith) hu
  nlinarith


/-- A complex displacement estimate from the actual derivative on a convex ball. -/
theorem complexWeight_displacement {u ζ x r : ℝ} (hu : 0 ≤ u) (hζ : 0 < ζ)
    (hx : |x| ≤ 1) (hr : 0 ≤ r) (hrtwo : r ≤ 2) (hrζ : r ≤ ζ / 2)
    (z : ℂ) (hz : ‖z‖ ≤ r) :
    ‖complexWeight u ζ ((x : ℂ) + z) - (weight u ζ x : ℂ)‖ ≤ 7 * u * r := by
  let s := Metric.closedBall (x : ℂ) r
  have hball (w : ℂ) (hw : w ∈ s) : |w.im| ≤ ζ / 2 ∧ ‖w‖ ≤ 3 := by
    have hdist : ‖w - (x : ℂ)‖ ≤ r := by simpa only [s, Metric.mem_closedBall, dist_eq_norm] using hw
    have him := Complex.abs_im_le_norm (w - (x : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
    have hnorm := norm_add_le (w - (x : ℂ)) (x : ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at hnorm
    exact ⟨him.trans (hdist.trans hrζ), by linarith⟩
  have hderiv : ∀ w ∈ s, HasDerivWithinAt (complexWeight u ζ) (complexSlope u ζ w) s w := by
    intro w hw
    exact (hasDerivAt_complexWeight hζ u (by have h := (hball w hw).1; linarith)).hasDerivWithinAt
  have hbound : ∀ w ∈ s, ‖complexSlope u ζ w‖ ≤ 7 * u := by
    intro w hw
    exact norm_complexSlope_le hu hζ (hball w hw).1 (hball w hw).2
  have hxmem : (x : ℂ) ∈ s := by simp [s, hr]
  have hzmem : (x : ℂ) + z ∈ s := by
    simpa only [s, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hz
  have hm := (convex_closedBall (x : ℂ) r).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound hxmem hzmem
  rw [complexWeight_real hζ, add_sub_cancel_left] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left hz (by positivity))

/-- The source floor uses the endpoint margin, not a source eigenvalue. -/
theorem weight_margin_lower {u ζ x ρ : ℝ} (hu : 0 ≤ u) (hρ : 0 < ρ)
    (hx : |x| ≤ 1 - ρ) : u * ρ ≤ weight u ζ x := by
  have hxone : |x| ≤ 1 := by linarith
  have hgap : ρ ≤ 1 - x ^ 2 := by
    nlinarith [sq_abs x, abs_nonneg x,
      mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hxone)]
  exact (mul_le_mul_of_nonneg_left hgap hu).trans (weight_lower hu hxone)

def complexError (u ζ x : ℝ) (z : ℂ) : ℂ :=
  (complexWeight u ζ ((x : ℂ) + z) - (weight u ζ x : ℂ)) / (weight u ζ x : ℂ)

/-- Uniform relative owner control; the scale `u` cancels. -/
theorem norm_complexError_le {u ζ x ρ r : ℝ} (hu : 0 < u) (hζ : 0 < ζ)
    (hρ : 0 < ρ) (hx : |x| ≤ 1 - ρ) (hr : 0 ≤ r) (hrtwo : r ≤ 2)
    (hrζ : r ≤ ζ / 2) (z : ℂ) (hz : ‖z‖ ≤ r) :
    ‖complexError u ζ x z‖ ≤ 7 * r / ρ := by
  have hbase := weight_margin_lower (ζ := ζ) hu.le hρ hx
  have hpos : 0 < weight u ζ x := (mul_pos hu hρ).trans_le hbase
  have hd := complexWeight_displacement hu.le hζ (by linarith : |x| ≤ 1) hr hrtwo hrζ z hz
  unfold complexError
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  calc
    _ ≤ (7 * u * r) / weight u ζ x := div_le_div_of_nonneg_right hd hpos.le
    _ ≤ (7 * u * r) / (u * ρ) := div_le_div_of_nonneg_left (by positivity) (mul_pos hu hρ) hbase
    _ = 7 * r / ρ := by field_simp

theorem complexWeight_eq_base_mul_error {u ζ x ρ : ℝ} (hu : 0 < u) (hρ : 0 < ρ)
    (hx : |x| ≤ 1 - ρ) (z : ℂ) :
    complexWeight u ζ ((x : ℂ) + z) =
      (weight u ζ x : ℂ) * (1 + complexError u ζ x z) := by
  have hpos : 0 < weight u ζ x := (mul_pos hu hρ).trans_le (weight_margin_lower hu.le hρ hx)
  have hne : (weight u ζ x : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  unfold complexError
  field_simp [hne]
  ring

end Source
end SeamlessKS
