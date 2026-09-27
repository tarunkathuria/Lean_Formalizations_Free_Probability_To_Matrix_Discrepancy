import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The smooth source and outward secant used by the seamless full-cube walk.
All estimates in this file are scalar consequences of the explicit formula. -/
noncomputable section
namespace SeamlessKS
namespace Source

/-- Smooth covariance weight; it vanishes at the actual cube endpoints. -/
def weight (u ζ x : ℝ) : ℝ :=
  u * (1 - x ^ 2 + Real.sqrt (1 + ζ ^ 2) - Real.sqrt (x ^ 2 + ζ ^ 2))

/-- Explicit first derivative of `weight`. -/
def slope (u ζ x : ℝ) : ℝ :=
  -u * (2 * x + x / Real.sqrt (x ^ 2 + ζ ^ 2))

/-- Explicit second derivative, with the positive square root cubed. -/
def curvature (u ζ x : ℝ) : ℝ :=
  -2 * u - u * ζ ^ 2 / (Real.sqrt (x ^ 2 + ζ ^ 2)) ^ 3

/-- The outward source loss per unit displacement, expressed at radius `r`. -/
def secant (u ζ r a : ℝ) : ℝ := (weight u ζ r - weight u ζ (r + a)) / a

lemma radicand_pos {ζ : ℝ} (hζ : 0 < ζ) (x : ℝ) : 0 < x ^ 2 + ζ ^ 2 := by
  positivity

@[simp] theorem weight_neg (u ζ x : ℝ) : weight u ζ (-x) = weight u ζ x := by
  simp [weight]

@[simp] theorem weight_one (u ζ : ℝ) : weight u ζ 1 = 0 := by simp [weight]
@[simp] theorem weight_neg_one (u ζ : ℝ) : weight u ζ (-1) = 0 := by simp [weight]

theorem weight_lower {u ζ x : ℝ} (hu : 0 ≤ u) (hx : |x| ≤ 1) :
    u * (1 - x ^ 2) ≤ weight u ζ x := by
  have hxx : x ^ 2 ≤ 1 := by rcases abs_le.mp hx with ⟨h₁, h₂⟩; nlinarith
  have hs := Real.sqrt_le_sqrt (show x ^ 2 + ζ ^ 2 ≤ 1 + ζ ^ 2 by linarith)
  unfold weight
  nlinarith [mul_nonneg hu (sub_nonneg.mpr hs)]

theorem weight_pos {u ζ x : ℝ} (hu : 0 < u) (hx : |x| < 1) :
    0 < weight u ζ x := by
  have hxx : x ^ 2 < 1 := by rcases abs_lt.mp hx with ⟨h₁, h₂⟩; nlinarith
  exact lt_of_lt_of_le (mul_pos hu (sub_pos.mpr hxx)) (weight_lower hu.le hx.le)

theorem weight_nonneg {u ζ x : ℝ} (hu : 0 ≤ u) (hx : |x| ≤ 1) :
    0 ≤ weight u ζ x := by
  have hxx : x ^ 2 ≤ 1 := by rcases abs_le.mp hx with ⟨h₁, h₂⟩; nlinarith
  exact (mul_nonneg hu (sub_nonneg.mpr hxx)).trans (weight_lower hu hx)

theorem weight_upper {u ζ : ℝ} (hu : 0 ≤ u) (hζ : 0 ≤ ζ) (x : ℝ) :
    weight u ζ x ≤ 2 * u := by
  have h₁ : Real.sqrt (1 + ζ ^ 2) ≤ 1 + ζ :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have h₂ : ζ ≤ Real.sqrt (x ^ 2 + ζ ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg x])
  have h₃ : 1 - x ^ 2 + Real.sqrt (1 + ζ ^ 2) - Real.sqrt (x ^ 2 + ζ ^ 2) ≤ 2 := by
    nlinarith [sq_nonneg x]
  calc weight u ζ x ≤ u * 2 := mul_le_mul_of_nonneg_left h₃ hu
       _ = 2 * u := by ring

theorem weight_continuous (u ζ : ℝ) : Continuous (weight u ζ) := by
  unfold weight
  fun_prop

theorem weight_contDiff {ζ : ℝ} (hζ : 0 < ζ) (u : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (weight u ζ) := by
  have hs : ContDiff ℝ n (fun x : ℝ => Real.sqrt (x ^ 2 + ζ ^ 2)) :=
    (contDiff_id.pow 2 |>.add contDiff_const).sqrt (fun x => ne_of_gt (radicand_pos hζ x))
  exact contDiff_const.mul (((contDiff_const.sub (contDiff_id.pow 2)).add contDiff_const).sub hs)

theorem secant_formula {u ζ r a : ℝ} (ha : a ≠ 0) :
    secant u ζ r a = u * (2 * r + a) + u / a *
      (Real.sqrt ((r + a) ^ 2 + ζ ^ 2) - Real.sqrt (r ^ 2 + ζ ^ 2)) := by
  unfold secant weight
  field_simp
  <;> ring

theorem secant_lower {u ζ r a : ℝ} (hu : 0 ≤ u) (hζ : 0 ≤ ζ)
    (hr : 0 ≤ r) (ha : 0 < a) (hscale : ζ ≤ a / 10) :
    u * (2 * r + a + 9 / 10) ≤ secant u ζ r a := by
  have h₁ : r + a ≤ Real.sqrt ((r + a) ^ 2 + ζ ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ζ])
  have h₂ : Real.sqrt (r ^ 2 + ζ ^ 2) ≤ r + ζ :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have h₃ : a * (9 / 10) ≤ Real.sqrt ((r + a) ^ 2 + ζ ^ 2) -
      Real.sqrt (r ^ 2 + ζ ^ 2) := by linarith
  rw [secant_formula ha.ne']
  have hmul := mul_le_mul_of_nonneg_left h₃ (div_nonneg hu ha.le)
  have hid : u / a * (a * (9 / 10)) = u * (9 / 10) := by field_simp
  rw [hid] at hmul
  linarith

theorem secant_pos {u ζ r a : ℝ} (hu : 0 < u) (hζ : 0 ≤ ζ)
    (hr : 0 ≤ r) (ha : 0 < a) (hscale : ζ ≤ a / 10) :
    0 < secant u ζ r a := by
  have h := secant_lower hu.le hζ hr ha hscale
  have : 0 < u * (2 * r + a + 9 / 10) := by positivity
  linarith

/-- Supporting-line inequality for the smoothed absolute value. -/
theorem sqrt_support {ζ r a : ℝ} (hζ : 0 < ζ) (hr : 0 ≤ r) (ha : 0 ≤ a) :
    a * r / Real.sqrt (r ^ 2 + ζ ^ 2) ≤
      Real.sqrt ((r + a) ^ 2 + ζ ^ 2) - Real.sqrt (r ^ 2 + ζ ^ 2) := by
  let t := Real.sqrt (r ^ 2 + ζ ^ 2)
  let s := Real.sqrt ((r + a) ^ 2 + ζ ^ 2)
  have ht : 0 < t := Real.sqrt_pos.mpr (radicand_pos hζ r)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = r ^ 2 + ζ ^ 2 := Real.sq_sqrt (radicand_pos hζ r).le
  have hs2 : s ^ 2 = (r + a) ^ 2 + ζ ^ 2 := Real.sq_sqrt (radicand_pos hζ (r + a)).le
  have hid : (t * s) ^ 2 - (t ^ 2 + a * r) ^ 2 = a ^ 2 * ζ ^ 2 := by
    calc
      _ = t ^ 2 * (s ^ 2 - t ^ 2 - 2 * a * r) - a ^ 2 * r ^ 2 := by ring
      _ = a ^ 2 * ζ ^ 2 := by rw [ht2, hs2]; ring
  have hcross : t ^ 2 + a * r ≤ t * s := by
    have hts : 0 ≤ t * s := mul_nonneg ht.le hs
    have htr : 0 ≤ t ^ 2 + a * r := by positivity
    nlinarith [sq_nonneg (a * ζ)]
  change a * r / t ≤ s - t
  apply (div_le_iff₀ ht).mpr
  nlinarith

theorem secant_ge_slope {u ζ r a : ℝ} (hu : 0 ≤ u) (hζ : 0 < ζ)
    (hr : 0 ≤ r) (ha : 0 < a) :
    |slope u ζ r| ≤ secant u ζ r a := by
  have hs : 0 ≤ 2 * r + r / Real.sqrt (r ^ 2 + ζ ^ 2) := by positivity
  have habs : |slope u ζ r| = u * (2 * r + r / Real.sqrt (r ^ 2 + ζ ^ 2)) := by
    unfold slope
    rw [abs_mul, abs_neg, abs_of_nonneg hu, abs_of_nonneg hs]
  rw [habs, secant_formula ha.ne']
  have h := mul_le_mul_of_nonneg_left (sqrt_support hζ hr ha.le) (div_nonneg hu ha.le)
  have hid : u / a * (a * r / Real.sqrt (r ^ 2 + ζ ^ 2)) =
      u * (r / Real.sqrt (r ^ 2 + ζ ^ 2)) := by field_simp
  rw [hid] at h
  nlinarith [mul_nonneg hu ha.le]

@[simp] theorem slope_neg (u ζ x : ℝ) : slope u ζ (-x) = -slope u ζ x := by
  simp only [slope, neg_sq, neg_div]
  ring

theorem abs_slope_abs (u ζ x : ℝ) : |slope u ζ (|x|)| = |slope u ζ x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, slope_neg, abs_neg]

theorem failed_slope_bound {u ζ x a q : ℝ} (hu : 0 ≤ u) (hζ : 0 < ζ)
    (ha : 0 < a) (hq : 0 ≤ q) (hfail : secant u ζ |x| a * q ≤ 1) :
    |slope u ζ x| * q ≤ 1 := by
  have h := secant_ge_slope hu hζ (abs_nonneg x) ha
  rw [abs_slope_abs] at h
  exact (mul_le_mul_of_nonneg_right h hq).trans hfail

theorem failed_probe_bound {u ζ r a q : ℝ} (hu : 0 < u) (hζ : 0 ≤ ζ)
    (hr : 0 ≤ r) (ha : 0 < a) (hscale : ζ ≤ a / 10) (hq : 0 ≤ q)
    (hfail : secant u ζ r a * q ≤ 1) : q ≤ 10 / (9 * u) := by
  have hl := secant_lower hu.le hζ hr ha hscale
  have hl' : 9 / 10 * u ≤ secant u ζ r a := by
    nlinarith [mul_nonneg hu.le hr, mul_nonneg hu.le ha.le]
  have hm := mul_le_mul_of_nonneg_right hl' hq
  apply (le_div_iff₀ (by positivity : 0 < 9 * u)).mpr
  nlinarith

theorem failed_weight_probe_sq_bound {u ζ x a q : ℝ} (hu : 0 < u) (hζ : 0 ≤ ζ)
    (ha : 0 < a) (hscale : ζ ≤ a / 10) (hq : 0 ≤ q)
    (hfail : secant u ζ |x| a * q ≤ 1) :
    weight u ζ x * q ^ 2 ≤ 200 / (81 * u) := by
  have hqmax := failed_probe_bound hu hζ (abs_nonneg x) ha hscale hq hfail
  have hqq : q ^ 2 ≤ (10 / (9 * u)) ^ 2 := by
    exact pow_le_pow_left₀ hq hqmax 2
  calc
    weight u ζ x * q ^ 2 ≤ (2 * u) * q ^ 2 :=
      mul_le_mul_of_nonneg_right (weight_upper hu.le hζ x) (sq_nonneg q)
    _ ≤ (2 * u) * (10 / (9 * u)) ^ 2 := mul_le_mul_of_nonneg_left hqq (by positivity)
    _ = 200 / (81 * u) := by field_simp; norm_num


/-- Linear source decay at the genuine cube boundary. -/
theorem weight_le_gap {u ζ x : ℝ} (hu : 0 ≤ u) (hx : |x| ≤ 1) :
    weight u ζ x ≤ 3 * u * (1 - |x|) := by
  let r := |x|
  have hr : 0 ≤ r := abs_nonneg x
  have hr1 : r ≤ 1 := hx
  have hr2 : r ^ 2 = x ^ 2 := sq_abs x
  let t := Real.sqrt (r ^ 2 + ζ ^ 2)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = r ^ 2 + ζ ^ 2 := Real.sq_sqrt (by positivity)
  have htr : r ≤ t := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ζ])
  have hs : Real.sqrt (1 + ζ ^ 2) ≤ t + (1 - r) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith [mul_nonneg (sub_nonneg.mpr htr) (sub_nonneg.mpr hr1)]
  have hbracket : 1 - r ^ 2 + Real.sqrt (1 + ζ ^ 2) - t ≤ 3 * (1 - r) := by
    nlinarith [sq_nonneg (1 - r)]
  have hm := mul_le_mul_of_nonneg_left hbracket hu
  change u * (1 - x ^ 2 + Real.sqrt (1 + ζ ^ 2) - Real.sqrt (x ^ 2 + ζ ^ 2)) ≤ _
  calc
    _ ≤ u * (3 * (1 - |x|)) := by simpa only [t, hr2, r] using hm
    _ = 3 * u * (1 - |x|) := by ring

/-- The source has a uniform first derivative bound even as smoothing vanishes. -/
theorem abs_slope_le {u ζ x : ℝ} (hu : 0 ≤ u) (hx : |x| ≤ 1) :
    |slope u ζ x| ≤ 3 * u := by
  have hr : 0 ≤ |x| := abs_nonneg x
  have hden : |x| ≤ Real.sqrt (|x| ^ 2 + ζ ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ζ])
  have hquot : |x| / Real.sqrt (|x| ^ 2 + ζ ^ 2) ≤ 1 := div_le_one_of_le₀ hden (by positivity)
  have hsum : 0 ≤ 2 * |x| + |x| / Real.sqrt (|x| ^ 2 + ζ ^ 2) := by positivity
  rw [← abs_slope_abs u ζ x]
  unfold slope
  rw [abs_mul, abs_neg, abs_of_nonneg hu, abs_of_nonneg hsum]
  have hm := mul_le_mul_of_nonneg_left (show 2 * |x| + |x| / Real.sqrt (|x| ^ 2 + ζ ^ 2) ≤ 3 by linarith) hu
  nlinarith

end Source
end SeamlessKS
