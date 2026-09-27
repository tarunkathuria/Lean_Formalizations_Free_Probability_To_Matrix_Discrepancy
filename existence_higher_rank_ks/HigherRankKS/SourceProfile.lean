import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-!
# The scalar higher-rank source profile

This file proves the calculus of the actual real-power function used in
Part III, including its endpoint behavior and its owner cancellation.
Derivatives are derived from `Real.rpow`, rather than supplied as hypotheses.
-/

noncomputable section

namespace HigherRankKS.SourceProfile

open Set Filter
open scoped Topology

def gap (x : ℝ) : ℝ := 1 - x ^ 2

def kappa (β : ℝ) : ℝ := β / (2 + 3 * β)

def ownerScale (β : ℝ) : ℝ := 100 / β

def weight (u κ x : ℝ) : ℝ := u / κ * (gap x) ^ κ

def slope (u κ x : ℝ) : ℝ := -2 * u * x * (gap x) ^ (κ - 1)

def curvature (u κ x : ℝ) : ℝ :=
  -2 * u * (gap x) ^ (κ - 1) +
    4 * u * (κ - 1) * x ^ 2 * (gap x) ^ (κ - 2)

def owner (β : ℝ) : ℝ → ℝ := weight (ownerScale β) (kappa β)

lemma kappa_pos {β : ℝ} (hβ : 0 < β) : 0 < kappa β := by
  unfold kappa
  positivity

lemma kappa_lt_one {β : ℝ} (hβ : 0 < β) : kappa β < 1 := by
  unfold kappa
  rw [div_lt_one (by positivity)]
  linarith

lemma ownerScale_pos {β : ℝ} (hβ : 0 < β) : 0 < ownerScale β := by
  unfold ownerScale
  positivity

lemma gap_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < gap x := by
  have h : 0 < (1 - x) * (1 + x) := mul_pos (by linarith [hx.2]) (by linarith [hx.1])
  unfold gap
  nlinarith

lemma gap_nonneg {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : 0 ≤ gap x := by
  have h : 0 ≤ (1 - x) * (1 + x) :=
    mul_nonneg (by linarith [hx.2]) (by linarith [hx.1])
  unfold gap
  nlinarith

lemma gap_le_one (x : ℝ) : gap x ≤ 1 := by
  unfold gap
  nlinarith [sq_nonneg x]

lemma continuous_weight (u : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) : Continuous (weight u κ) := by
  unfold weight gap
  exact continuous_const.mul ((Real.continuous_rpow_const hκ).comp
    (continuous_const.sub (continuous_id.pow 2)))

theorem continuousOn_owner {β : ℝ} (hβ : 0 < β) :
    ContinuousOn (owner β) (Icc (-1 : ℝ) 1) :=
  (continuous_weight _ (kappa_pos hβ).le).continuousOn

/-- Coordinate sources remain continuous on the entire coefficient cube. -/
theorem continuous_coordinate_owner {ι : Type*} {β : ℝ} (hβ : 0 < β) (i : ι) :
    Continuous (fun x : ι → ℝ => owner β (x i)) :=
  (continuous_weight _ (kappa_pos hβ).le).comp (continuous_apply i)

theorem contDiffOn_weight (u κ : ℝ) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (weight u κ) (Ioo (-1 : ℝ) 1) := by
  have hg : ContDiff ℝ n gap := by unfold gap; fun_prop
  exact contDiffOn_const.mul (hg.contDiffOn.rpow_const_of_ne
    (fun _ hx => (gap_pos hx).ne'))

theorem contDiffOn_owner (β : ℝ) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (owner β) (Ioo (-1 : ℝ) 1) := contDiffOn_weight _ _ n

@[simp] theorem weight_one (u : ℝ) {κ : ℝ} (hκ : κ ≠ 0) : weight u κ 1 = 0 := by
  simp [weight, gap, Real.zero_rpow hκ]

@[simp] theorem weight_neg_one (u : ℝ) {κ : ℝ} (hκ : κ ≠ 0) : weight u κ (-1) = 0 := by
  simp [weight, gap, Real.zero_rpow hκ]

@[simp] theorem owner_one {β : ℝ} (hβ : 0 < β) : owner β 1 = 0 :=
  weight_one _ (kappa_pos hβ).ne'

@[simp] theorem owner_neg_one {β : ℝ} (hβ : 0 < β) : owner β (-1) = 0 :=
  weight_neg_one _ (kappa_pos hβ).ne'

lemma weight_pos {u κ x : ℝ} (hu : 0 < u) (hκ : 0 < κ)
    (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < weight u κ x := by
  exact mul_pos (div_pos hu hκ) (Real.rpow_pos_of_pos (gap_pos hx) _)

theorem owner_pos {β x : ℝ} (hβ : 0 < β) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < owner β x := weight_pos (ownerScale_pos hβ) (kappa_pos hβ) hx

lemma weight_nonneg {u κ x : ℝ} (hu : 0 ≤ u) (hκ : 0 ≤ κ)
    (hx : x ∈ Icc (-1 : ℝ) 1) : 0 ≤ weight u κ x := by
  exact mul_nonneg (div_nonneg hu hκ) (Real.rpow_nonneg (gap_nonneg hx) _)

@[simp] lemma weight_zero (u κ : ℝ) : weight u κ 0 = u / κ := by
  simp [weight, gap]

lemma weight_le_at_zero {u κ x : ℝ} (hu : 0 ≤ u) (hκ : 0 ≤ κ)
    (hx : x ∈ Icc (-1 : ℝ) 1) : weight u κ x ≤ weight u κ 0 := by
  rw [weight_zero]
  have hp := Real.rpow_le_one (gap_nonneg hx) (gap_le_one x) hκ
  simpa [weight] using mul_le_mul_of_nonneg_left hp (div_nonneg hu hκ)

theorem owner_at_zero {β : ℝ} (hβ : 0 < β) :
    owner β 0 = 200 / β ^ 2 + 300 / β := by
  simp only [owner, weight_zero, ownerScale, kappa]
  field_simp
  ring

theorem owner_at_zero_le {β : ℝ} (hβ : 0 < β) (hβhalf : β ≤ 1 / 2) :
    owner β 0 ≤ 350 / β ^ 2 := by
  rw [owner_at_zero hβ]
  apply (le_div_iff₀ (sq_pos_of_pos hβ)).2
  have heq : (200 / β ^ 2 + 300 / β) * β ^ 2 = 200 + 300 * β := by
    field_simp
  rw [heq]
  linarith

lemma hasDerivAt_gap (x : ℝ) : HasDerivAt gap (-2 * x) x := by
  convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1
  simp

theorem hasDerivAt_weight (u : ℝ) {κ x : ℝ} (hκ : κ ≠ 0)
    (hx : x ∈ Ioo (-1 : ℝ) 1) : HasDerivAt (weight u κ) (slope u κ x) x := by
  convert ((hasDerivAt_gap x).rpow_const (Or.inl (gap_pos hx).ne')).const_mul (u / κ)
    using 1
  unfold slope
  field_simp

theorem deriv_weight (u : ℝ) {κ x : ℝ} (hκ : κ ≠ 0)
    (hx : x ∈ Ioo (-1 : ℝ) 1) : deriv (weight u κ) x = slope u κ x :=
  (hasDerivAt_weight u hκ hx).deriv

theorem hasDerivAt_slope (u κ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (slope u κ) (curvature u κ x) x := by
  have hp := (hasDerivAt_gap x).rpow_const (p := κ - 1) (Or.inl (gap_pos hx).ne')
  convert ((hasDerivAt_id x).mul hp).const_mul (-2 * u) using 1
  · ext t
    simp [slope]
    ring
  · simp only [curvature, id_eq, show κ - 1 - 1 = κ - 2 by ring]
    ring

theorem hasDerivAt_deriv_weight (u : ℝ) {κ x : ℝ} (hκ : κ ≠ 0)
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (deriv (weight u κ)) (curvature u κ x) x := by
  have heq : deriv (weight u κ) =ᶠ[𝓝 x] slope u κ := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact deriv_weight u hκ hy
  exact (hasDerivAt_slope u κ hx).congr_of_eventuallyEq heq

theorem second_deriv_weight (u : ℝ) {κ x : ℝ} (hκ : κ ≠ 0)
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    deriv (deriv (weight u κ)) x = curvature u κ x :=
  (hasDerivAt_deriv_weight u hκ hx).deriv

lemma rpow_sub_two {a : ℝ} (ha : 0 < a) (κ : ℝ) :
    a ^ (κ - 2) = a ^ κ / a ^ (2 : ℕ) := by
  rw [Real.rpow_sub ha, Real.rpow_two]

/-- Exact cancellation for any nonzero exponent, prior to fixing the beta scale. -/
theorem cancellation {u κ x : ℝ} (hu : u ≠ 0) (hκ : κ ≠ 0)
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    -curvature u κ x - ((1 - κ) / κ) * (slope u κ x) ^ 2 / weight u κ x =
      2 * u * (gap x) ^ (κ - 1) := by
  have hf := (gap_pos hx).ne'
  have hp := (Real.rpow_pos_of_pos (gap_pos hx) κ).ne'
  unfold curvature slope weight
  rw [Real.rpow_sub_one hf, rpow_sub_two (gap_pos hx)]
  field_simp
  ring

lemma cancellation_coefficient {β : ℝ} (hβ : 0 < β) :
    (1 - kappa β) / kappa β = 2 * (1 - β) / β + 4 := by
  unfold kappa
  have hden : 2 + 3 * β ≠ 0 := by positivity
  field_simp
  ring


theorem owner_cancellation {β x : ℝ} (hβ : 0 < β)
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    -deriv (deriv (owner β)) x - (2 * (1 - β) / β + 4) *
      (deriv (owner β) x) ^ 2 / owner β x =
        2 * ownerScale β * (gap x) ^ (kappa β - 1) := by
  unfold owner
  rw [second_deriv_weight _ (kappa_pos hβ).ne' hx,
    deriv_weight _ (kappa_pos hβ).ne' hx, ← cancellation_coefficient hβ]
  exact cancellation (ownerScale_pos hβ).ne' (kappa_pos hβ).ne' hx

theorem owner_cancellation_lower {β x : ℝ} (hβ : 0 < β)
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    2 * ownerScale β ≤ -deriv (deriv (owner β)) x - (2 * (1 - β) / β + 4) *
      (deriv (owner β) x) ^ 2 / owner β x := by
  rw [owner_cancellation hβ hx]
  have hp : 1 ≤ (gap x) ^ (kappa β - 1) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (gap_pos hx) (gap_le_one x)
      (by linarith [kappa_lt_one hβ])
  nlinarith [ownerScale_pos hβ]

lemma curvature_nonpos {u κ x : ℝ} (hu : 0 ≤ u) (hκ : κ ≤ 1)
    (hx : x ∈ Ioo (-1 : ℝ) 1) : curvature u κ x ≤ 0 := by
  have hfirst : -2 * u * (gap x) ^ (κ - 1) ≤ 0 := by
    have hp := (Real.rpow_pos_of_pos (gap_pos hx) (κ - 1)).le
    nlinarith
  have hsecond : 4 * u * (κ - 1) * x ^ 2 * (gap x) ^ (κ - 2) ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · apply mul_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      · positivity
    · exact (Real.rpow_pos_of_pos (gap_pos hx) _).le
  exact add_nonpos hfirst hsecond

theorem concaveOn_weight {u κ : ℝ} (hu : 0 ≤ u) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ConcaveOn ℝ (Icc (-1 : ℝ) 1) (weight u κ) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (continuous_weight u hκ.le).continuousOn
      (f' := slope u κ) (f'' := curvature u κ)
  · intro x hx
    exact (hasDerivAt_weight u hκ.ne' (by simpa using hx)).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_slope u κ (by simpa using hx)).hasDerivWithinAt
  · intro x hx
    exact curvature_nonpos hu hκ1 (by simpa using hx)

theorem concaveOn_owner {β : ℝ} (hβ : 0 < β) :
    ConcaveOn ℝ (Icc (-1 : ℝ) 1) (owner β) :=
  concaveOn_weight (ownerScale_pos hβ).le (kappa_pos hβ) (kappa_lt_one hβ).le

def endpointDistance (x : ℝ) : ℝ := 1 - |x|

lemma endpointDistance_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < endpointDistance x := by
  unfold endpointDistance
  have : |x| < 1 := abs_lt.mpr hx
  linarith

lemma gap_factor (x : ℝ) : gap x = (1 - |x|) * (1 + |x|) := by
  unfold gap
  nlinarith [sq_abs x]

lemma endpointDistance_sq_le_power {κ x : ℝ} (hκ1 : κ ≤ 1)
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    endpointDistance x ^ 2 ≤ (gap x) ^ κ := by
  have habs : |x| < 1 := abs_lt.mpr hx
  have hsq : endpointDistance x ^ 2 ≤ gap x := by
    rw [gap_factor]
    unfold endpointDistance
    nlinarith [abs_nonneg x, mul_nonneg (sub_nonneg.mpr habs.le) (abs_nonneg x)]
  have hp : gap x ≤ (gap x) ^ κ := by
    simpa using Real.rpow_le_rpow_of_exponent_ge (gap_pos hx) (gap_le_one x) hκ1
  exact hsq.trans hp

lemma endpoint_slope_ratio {u κ x : ℝ} (hu : 0 < u) (hκ : 0 < κ)
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    endpointDistance x * |slope u κ x| / weight u κ x =
      2 * κ * |x| / (1 + |x|) := by
  have hf := (gap_pos hx).ne'
  have hp := (Real.rpow_pos_of_pos (gap_pos hx) κ).ne'
  have hs : |slope u κ x| = 2 * u * |x| * (gap x) ^ (κ - 1) := by
    simp [slope, abs_mul, abs_of_pos hu,
      abs_of_pos (Real.rpow_pos_of_pos (gap_pos hx) (κ - 1))]
  rw [hs]
  unfold weight endpointDistance
  rw [Real.rpow_sub_one hf]
  have hplus : 1 + |x| ≠ 0 := by positivity
  have hminus : 1 - |x| ≠ 0 := (endpointDistance_pos hx).ne'
  rw [gap_factor x] at hf hp ⊢
  field_simp [hp]

lemma endpoint_slope_cap {u κ x : ℝ} (hu : 0 < u) (hκ : 0 < κ)
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    endpointDistance x * |slope u κ x| ≤ κ * weight u κ x := by
  have hr := endpoint_slope_ratio hu hκ hx
  have hc := weight_pos hu hκ hx
  have habs : |x| ≤ 1 := (abs_lt.mpr hx).le
  have hd : 0 < 1 + |x| := by positivity
  have hratio : endpointDistance x * |slope u κ x| / weight u κ x ≤ κ := by
    rw [hr, div_le_iff₀ hd]
    nlinarith
  exact (div_le_iff₀ hc).mp hratio

lemma kappa_div_beta_lt_one {β : ℝ} (hβ : 0 < β) : kappa β / β < 1 := by
  unfold kappa
  have hid : β / (2 + 3 * β) / β = 1 / (2 + 3 * β) := by field_simp
  rw [hid, div_lt_one (by positivity)]
  linarith

lemma cap_scale_bound {β : ℝ} (hβ : 0 < β) : kappa β / β ^ 2 ≤ 1 / (2 * β) := by
  unfold kappa
  apply (div_le_div_iff₀ (sq_pos_of_pos hβ) (by positivity)).2
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 2 + 3 * β)).2
  nlinarith [mul_pos (sq_pos_of_pos hβ) hβ]

/-- Failure of the finite endpoint certificate bounds the scalarized center force. -/
theorem failed_endpoint_slope_cap {u κ β x q : ℝ} (hu : 0 < u) (hκ : 0 < κ)
    (hβ : 0 < β) (hq : 0 ≤ q) (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hfail : β * weight u κ x * q < endpointDistance x) :
    |-(slope u κ x) * q| ≤ κ / β := by
  have hc := weight_pos hu hκ hx
  have hmain : weight u κ x * (β * |slope u κ x| * q) ≤ weight u κ x * κ := by
    calc
      weight u κ x * (β * |slope u κ x| * q) =
          (β * weight u κ x * q) * |slope u κ x| := by ring
      _ ≤ endpointDistance x * |slope u κ x| :=
        mul_le_mul_of_nonneg_right hfail.le (abs_nonneg _)
      _ ≤ κ * weight u κ x := endpoint_slope_cap hu hκ hx
      _ = weight u κ x * κ := by ring
  have hh := (mul_le_mul_iff_right₀ hc).mp hmain
  rw [abs_mul, abs_neg, abs_of_nonneg hq]
  apply (le_div_iff₀ hβ).2
  nlinarith

/-- Failure of the same certificate bounds the squared transport coefficient. -/
theorem failed_endpoint_square_cap {u κ β x q : ℝ} (hu : 0 < u) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hβ : 0 < β) (hq : 0 ≤ q) (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hfail : β * weight u κ x * q < endpointDistance x) :
    (Real.sqrt (weight u κ x) * q) ^ 2 ≤ (κ / β ^ 2) / u := by
  have hc := weight_pos hu hκ hx
  have ha := endpointDistance_pos hx
  have hb : 0 ≤ β * weight u κ x * q := by positivity
  have hs : (β * weight u κ x * q) ^ 2 ≤ (gap x) ^ κ := by
    apply le_trans _ (endpointDistance_sq_le_power hκ1 hx)
    nlinarith [mul_nonneg (sub_nonneg.mpr hfail.le) (show
      0 ≤ endpointDistance x + β * weight u κ x * q by positivity)]
  have hmain : weight u κ x * (weight u κ x * q ^ 2 * (β ^ 2 * u)) ≤
      weight u κ x * κ := by
    calc
      weight u κ x * (weight u κ x * q ^ 2 * (β ^ 2 * u)) =
          u * (β * weight u κ x * q) ^ 2 := by ring
      _ ≤ u * (gap x) ^ κ := mul_le_mul_of_nonneg_left hs hu.le
      _ = weight u κ x * κ := by
        unfold weight
        field_simp
  have hh := (mul_le_mul_iff_right₀ hc).mp hmain
  rw [mul_pow, Real.sq_sqrt hc.le, div_div]
  exact (le_div_iff₀ (mul_pos (sq_pos_of_pos hβ) hu)).2 hh


theorem failed_endpoint_caps {β x q : ℝ} (hβ : 0 < β) (hq : 0 ≤ q)
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hfail : β * owner β x * q < endpointDistance x) :
    |-(deriv (owner β) x) * q| ≤ kappa β / β ∧
      kappa β / β < 1 ∧
      (Real.sqrt (owner β x) * q) ^ 2 ≤ (kappa β / β ^ 2) / ownerScale β ∧
      kappa β / β ^ 2 ≤ 1 / (2 * β) := by
  refine ⟨?_, kappa_div_beta_lt_one hβ, ?_, cap_scale_bound hβ⟩
  · unfold owner
    rw [deriv_weight _ (kappa_pos hβ).ne' hx]
    exact failed_endpoint_slope_cap (ownerScale_pos hβ) (kappa_pos hβ) hβ hq hx hfail
  · exact failed_endpoint_square_cap (ownerScale_pos hβ) (kappa_pos hβ)
      (kappa_lt_one hβ).le hβ hq hx hfail

end HigherRankKS.SourceProfile
