import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Scalar parameters for the rectangular Tsallis construction

Only real-variable bookkeeping is proved here. In particular this module
does not assume or assert a matrix response, epoch, or signing theorem.
The physical dimension `D` includes the signed doubling; `n` counts the
original coefficient labels. The exponent and strength are fixed globally.
-/

noncomputable section
namespace MatrixSpencer.RectangularParameters

def aspect (D n : ℝ) : ℝ := max 1 (D / n)

def order (D n : ℝ) : ℕ := max 2 ⌈Real.log (aspect D n)⌉₊

def exponent (D n : ℝ) : ℝ := 1 / (order D n : ℝ)

lemma aspect_one_le (D n : ℝ) : 1 ≤ aspect D n := le_max_left _ _

lemma aspect_pos (D n : ℝ) : 0 < aspect D n := lt_of_lt_of_le zero_lt_one (aspect_one_le D n)

lemma log_aspect_nonneg (D n : ℝ) : 0 ≤ Real.log (aspect D n) :=
  Real.log_nonneg (aspect_one_le D n)

lemma order_two_le (D n : ℝ) : 2 ≤ order D n := le_max_left _ _

lemma order_pos (D n : ℝ) : 0 < (order D n : ℝ) := by
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) (order_two_le D n))

lemma log_aspect_le_order (D n : ℝ) : Real.log (aspect D n) ≤ order D n := by
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))

lemma order_le_two_add_log (D n : ℝ) :
    (order D n : ℝ) ≤ 2 + Real.log (aspect D n) := by
  rw [order, Nat.cast_max]
  apply max_le
  · norm_num
    exact log_aspect_nonneg D n
  · have h := Nat.ceil_lt_add_one (log_aspect_nonneg D n)
    linarith

lemma exponent_pos (D n : ℝ) : 0 < exponent D n := one_div_pos.mpr (order_pos D n)

lemma exponent_le_half (D n : ℝ) : exponent D n ≤ 1 / 2 := by
  apply one_div_le_one_div_of_le (by norm_num)
  exact_mod_cast order_two_le D n

lemma one_sub_exponent_half_le (D n : ℝ) : 1 / 2 ≤ 1 - exponent D n := by
  linarith [exponent_le_half D n]

lemma aspect_rpow_exponent_le_exp (D n : ℝ) :
    (aspect D n) ^ exponent D n ≤ Real.exp 1 := by
  rw [Real.rpow_def_of_pos (aspect_pos D n)]
  apply Real.exp_le_exp.mpr
  simpa only [exponent, mul_one_div] using
    (div_le_one (order_pos D n)).mpr (log_aspect_le_order D n)

lemma aspect_rpow_exponent_le_three (D n : ℝ) :
    (aspect D n) ^ exponent D n ≤ 3 := by
  exact (aspect_rpow_exponent_le_exp D n).trans (by linarith [Real.exp_one_lt_d9])

lemma cap_rpow_le_sixtyfour {q : ℝ} (hq : q ≤ 1 / 2) : (4096 : ℝ) ^ q ≤ 64 := by
  calc
    (4096 : ℝ) ^ q ≤ 4096 ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hq
    _ = 64 := by rw [← Real.sqrt_eq_rpow]; norm_num

/-- The globally balanced strength, including the exact regularizer factor. -/
def strength (D n q : ℝ) : ℝ :=
  Real.sqrt ((1 - q) * (4096 : ℝ) ^ q * n ^ (1 - q) / (q * D ^ q))

lemma strength_pos {D n q : ℝ} (hD : 0 < D) (hn : 0 < n)
    (hq : 0 < q) (hq1 : q < 1) : 0 < strength D n q := by
  apply Real.sqrt_pos.mpr
  exact div_pos (mul_pos (mul_pos (sub_pos.mpr hq1) (Real.rpow_pos_of_pos (by norm_num) _))
    (Real.rpow_pos_of_pos hn _)) (mul_pos hq (Real.rpow_pos_of_pos hD _))

lemma strength_sq {D n q : ℝ} (hD : 0 < D) (hn : 0 < n)
    (hq : 0 < q) (hq1 : q < 1) :
    strength D n q ^ 2 = (1 - q) * (4096 : ℝ) ^ q * n ^ (1 - q) / (q * D ^ q) := by
  apply Real.sq_sqrt
  exact le_of_lt (div_pos (mul_pos (mul_pos (sub_pos.mpr hq1)
    (Real.rpow_pos_of_pos (by norm_num) _)) (Real.rpow_pos_of_pos hn _))
    (mul_pos hq (Real.rpow_pos_of_pos hD _)))

lemma strength_balances {D n q : ℝ} (hD : 0 < D) (hn : 0 < n)
    (hq : 0 < q) (hq1 : q < 1) :
    strength D n q * D ^ q / (1 - q) =
      (4096 : ℝ) ^ q * n ^ (1 - q) / (strength D n q * q) := by
  have ht := strength_pos hD hn hq hq1
  have hd := Real.rpow_pos_of_pos hD q
  have hsub : 0 < 1 - q := sub_pos.mpr hq1
  have hs := strength_sq hD hn hq hq1
  field_simp at hs ⊢
  nlinarith

lemma power_product_aspect {D n q : ℝ} (hD : 0 < D) (hn : 0 < n) :
    n ^ (1 - q) * D ^ q = n * (D / n) ^ q := by
  rw [Real.rpow_sub hn, Real.rpow_one, Real.div_rpow hD.le hn.le]
  ring

lemma balanced_term_sq {D n q : ℝ} (hD : 0 < D) (hn : 0 < n)
    (hq : 0 < q) (hq1 : q < 1) :
    (strength D n q * D ^ q / (1 - q)) ^ 2 =
      (4096 : ℝ) ^ q * n * (D / n) ^ q / (q * (1 - q)) := by
  have hsub : 0 < 1 - q := sub_pos.mpr hq1
  have ht := strength_pos hD hn hq hq1
  calc
    _ = (strength D n q * D ^ q / (1 - q)) *
        ((4096 : ℝ) ^ q * n ^ (1 - q) / (strength D n q * q)) := by
      rw [← strength_balances hD hn hq hq1, pow_two]
    _ = (4096 : ℝ) ^ q * (n ^ (1 - q) * D ^ q) / (q * (1 - q)) := by
      field_simp
    _ = _ := by rw [power_product_aspect hD hn]; ring

lemma balanced_term_sq_le_of_reciprocal {D n p : ℝ} (hD : 0 < D) (hn : 0 < n)
    (hp : 2 ≤ p) (hlogp : Real.log (aspect D n) ≤ p)
    (hupper : p ≤ 4 * (1 + Real.log (aspect D n))) :
    (strength D n (1 / p) * D ^ (1 / p) / (1 - 1 / p)) ^ 2 ≤
      1536 * (n * (1 + Real.log (aspect D n))) := by
  let q := 1 / p
  have hp0 : 0 < p := by linarith
  have hq : 0 < q := one_div_pos.mpr hp0
  have hqh : q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp
  have hq1 : q < 1 := by linarith
  have hr0 : 0 ≤ (D / n) ^ q := Real.rpow_nonneg (div_nonneg hD.le hn.le) _
  have haspect : (aspect D n) ^ q ≤ 3 := by
    calc
      (aspect D n) ^ q ≤ Real.exp 1 := by
        rw [Real.rpow_def_of_pos (aspect_pos D n)]
        apply Real.exp_le_exp.mpr
        simpa only [q, mul_one_div] using (div_le_one hp0).mpr hlogp
      _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hr : (D / n) ^ q ≤ 3 :=
    (Real.rpow_le_rpow (div_nonneg hD.le hn.le) (le_max_right _ _) hq.le).trans
      haspect
  have hL0 : 0 ≤ (4096 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
  have hL : (4096 : ℝ) ^ q ≤ 64 := cap_rpow_le_sixtyfour hqh
  have hprod : (4096 : ℝ) ^ q * (D / n) ^ q ≤ 192 := by nlinarith
  have hden : p / (1 - q) ≤ 2 * p := by
    apply (div_le_iff₀ (sub_pos.mpr hq1)).mpr
    nlinarith
  have hlog := log_aspect_nonneg D n
  have hinv : p / (1 - q) ≤ 8 * (1 + Real.log (aspect D n)) := by
    linarith
  have he : (4096 : ℝ) ^ q * n * (D / n) ^ q / (q * (1 - q)) =
      ((4096 : ℝ) ^ q * (D / n) ^ q) * n * (p / (1 - q)) := by
    dsimp only [q]
    field_simp
  rw [balanced_term_sq hD hn hq hq1]
  change (4096 : ℝ) ^ q * n * (D / n) ^ q / (q * (1 - q)) ≤ _
  rw [he]
  calc
    _ ≤ 192 * n * (8 * (1 + Real.log (aspect D n))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hprod hn.le
      · exact hinv
      · exact div_nonneg hp0.le (sub_pos.mpr hq1).le
      · positivity
    _ = _ := by ring

/-- The optimized complete scalar budget has square-root logarithmic growth. -/
theorem optimized_budget_le_of_reciprocal {D n p : ℝ} (hD : 0 < D) (hn : 0 < n)
    (hp : 2 ≤ p) (hlogp : Real.log (aspect D n) ≤ p)
    (hupper : p ≤ 4 * (1 + Real.log (aspect D n))) :
    Real.sqrt n + strength D n (1 / p) * D ^ (1 / p) / (1 - 1 / p) +
      (4096 : ℝ) ^ (1 / p) * n ^ (1 - 1 / p) /
        (strength D n (1 / p) * (1 / p)) ≤
      81 * Real.sqrt (n * (1 + Real.log (aspect D n))) := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < 1 / p := one_div_pos.mpr hp0
  have hqh : 1 / p ≤ (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hp
  have hq1 : 1 / p < 1 := by linarith
  have hs := balanced_term_sq_le_of_reciprocal hD hn hp hlogp hupper
  have hlog := log_aspect_nonneg D n
  have hb : 0 ≤ n * (1 + Real.log (aspect D n)) := by positivity
  have hsqrt := Real.sq_sqrt hb
  have ht : 0 ≤ strength D n (1 / p) * D ^ (1 / p) / (1 - 1 / p) :=
    div_nonneg (mul_nonneg (strength_pos hD hn hq hq1).le (Real.rpow_nonneg hD.le _))
      (sub_pos.mpr hq1).le
  have htbound : strength D n (1 / p) * D ^ (1 / p) /
      (1 - 1 / p) ≤ 40 * Real.sqrt (n * (1 + Real.log (aspect D n))) := by
    nlinarith [Real.sqrt_nonneg (n * (1 + Real.log (aspect D n)))]
  have hnle : n ≤ n * (1 + Real.log (aspect D n)) := by nlinarith
  have hroot := Real.sqrt_le_sqrt hnle
  rw [← strength_balances hD hn hq hq1]
  linarith

theorem optimized_budget_le {D n : ℝ} (hD : 0 < D) (hn : 0 < n) :
    Real.sqrt n + strength D n (exponent D n) * D ^ exponent D n / (1 - exponent D n) +
      (4096 : ℝ) ^ exponent D n * n ^ (1 - exponent D n) /
        (strength D n (exponent D n) * exponent D n) ≤
      81 * Real.sqrt (n * (1 + Real.log (aspect D n))) := by
  apply optimized_budget_le_of_reciprocal hD hn
  · exact_mod_cast order_two_le D n
  · exact log_aspect_le_order D n
  · linarith [order_le_two_add_log D n, log_aspect_nonneg D n]

/-- Dyadic orders allow the matrix powers to be built by repeated square roots. -/
def dyadicDepth (D n : ℝ) : ℕ := Nat.log 2 (order D n) + 1

def dyadicOrder (D n : ℝ) : ℕ := 2 ^ dyadicDepth D n

lemma dyadicDepth_pos (D n : ℝ) : 0 < dyadicDepth D n := Nat.succ_pos _

lemma order_le_dyadicOrder (D n : ℝ) : order D n ≤ dyadicOrder D n :=
  (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (order D n)).le

lemma dyadicOrder_le_twice_order (D n : ℝ) : dyadicOrder D n ≤ 2 * order D n := by
  have hpos : order D n ≠ 0 := by have := order_two_le D n; omega
  have h := Nat.pow_log_le_self 2 hpos
  dsimp only [dyadicOrder, dyadicDepth]
  rw [pow_succ]
  omega

lemma dyadicOrder_two_le (D n : ℝ) : 2 ≤ dyadicOrder D n :=
  (order_two_le D n).trans (order_le_dyadicOrder D n)

lemma dyadic_reciprocal_pos (D n : ℝ) : 0 < 1 / (dyadicOrder D n : ℝ) := by
  apply one_div_pos.mpr
  have h : (2 : ℝ) ≤ dyadicOrder D n := by exact_mod_cast dyadicOrder_two_le D n
  linarith

lemma dyadic_reciprocal_le_half (D n : ℝ) : 1 / (dyadicOrder D n : ℝ) ≤ 1 / 2 := by
  apply one_div_le_one_div_of_le (by norm_num)
  exact_mod_cast dyadicOrder_two_le D n

lemma dyadic_reciprocal_eq (D n : ℝ) :
    1 / (dyadicOrder D n : ℝ) = (1 / 2 : ℝ) ^ dyadicDepth D n := by
  simp only [dyadicOrder, Nat.cast_pow, Nat.cast_ofNat, one_div_pow]

lemma log_aspect_le_dyadicOrder (D n : ℝ) :
    Real.log (aspect D n) ≤ dyadicOrder D n :=
  (log_aspect_le_order D n).trans (Nat.cast_le.mpr (order_le_dyadicOrder D n))

lemma dyadicOrder_le_four_add_two_log (D n : ℝ) :
    (dyadicOrder D n : ℝ) ≤ 4 + 2 * Real.log (aspect D n) := by
  have h : (dyadicOrder D n : ℝ) ≤ 2 * order D n := by
    exact_mod_cast dyadicOrder_le_twice_order D n
  linarith [order_le_two_add_log D n]

theorem dyadic_optimized_budget_le {D n : ℝ} (hD : 0 < D) (hn : 0 < n) :
    Real.sqrt n + strength D n (1 / (dyadicOrder D n : ℝ)) * D ^ (1 / (dyadicOrder D n : ℝ)) /
      (1 - 1 / (dyadicOrder D n : ℝ)) +
      (4096 : ℝ) ^ (1 / (dyadicOrder D n : ℝ)) * n ^ (1 - 1 / (dyadicOrder D n : ℝ)) /
        (strength D n (1 / (dyadicOrder D n : ℝ)) * (1 / (dyadicOrder D n : ℝ))) ≤
      81 * Real.sqrt (n * (1 + Real.log (aspect D n))) := by
  apply optimized_budget_le_of_reciprocal hD hn
  · exact_mod_cast dyadicOrder_two_le D n
  · exact log_aspect_le_dyadicOrder D n
  · linarith [dyadicOrder_le_four_add_two_log D n, log_aspect_nonneg D n]

/-- After signed doubling, the unregularized logarithm already stays away from zero. -/
lemma sqrt_regularized_log_le {D n : ℝ} (hn : 0 < n) (hDn : 2 * n ≤ D) :
    Real.sqrt (n * (1 + Real.log (aspect D n))) ≤
      2 * Real.sqrt (n * Real.log (D / n)) := by
  have hr : (2 : ℝ) ≤ D / n := (le_div_iff₀ hn).mpr hDn
  have ha : aspect D n = D / n := max_eq_right (by linarith)
  have hlog : 1 / 2 ≤ Real.log (D / n) := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hr
    linarith [Real.log_two_gt_d9]
  rw [ha]
  have hleft : 0 ≤ n * (1 + Real.log (D / n)) := by positivity
  have hright : 0 ≤ n * Real.log (D / n) := by positivity
  have hsleft := Real.sq_sqrt hleft
  have hsright := Real.sq_sqrt hright
  nlinarith [Real.sqrt_nonneg (n * (1 + Real.log (D / n))),
    Real.sqrt_nonneg (n * Real.log (D / n))]

theorem dyadic_rectangular_budget_le {D n : ℝ} (hn : 0 < n) (hDn : 2 * n ≤ D) :
    Real.sqrt n + strength D n (1 / (dyadicOrder D n : ℝ)) * D ^ (1 / (dyadicOrder D n : ℝ)) /
      (1 - 1 / (dyadicOrder D n : ℝ)) +
      (4096 : ℝ) ^ (1 / (dyadicOrder D n : ℝ)) * n ^ (1 - 1 / (dyadicOrder D n : ℝ)) /
        (strength D n (1 / (dyadicOrder D n : ℝ)) * (1 / (dyadicOrder D n : ℝ))) ≤
      162 * Real.sqrt (n * Real.log (D / n)) := by
  have hD : 0 < D := by linarith
  have hb := dyadic_optimized_budget_le hD hn
  have hs := sqrt_regularized_log_le hn hDn
  linarith

/-- The reciprocal epoch duration absorbs a possibly large response coefficient. -/
def epochRate (q θ k : ℝ) : ℝ :=
  3 + 6 * (4096 : ℝ) ^ q / (θ * q) * k ^ (1 / 2 - q)

def epochDuration (q θ k : ℝ) : ℝ := 1 / epochRate q θ k

lemma epochRate_three_le {q θ k : ℝ} (hq : 0 < q) (hθ : 0 < θ) (hk : 0 ≤ k) :
    3 ≤ epochRate q θ k := by
  have h : 0 ≤ 6 * (4096 : ℝ) ^ q / (θ * q) * k ^ (1 / 2 - q) := by positivity
  dsimp only [epochRate]
  linarith

lemma epochDuration_pos {q θ k : ℝ} (hq : 0 < q) (hθ : 0 < θ) (hk : 0 ≤ k) :
    0 < epochDuration q θ k := by
  apply one_div_pos.mpr
  linarith [epochRate_three_le hq hθ hk]

lemma epochDuration_le_third {q θ k : ℝ} (hq : 0 < q) (hθ : 0 < θ) (hk : 0 ≤ k) :
    epochDuration q θ k ≤ 1 / 3 :=
  one_div_le_one_div_of_le (by norm_num) (epochRate_three_le hq hθ hk)

lemma epochRate_mono {q θ k l : ℝ} (hq : 0 < q) (hqh : q ≤ 1 / 2)
    (hθ : 0 < θ) (hk : 0 ≤ k) (hkl : k ≤ l) : epochRate q θ k ≤ epochRate q θ l := by
  have hpow := Real.rpow_le_rpow hk hkl (sub_nonneg.mpr hqh)
  have hc : 0 ≤ 6 * (4096 : ℝ) ^ q / (θ * q) := by positivity
  exact add_le_add_left (mul_le_mul_of_nonneg_left hpow hc) 3

lemma epochDuration_antitone {q θ k l : ℝ} (hq : 0 < q) (hqh : q ≤ 1 / 2)
    (hθ : 0 < θ) (hk : 0 ≤ k) (hkl : k ≤ l) :
    epochDuration q θ l ≤ epochDuration q θ k := by
  apply one_div_le_one_div_of_le
  · linarith [epochRate_three_le hq hθ hk]
  · exact epochRate_mono hq hqh hθ hk hkl

lemma power_times_sqrt {q k : ℝ} (hqh : q ≤ 1 / 2) (hk : 0 ≤ k) :
    k ^ (1 / 2 - q) * Real.sqrt k = k ^ (1 - q) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add_of_nonneg hk (sub_nonneg.mpr hqh) (by norm_num)]
  congr 1
  ring

lemma epochRate_mul_sqrt {q θ k : ℝ} (hqh : q ≤ 1 / 2) (hk : 0 ≤ k) :
    epochRate q θ k * Real.sqrt k =
      3 * Real.sqrt k + 6 * (4096 : ℝ) ^ q / (θ * q) * k ^ (1 - q) := by
  dsimp only [epochRate]
  rw [add_mul, mul_assoc, power_times_sqrt hqh hk]

lemma epoch_response_drift_le {q θ k : ℝ} (hq : 0 < q) (hqh : q ≤ 1 / 2)
    (hθ : 0 < θ) (hk : 0 ≤ k) :
    (2 * Real.sqrt k + 6 * (4096 : ℝ) ^ q / (θ * q) * k ^ (1 - q)) *
      epochDuration q θ k ≤ Real.sqrt k := by
  have hr : 0 < epochRate q θ k := by linarith [epochRate_three_le hq hθ hk]
  have he := epochRate_mul_sqrt (θ := θ) hqh hk
  rw [epochDuration, mul_one_div]
  apply (div_le_iff₀ hr).mpr
  nlinarith [Real.sqrt_nonneg k]

/-- One response coefficient, chosen at the initial count, bounds all later counts. -/
def globalResponseCoefficient (q θ n : ℝ) : ℝ := epochRate q θ n - 1

lemma globalResponseCoefficient_eq (q θ n : ℝ) :
    globalResponseCoefficient q θ n =
      2 + 6 * (4096 : ℝ) ^ q / (θ * q) * n ^ (1 / 2 - q) := by
  dsimp only [globalResponseCoefficient, epochRate]
  ring

lemma globalResponseCoefficient_two_le {q θ n : ℝ} (hq : 0 < q) (hθ : 0 < θ)
    (hn : 0 ≤ n) : 2 ≤ globalResponseCoefficient q θ n := by
  have h := epochRate_three_le hq hθ hn
  dsimp only [globalResponseCoefficient]
  linarith

lemma response_le_global_coefficient {q θ k n : ℝ} (hq : 0 < q) (hqh : q ≤ 1 / 2)
    (hθ : 0 < θ) (hk : 0 ≤ k) (hkn : k ≤ n) :
    2 * Real.sqrt k + 6 * (4096 : ℝ) ^ q / (θ * q) * k ^ (1 - q) ≤
      globalResponseCoefficient q θ n * Real.sqrt k := by
  have hm := mul_le_mul_of_nonneg_right (epochRate_mono hq hqh hθ hk hkn)
    (Real.sqrt_nonneg k)
  have he := epochRate_mul_sqrt (θ := θ) hqh hk
  dsimp only [globalResponseCoefficient]
  nlinarith

lemma global_coefficient_budget_identity {q θ n : ℝ} (hqh : q ≤ 1 / 2) (hn : 0 ≤ n) :
    (globalResponseCoefficient q θ n + 1) * Real.sqrt n =
      3 * Real.sqrt n + 6 * (4096 : ℝ) ^ q / (θ * q) * n ^ (1 - q) := by
  simpa only [globalResponseCoefficient, sub_add_cancel] using epochRate_mul_sqrt (θ := θ) hqh hn

/-- The initial potential and fixed-duration phase cost fit the balanced scalar budget. -/
lemma global_ledger_le_budget {D n q θ K : ℝ} (hD : 0 < D) (hn : 0 < n)
    (hq : 0 < q) (hqh : q ≤ 1 / 2) (hθ : 0 < θ) (hK : 0 ≤ K) :
    2 * Real.sqrt n + θ * D ^ q / (1 - q) +
      K * (globalResponseCoefficient q θ n + 1) * Real.sqrt n ≤
      (6 * K + 2) * (Real.sqrt n + θ * D ^ q / (1 - q) +
        (4096 : ℝ) ^ q * n ^ (1 - q) / (θ * q)) := by
  have hs := Real.sqrt_nonneg n
  have hq1 : q < 1 := by linarith
  have ht : 0 ≤ θ * D ^ q / (1 - q) :=
    div_nonneg (mul_nonneg hθ.le (Real.rpow_nonneg hD.le _)) (sub_pos.mpr hq1).le
  have hu : 0 ≤ (4096 : ℝ) ^ q * n ^ (1 - q) / (θ * q) := by positivity
  have he := global_coefficient_budget_identity (θ := θ) hqh hn.le
  have hrearr : 6 * (4096 : ℝ) ^ q / (θ * q) * n ^ (1 - q) =
      6 * ((4096 : ℝ) ^ q * n ^ (1 - q) / (θ * q)) := by ring
  rw [hrearr] at he
  have heK := congrArg (fun t : ℝ => K * t) he
  nlinarith [mul_nonneg hK hs, mul_nonneg hK ht]

/-- Direct final normalization for the fixed-duration dyadic ledger. -/
theorem dyadic_global_ledger_le {D n K : ℝ} (hn : 0 < n) (hDn : 2 * n ≤ D) (hK : 0 ≤ K) :
    let q := 1 / (dyadicOrder D n : ℝ)
    let θ := strength D n q
    2 * Real.sqrt n + θ * D ^ q / (1 - q) +
      K * (globalResponseCoefficient q θ n + 1) * Real.sqrt n ≤
      (162 * (6 * K + 2)) * Real.sqrt (n * Real.log (D / n)) := by
  dsimp only
  have hD : 0 < D := by linarith
  have hq := dyadic_reciprocal_pos D n
  have hqh := dyadic_reciprocal_le_half D n
  have hq1 : 1 / (dyadicOrder D n : ℝ) < 1 := by linarith
  have hθ := strength_pos hD hn hq hq1
  have hledger := global_ledger_le_budget hD hn hq hqh hθ hK
  have hbudget := mul_le_mul_of_nonneg_left (dyadic_rectangular_budget_le hn hDn)
    (show 0 ≤ 6 * K + 2 by positivity)
  nlinarith

/-- Every exponent at least one half has the same coarse halving contraction. -/
lemma half_rpow_le_three_quarters {a : ℝ} (ha : 1 / 2 ≤ a) :
    (1 / 2 : ℝ) ^ a ≤ 3 / 4 := by
  calc
    (1 / 2 : ℝ) ^ a ≤ (1 / 2 : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ha
    _ = Real.sqrt (1 / 2) := (Real.sqrt_eq_rpow _).symm
    _ ≤ 3 / 4 := by
      have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
      nlinarith [Real.sqrt_nonneg (1 / 2)]

lemma rpow_halving_le {a x y : ℝ} (ha : 1 / 2 ≤ a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : y ≤ x / 2) : y ^ a ≤ (3 / 4) * x ^ a := by
  calc
    y ^ a ≤ ((1 / 2) * x) ^ a := Real.rpow_le_rpow hy (by linarith) (by linarith)
    _ = (1 / 2 : ℝ) ^ a * x ^ a := Real.mul_rpow (by norm_num) hx
    _ ≤ (3 / 4) * x ^ a := mul_le_mul_of_nonneg_right
      (half_rpow_le_three_quarters ha) (Real.rpow_nonneg hx _)

lemma power_phase_cost_le_drop {a x y B : ℝ} (ha : 1 / 2 ≤ a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : y ≤ x / 2) (hB : 0 ≤ B) :
    B * x ^ a + 4 * B * y ^ a ≤ 4 * B * x ^ a := by
  have h := mul_le_mul_of_nonneg_left (rpow_halving_le ha hx hy hxy)
    (show 0 ≤ 4 * B by positivity)
  nlinarith

/-- A finite phase sum has a uniform constant, including the last residual budget. -/
lemma sum_powers_of_halving {a : ℝ} (ha : 1 / 2 ≤ a) (x : ℕ → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hhalf : ∀ j, x (j + 1) ≤ x j / 2) (m : ℕ) :
    (∑ j ∈ Finset.range m, (x j) ^ a) + 4 * (x m) ^ a ≤ 4 * (x 0) ^ a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h := power_phase_cost_le_drop ha (hx m) (hx (m + 1)) (hhalf m)
      (by norm_num : (0 : ℝ) ≤ 1)
    norm_num at h
    linarith

end MatrixSpencer.RectangularParameters
