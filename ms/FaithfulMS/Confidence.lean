import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! A polynomial retry budget with a specified failure exponent. -/
namespace FaithfulMS.Confidence

theorem retry_failure (M b : ℕ) {q : ℝ} (hq : 0 ≤ q) (hqhalf : q ≤ 1/2) :
    (M : ℝ) * q^(M+b+1) ≤ (1/2 : ℝ)^b := by
  have hm : (M : ℝ) ≤ (2 : ℝ)^M := by
    exact_mod_cast (show M < 2^M from Nat.lt_two_pow_self).le
  have hnonneg : 0 ≤ (1/2 : ℝ)^M := by positivity
  have hcancel : (2 : ℝ)^M * (1/2 : ℝ)^M = 1 := by
    rw [←mul_pow]
    norm_num
  have hfirst : (M : ℝ)*(1/2 : ℝ)^M ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right hm hnonneg).trans_eq hcancel
  have hp := pow_le_pow_left₀ hq hqhalf (M+b+1)
  calc
    _ ≤ (M : ℝ)*(1/2 : ℝ)^(M+b+1) := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg M)
    _ = ((M : ℝ)*(1/2 : ℝ)^M) * (1/2 : ℝ)^b * (1/2 : ℝ) := by
      rw [pow_add,pow_add,pow_one]
      ring
    _ ≤ 1 * (1/2 : ℝ)^b * (1/2 : ℝ) := by gcongr
    _ ≤ (1/2 : ℝ)^b := by nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) b]

end FaithfulMS.Confidence
