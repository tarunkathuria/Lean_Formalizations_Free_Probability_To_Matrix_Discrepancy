import AugmentedHigherRankKS.RuntimeRegularity.LocalLeibniz
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-! Exact scalar reserve derivatives and uniform geometric coefficient bounds. -/

open scoped BigOperators Topology
namespace HigherRankKSRuntime.QuadraticCoefficients

def quadratic (c v w : ℝ) (t : ℝ) : ℝ := c + v * t + w * t ^ 2

theorem quadratic_deriv (c v w : ℝ) : deriv (quadratic c v w) = fun t => v + 2 * w * t := by
  funext t
  have hd := ((hasDerivAt_const t c).add ((hasDerivAt_id t).const_mul v)).add
    (((hasDerivAt_id t).pow 2).const_mul w)
  convert hd.deriv using 1 <;> dsimp [quadratic] <;> ring

theorem quadratic_second (c v w : ℝ) : iteratedDeriv 2 (quadratic c v w) = fun _ => 2 * w := by
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ', quadratic_deriv]
  funext t
  rw [iteratedDeriv_one]
  have hd := (hasDerivAt_const t v).add ((hasDerivAt_id t).const_mul (2 * w))
  simpa only [zero_add, mul_one] using hd.deriv

theorem quadratic_third (c v w : ℝ) : iteratedDeriv 3 (quadratic c v w) = fun _ => 0 := by
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ, quadratic_second]
  funext t
  exact deriv_const t (2 * w)

theorem quadratic_higher (c v w : ℝ) (k : ℕ) (hk : 3 ≤ k) :
    iteratedDeriv k (quadratic c v w) = fun _ => 0 := by
  induction k, hk using Nat.le_induction with
  | base => exact quadratic_third c v w
  | succ k hk ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact deriv_const t 0

theorem quadratic_coefficient_bound {c v w d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hv : |v| ≤ d * c) (hw : |w| ≤ d ^ 2 * c) (k : ℕ) :
    ‖iteratedDeriv k (quadratic c v w) 0‖ ≤ (k.factorial : ℝ) * d ^ k * c := by
  rcases lt_or_ge k 3 with hk | hk
  · interval_cases k
    · simp only [iteratedDeriv_zero, quadratic, mul_zero, zero_pow (by decide : 2 ≠ 0),
        add_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one, one_mul,
        Real.norm_eq_abs, abs_of_nonneg hc]
      exact le_rfl
    · simpa only [iteratedDeriv_one, quadratic_deriv, mul_zero, add_zero,
        Nat.factorial_one, Nat.cast_one, pow_one, one_mul, Real.norm_eq_abs] using hv
    · rw [quadratic_second]
      simpa [Real.norm_eq_abs, abs_mul, Nat.factorial, mul_assoc] using
        mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 2)
  · rw [quadratic_higher c v w k hk]
    simp only [norm_zero]
    positivity

theorem reserve_as_quadratic (c a u h : ℝ) :
    (fun t : ℝ => c - a * (u + t * h) ^ 2) =
      quadratic (c - a * u ^ 2) (-2 * a * u * h) (-a * h ^ 2) := by
  funext t
  dsimp [quadratic]
  ring

theorem reserve_coefficient_bound {c a u h ζ H : ℝ}
    (ha : 1 ≤ a) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hc : ζ ≤ c - a * u ^ 2) (hu : |u| ≤ 1) (hh : |h| ≤ H) (k : ℕ) :
    ‖iteratedDeriv k (fun t : ℝ => c - a * (u + t * h) ^ 2) 0‖ ≤
      (k.factorial : ℝ) * ((4 * a / ζ) * H) ^ k * (c - a * u ^ 2) := by
  have ha0 : 0 ≤ a := by linarith
  have hH : 0 ≤ H := (abs_nonneg h).trans hh
  have hc0 : 0 ≤ c - a * u ^ 2 := hζ.le.trans hc
  have hdiv : 1 ≤ a / ζ := (le_div_iff₀ hζ).mpr (by linarith)
  have hdivc : a ≤ (a / ζ) * (c - a * u ^ 2) := by
    calc
      a = (a / ζ) * ζ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (div_nonneg ha0 hζ.le)
  have hv : |-2 * a * u * h| ≤ ((4 * a / ζ) * H) * (c - a * u ^ 2) := by
    rw [abs_mul, abs_mul, abs_mul]
    rw [abs_of_nonneg ha0]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hm := mul_le_mul hu hh (abs_nonneg h) (by norm_num : (0 : ℝ) ≤ 1)
    have hh' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * a by positivity)
    have hcc := mul_le_mul_of_nonneg_left hdivc hH
    have he : ((4 * a / ζ) * H) * (c - a * u ^ 2) =
        4 * H * ((a / ζ) * (c - a * u ^ 2)) := by ring
    rw [he]
    nlinarith
  have hw : |-a * h ^ 2| ≤ ((4 * a / ζ) * H) ^ 2 * (c - a * u ^ 2) := by
    rw [abs_mul, abs_neg, abs_of_nonneg ha0, abs_of_nonneg (sq_nonneg h)]
    have hsq : h ^ 2 ≤ H ^ 2 := by
      have ht := mul_self_le_mul_self (abs_nonneg h) hh
      simpa only [← sq, sq_abs] using ht
    have hm := mul_le_mul_of_nonneg_left hsq ha0
    have hd2 : a ≤ 16 * (a / ζ) ^ 2 * (c - a * u ^ 2) := by
      have hp : 0 ≤ (a / ζ) * (c - a * u ^ 2) := by positivity
      nlinarith
    have hfinal := mul_le_mul_of_nonneg_right hd2 (sq_nonneg H)
    have he : ((4 * a / ζ) * H) ^ 2 * (c - a * u ^ 2) =
        (16 * (a / ζ) ^ 2 * (c - a * u ^ 2)) * H ^ 2 := by ring
    rw [he]
    exact hm.trans hfinal
  rw [reserve_as_quadratic]
  exact quadratic_coefficient_bound hc0 (by positivity) hv hw k

end HigherRankKSRuntime.QuadraticCoefficients
