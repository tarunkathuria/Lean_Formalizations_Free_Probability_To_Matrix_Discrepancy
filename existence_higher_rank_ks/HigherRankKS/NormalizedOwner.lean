import HigherRankKS.SourceProfile

/-! The scalar owner curvature after normalizing a coefficient direction. -/

noncomputable section
namespace HigherRankKS.NormalizedOwner

open SourceProfile

theorem quadratic_payment {c u τ d dd K y : ℝ} (hc : 0 < c) (hu : 0 < u)
    (hτ : 0 ≤ τ) (hcancel : 2 * u ≤ -dd - (K + 4) * d ^ 2 / c) :
    (c / (2 * u)) * y ^ 2 * τ * (dd + K * d ^ 2 / c) ≤
      -(c * τ * y ^ 2) - (2 / u) * d ^ 2 * τ * y ^ 2 := by
  have h := mul_le_mul_of_nonneg_left hcancel
    (show 0 ≤ c / (2 * u) * y ^ 2 * τ by positivity)
  have he : (c / (2 * u) * y ^ 2 * τ) *
      (-dd - (K + 4) * d ^ 2 / c - 2 * u) =
      -(c * τ * y ^ 2) - (2 / u) * d ^ 2 * τ * y ^ 2 -
        (c / (2 * u)) * y ^ 2 * τ * (dd + K * d ^ 2 / c) := by
    field_simp
    ring
  have hh : 0 ≤ (c / (2 * u) * y ^ 2 * τ) *
      (-dd - (K + 4) * d ^ 2 / c - 2 * u) := by nlinarith
  rw [he] at hh
  linarith

def direction (c u y : ℝ) : ℝ := Real.sqrt (c / u) * y

theorem direction_eq_inv_sqrt {c : ℝ} (hc : 0 ≤ c) (u y : ℝ) :
    direction c u y = (1 / Real.sqrt u) * Real.sqrt c * y := by
  rw [direction, Real.sqrt_div hc]
  ring

theorem direction_sq {c u : ℝ} (hc : 0 ≤ c) (hu : 0 ≤ u) (y : ℝ) :
    direction c u y ^ 2 = c / u * y ^ 2 := by
  rw [direction, mul_pow, Real.sq_sqrt (div_nonneg hc hu)]

theorem owner_payment {β x p q : ℝ} (hβ : 0 < β)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hp : 0 ≤ p) (hq : 0 < q) (y : ℝ) :
    (1 / 2 : ℝ) * direction (owner β x) (ownerScale β) y ^ 2 * (p * q) *
      (deriv (deriv (owner β)) x + (2 * (1 - β) / β) *
        (deriv (owner β) x) ^ 2 / owner β x) ≤
      -(owner β x * (p * q) * y ^ 2) -
        (2 / ownerScale β) * (p / q) * (-(deriv (owner β) x) * q) ^ 2 * y ^ 2 := by
  have hb := quadratic_payment (owner_pos hβ hx) (ownerScale_pos hβ)
    (mul_nonneg hp hq.le) (owner_cancellation_lower hβ hx) (y := y)
  rw [direction_sq (owner_pos hβ hx).le (ownerScale_pos hβ).le]
  convert hb using 1 <;> field_simp

theorem direction_ne_zero {ι : Type*} {c : ι → ℝ} {u : ℝ}
    (hc : ∀ i, 0 < c i) (hu : 0 < u) {y : ι → ℝ} (hy : y ≠ 0) :
    (fun i => direction (c i) u (y i)) ≠ 0 := by
  intro hz
  apply hy
  funext i
  have hi := congrFun hz i
  have hroot : Real.sqrt (c i / u) ≠ 0 := (Real.sqrt_pos.mpr (div_pos (hc i) hu)).ne'
  exact (mul_eq_zero.mp hi).resolve_left hroot

end HigherRankKS.NormalizedOwner
