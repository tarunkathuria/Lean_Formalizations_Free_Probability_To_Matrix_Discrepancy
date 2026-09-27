import MatrixSpencer.EpochSelection
import MatrixSpencer.MSManuscriptProbability

/-! A dimensionless endpoint score, derived from the existing epoch moments.
It is an exact mathematical certificate; its numerical report is separate. -/
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSManuscriptScore

 def score (k energy paid tangent : ℝ) : ℝ :=
  energy / (12 * Real.sqrt k) + paid / (k / 128) + tangent^2 / (36*k)

theorem score_nonneg {k energy paid tangent : ℝ} (hk : 0 < k)
    (he : 0 ≤ energy) (hp : 0 ≤ paid) : 0 ≤ score k energy paid tangent := by
  unfold score
  positivity

theorem score_lt_one {k energy paid tangent : ℝ} (hk : 0 < k)
    (he : 0 ≤ energy) (hp : 0 ≤ paid) (hs : score k energy paid tangent < 1) :
    energy < 12*Real.sqrt k ∧ paid < k/128 ∧ |tangent| < 6*Real.sqrt k := by
  have hroot := Real.sqrt_pos.mpr hk
  have ha : 0 ≤ energy / (12*Real.sqrt k) := by positivity
  have hb : 0 ≤ paid / (k/128) := by positivity
  have hc : 0 ≤ tangent^2 / (36*k) := by positivity
  unfold score at hs
  have he' : energy / (12*Real.sqrt k) < 1 := by linarith
  have hp' : paid / (k/128) < 1 := by linarith
  have ht' : tangent^2 / (36*k) < 1 := by linarith
  refine ⟨(div_lt_one (by positivity)).mp he', (div_lt_one (by positivity)).mp hp', ?_⟩
  have ht : tangent^2 < 36*k := (div_lt_one (by positivity)).mp ht'
  have hsquare := Real.sq_sqrt hk.le
  nlinarith [sq_abs tangent, abs_nonneg tangent]

variable {L : Type} [Fintype L]

theorem score_moment_le (w energy paid tangent : L → ℝ) {k : ℝ} (hk : 0 < k)
    (he : (∑ l, w l * energy l) ≤ (301/100:ℝ)*Real.sqrt k)
    (hp : (∑ l, w l * paid l) ≤ (301/100:ℝ)*k/epochTracePriceScale)
    (ht : (∑ l, w l * (tangent l)^2) ≤ k) :
    (∑ l, w l * score k (energy l) (paid l) (tangent l)) ≤ 3/8 := by
  have hr := Real.sqrt_pos.mpr hk
  have heq : (∑ l, w l * score k (energy l) (paid l) (tangent l)) =
      (∑ l, w l*energy l)/(12*Real.sqrt k) + (∑ l, w l*paid l)/(k/128) +
        (∑ l, w l*(tangent l)^2)/(36*k) := by
    simp only [score, mul_add, mul_div_assoc, Finset.sum_add_distrib, Finset.sum_div]
  rw [heq]
  have h1 := div_le_div_of_nonneg_right he (by positivity : 0 ≤ 12*Real.sqrt k)
  have h2 := div_le_div_of_nonneg_right hp (by positivity : 0 ≤ k/128)
  have h3 := div_le_div_of_nonneg_right ht (by positivity : 0 ≤ 36*k)
  have hc : ((301/100:ℝ)*Real.sqrt k)/(12*Real.sqrt k) +
      ((301/100:ℝ)*k/epochTracePriceScale)/(k/128) + k/(36*k) = 10733/28800 := by
    norm_num [epochTracePriceScale]
    field_simp
    ring
  linarith

end MatrixSpencer.MSManuscriptScore
