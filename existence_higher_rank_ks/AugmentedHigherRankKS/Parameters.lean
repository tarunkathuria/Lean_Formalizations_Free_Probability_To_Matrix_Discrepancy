import HigherRankKS.Parameters

/-! Scalar constants for the square-root-logarithmic augmented-reserve proof. -/
noncomputable section
namespace AugmentedHigherRankKS

def reserveScale (β : ℝ) : ℝ := 128 / β

def epochScale (β ε : ℝ) : ℝ := 128 * Real.sqrt (ε / β)

theorem reserveScale_pos {β : ℝ} (hβ : 0 < β) : 0 < reserveScale β := by
  unfold reserveScale
  positivity

theorem reserveScale_dominates_response {β : ℝ} (hβ : 0 < β) :
    120 / β ≤ reserveScale β := by
  unfold reserveScale
  exact (div_le_div_iff_of_pos_right hβ).mpr (by norm_num)

theorem reserveScale_cap {β : ℝ} (hβ : 0 < β) (hβ2 : β ≤ 1 / 2) :
    4 / reserveScale β ≤ 1 / 48 := by
  have he : 4 / reserveScale β = β / 32 := by unfold reserveScale; field_simp; ring
  rw [he]
  linarith

theorem epochScale_nonneg (β ε : ℝ) : 0 ≤ epochScale β ε := by
  unfold epochScale
  positivity

/-- Initialization pays only one reciprocal power of the source exponent. -/
theorem initial_epoch_budget_le {β ε b s : ℝ}
    (hβ : 0 < β) (hε : 0 ≤ ε) (hb : 0 ≤ b) (hs : s ≤ 2) :
    2 * Real.sqrt (4 * (reserveScale β * 4) * ε * s * b) ≤
      epochScale β ε * Real.sqrt b := by
  have he : 4 * (reserveScale β * 4) * ε * s * b =
      2048 * (ε / β) * s * b := by unfold reserveScale; ring
  rw [he]
  have hsrc : 2048 * (ε / β) * s * b ≤ 4096 * (ε / β) * b := by
    have h := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2048 * (ε / β) * b)
    nlinarith
  calc
    _ ≤ 2 * Real.sqrt (4096 * (ε / β) * b) := by gcongr
    _ = epochScale β ε * Real.sqrt b := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 4096 * (ε / β)),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4096)]
      norm_num [epochScale]
      ring

theorem dyadic_scale_le_four_log {r q : ℕ} (hr : 1 ≤ r)
    (hq : (q : ℝ) ≤ 2 * HigherRankKS.logRank r) :
    (q : ℝ) ≤ 4 * Real.log (2 * (r : ℝ)) := by
  have hlog : 0 ≤ Real.log (2 * (r : ℝ)) := by
    apply Real.log_nonneg
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply hq.trans
  unfold HigherRankKS.logRank Real.logb
  apply (le_of_mul_le_mul_right ?_ htwo)
  have he : 2 * (Real.log (2 * (r : ℝ)) / Real.log 2) * Real.log 2 =
      2 * Real.log (2 * (r : ℝ)) := by field_simp
  rw [he]
  have hl := Real.log_two_gt_d9
  nlinarith

/-- Natural-log conversion for the stronger finite-epoch existence constant. -/
theorem existence_log_constant {r q : ℕ} (hr : 1 ≤ r)
    (hq : (q : ℝ) ≤ 2 * HigherRankKS.logRank r) {ε : ℝ} (hε : 0 ≤ ε) :
    512 * Real.sqrt (ε * q) ≤ 10000 * Real.sqrt (ε * Real.log (2 * (r : ℝ))) := by
  have hscale := dyadic_scale_le_four_log hr hq
  have hlog : 0 ≤ Real.log (2 * (r : ℝ)) := by
    apply Real.log_nonneg
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hsq : Real.sqrt (ε * q) ≤ 2 * Real.sqrt (ε * Real.log (2 * (r : ℝ))) := by
    have h := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hscale hε)
    rw [show ε * (4 * Real.log (2 * (r : ℝ))) =
      4 * (ε * Real.log (2 * (r : ℝ))) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at h
    norm_num at h
    simpa only [Real.sqrt_mul hε] using h
  have hnonneg := Real.sqrt_nonneg (ε * Real.log (2 * (r : ℝ)))
  nlinarith

end AugmentedHigherRankKS
