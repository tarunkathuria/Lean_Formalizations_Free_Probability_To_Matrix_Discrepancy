import HigherRankKS.SourceProfile
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Dyadic parameter choice and the logarithmic numerical constant

The least admissible dyadic integer is constructed by natural-number
well-ordering. All logarithmic and reserve estimates are scalar theorems.
-/

noncomputable section
namespace HigherRankKS

def logRank (r : ℕ) : ℝ := Real.logb 2 (2 * (r : ℝ))

lemma one_le_logRank {r : ℕ} (hr : 1 ≤ r) : 1 ≤ logRank r := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  unfold logRank
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by positivity)).2
  simpa using (show (2 : ℝ) ≤ 2 * r by linarith)

/-- There is a dyadic upper approximation with factor two, also at rank one. -/
theorem exists_dyadic_scale {r : ℕ} (hr : 1 ≤ r) :
    ∃ k : ℕ, (2 : ℝ) ≤ 2 ^ k ∧ logRank r ≤ (2 : ℝ) ^ k ∧
      (2 : ℝ) ^ k ≤ 2 * logRank r := by
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near (one_le_logRank hr) (by norm_num : (1 : ℝ) < 2)
  refine ⟨j + 1, ?_, hj'.le, ?_⟩
  · have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith
  · rw [pow_succ]
    linarith

/-- A least admissible dyadic q exists and satisfies the sharper bound
`q ≤ 2 log₂(2r)`, including the case r = 1. -/
theorem exists_least_dyadic_scale {r : ℕ} (hr : 1 ≤ r) :
    ∃ k : ℕ, (2 : ℝ) ≤ 2 ^ k ∧ logRank r ≤ (2 : ℝ) ^ k ∧
      (2 : ℝ) ^ k ≤ 2 * logRank r ∧
      ∀ j : ℕ, (2 : ℝ) ≤ 2 ^ j → logRank r ≤ (2 : ℝ) ^ j → k ≤ j := by
  obtain ⟨j, hj2, hjlog, hjupper⟩ := exists_dyadic_scale hr
  have hex : ∃ k : ℕ, (2 : ℝ) ≤ 2 ^ k ∧ logRank r ≤ (2 : ℝ) ^ k :=
    ⟨j, hj2, hjlog⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_, ?_⟩
  · exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.find_min' hex ⟨hj2, hjlog⟩)).trans hjupper
  · intro k hk2 hklog
    exact Nat.find_min' hex ⟨hk2, hklog⟩

lemma reciprocal_scale_bounds {q : ℕ} (hq : 2 ≤ q) :
    0 < (1 : ℝ) / q ∧ (1 : ℝ) / q ≤ 1 / 2 := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  constructor
  · positivity
  · exact one_div_le_one_div_of_le (by norm_num) hq'

/-- The fractional rank cost is at most two at the chosen scale. -/
theorem rank_rpow_reciprocal_le_two {r q : ℕ} (hr : 1 ≤ r) (hq : 2 ≤ q)
    (hqlog : logRank r ≤ q) : (r : ℝ) ^ ((1 : ℝ) / q) ≤ 2 := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hq' : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hq)
  have hβ := (reciprocal_scale_bounds hq).1
  have hbase : (r : ℝ) ≤ (2 : ℝ) ^ (q : ℝ) := by
    apply le_trans (show (r : ℝ) ≤ 2 * r by linarith)
    exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by positivity)).1 hqlog
  have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ r) hbase hβ.le
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hp
  simpa [hq'.ne'] using hp

/-- Natural dyadic q with all source parameter bounds, produced without a parameter oracle. -/
theorem exists_dyadic_parameters {r : ℕ} (hr : 1 ≤ r) :
    ∃ q : ℕ, (∃ k : ℕ, q = 2 ^ k) ∧ 2 ≤ q ∧ logRank r ≤ q ∧
      (q : ℝ) ≤ 2 * logRank r ∧
      0 < (1 : ℝ) / q ∧ (1 : ℝ) / q ≤ 1 / 2 ∧
      (r : ℝ) ^ ((1 : ℝ) / q) ≤ 2 ∧
      ∀ j : ℕ, (2 : ℝ) ≤ 2 ^ j → logRank r ≤ (2 : ℝ) ^ j → q ≤ 2 ^ j := by
  obtain ⟨k, hk2, hklog, hkupper, hkmin⟩ := exists_least_dyadic_scale hr
  have hq2 : 2 ≤ (2 : ℕ) ^ k := by exact_mod_cast hk2
  have hql : logRank r ≤ (↑((2 : ℕ) ^ k) : ℝ) := by exact_mod_cast hklog
  refine ⟨2 ^ k, ⟨k, rfl⟩, hq2, hql, ?_, (reciprocal_scale_bounds hq2).1,
    (reciprocal_scale_bounds hq2).2, rank_rpow_reciprocal_le_two hr hq2 hql, ?_⟩
  · exact_mod_cast hkupper
  · intro j hj2 hjlog
    exact Nat.pow_le_pow_right (by decide) (hkmin j hj2 hjlog)

theorem twenty_sqrt_fourteen_lt_seventy_five : 20 * Real.sqrt 14 < (75 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 14)
  have hp := Real.sqrt_nonneg (14 : ℝ)
  nlinarith

theorem log_constant_conversion : (150 : ℝ) / Real.log 2 < 250 := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_lt_iff₀ hp).2
  linarith [Real.log_two_gt_d9]

/-- Conversion from the dyadic scale estimate to the advertised natural logarithm. -/
theorem discrepancy_constant_conversion {r q : ℕ} (hr : 1 ≤ r)
    (hqupper : (q : ℝ) ≤ 2 * logRank r) (ε : ℝ) :
    75 * q * Real.sqrt ε ≤ 250 * Real.sqrt ε * Real.log (2 * (r : ℝ)) := by
  have hlog : 0 ≤ Real.log (2 * (r : ℝ)) := by
    apply Real.log_nonneg
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  calc
    75 * q * Real.sqrt ε ≤ 75 * (2 * logRank r) * Real.sqrt ε := by
      gcongr
    _ = ((150 : ℝ) / Real.log 2) * Real.sqrt ε * Real.log (2 * (r : ℝ)) := by
      unfold logRank Real.logb
      ring
    _ ≤ 250 * Real.sqrt ε * Real.log (2 * (r : ℝ)) := by
      gcongr
      exact log_constant_conversion.le

@[simp] lemma logRank_one : logRank 1 = 1 := by
  simp [logRank, Real.logb, (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

lemma scale_at_rank_one {q : ℕ} (hq : 2 ≤ q)
    (hqupper : (q : ℝ) ≤ 2 * logRank 1) : q = 2 := by
  simp only [logRank_one, mul_one] at hqupper
  have : q ≤ 2 := by exact_mod_cast hqupper
  omega

/-- The source coefficient at zero has quadratic reserve in q. -/
theorem owner_zero_reciprocal_le {q : ℕ} (hq : 2 ≤ q) :
    SourceProfile.owner ((1 : ℝ) / q) 0 ≤ 350 * (q : ℝ) ^ 2 := by
  have hb := reciprocal_scale_bounds hq
  simpa [one_div, inv_pow] using SourceProfile.owner_at_zero_le hb.1 hb.2

/-- The scalar initial-reserve estimate before the small numerical relaxation. -/
theorem initial_reserve_le_twenty_sqrt_fourteen {r q : ℕ} (hr : 1 ≤ r)
    (hq : 2 ≤ q) (hqlog : logRank r ≤ q) {ε : ℝ} (hε : 0 ≤ ε) :
    2 * Real.sqrt (2 * SourceProfile.owner ((1 : ℝ) / q) 0 * ε *
      (r : ℝ) ^ ((1 : ℝ) / q)) ≤ 20 * Real.sqrt 14 * q * Real.sqrt ε := by
  have hb := reciprocal_scale_bounds hq
  have hc := owner_zero_reciprocal_le hq
  have hc0 : 0 ≤ SourceProfile.owner ((1 : ℝ) / q) 0 :=
    (SourceProfile.owner_pos hb.1 (by constructor <;> norm_num)).le
  have hp := rank_rpow_reciprocal_le_two hr hq hqlog
  have hp0 : 0 ≤ (r : ℝ) ^ ((1 : ℝ) / q) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hinside : 2 * SourceProfile.owner ((1 : ℝ) / q) 0 * ε *
      (r : ℝ) ^ ((1 : ℝ) / q) ≤ 1400 * (q : ℝ) ^ 2 * ε := by
    calc
      _ ≤ 2 * (350 * (q : ℝ) ^ 2) * ε * 2 := by gcongr
      _ = _ := by ring
  have hin0 : 0 ≤ 2 * SourceProfile.owner ((1 : ℝ) / q) 0 * ε *
      (r : ℝ) ^ ((1 : ℝ) / q) := by positivity
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  have hs14 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 14)
  have hsε := Real.sq_sqrt hε
  have hsin := Real.sq_sqrt hin0
  simp only [mul_pow]
  rw [hs14, hsε, hsin]
  nlinarith

theorem initial_reserve_le_seventy_five {r q : ℕ} (hr : 1 ≤ r)
    (hq : 2 ≤ q) (hqlog : logRank r ≤ q) {ε : ℝ} (hε : 0 ≤ ε) :
    2 * Real.sqrt (2 * SourceProfile.owner ((1 : ℝ) / q) 0 * ε *
      (r : ℝ) ^ ((1 : ℝ) / q)) ≤ 75 * q * Real.sqrt ε := by
  apply (initial_reserve_le_twenty_sqrt_fourteen hr hq hqlog hε).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right twenty_sqrt_fourteen_lt_seventy_five.le
      (Nat.cast_nonneg q)) (Real.sqrt_nonneg ε)

/-- The full scalar reserve conversion to the literal constant in the signing theorem. -/
theorem initial_reserve_le_logarithmic {r q : ℕ} (hr : 1 ≤ r)
    (hq : 2 ≤ q) (hqlog : logRank r ≤ q) (hqupper : (q : ℝ) ≤ 2 * logRank r)
    {ε : ℝ} (hε : 0 ≤ ε) :
    2 * Real.sqrt (2 * SourceProfile.owner ((1 : ℝ) / q) 0 * ε *
      (r : ℝ) ^ ((1 : ℝ) / q)) ≤
      250 * Real.sqrt ε * Real.log (2 * (r : ℝ)) :=
  (initial_reserve_le_seventy_five hr hq hqlog hε).trans
    (discrepancy_constant_conversion hr hqupper ε)

theorem min_discrepancy_constant_conversion {r q : ℕ} (hr : 1 ≤ r)
    (hqupper : (q : ℝ) ≤ 2 * logRank r) (ε : ℝ) :
    min 1 (75 * q * Real.sqrt ε) ≤
      min 1 (250 * Real.sqrt ε * Real.log (2 * (r : ℝ))) :=
  min_le_min_left _ (discrepancy_constant_conversion hr hqupper ε)

end HigherRankKS
