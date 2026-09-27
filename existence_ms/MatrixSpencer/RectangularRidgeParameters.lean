import MatrixSpencer.RectangularParameters

/-!
Explicit scalar conditioning parameters for the rectangular potential with an
additional square-root term `2 / D * Tr sqrt(S)`.  These results use the actual
dyadic Tsallis tuning. They do not assert matrix differentiability or a walk
runtime theorem: their role is to replace an instance-dependent density floor
by a fixed-degree inverse-polynomial bound once the matrix KKT inequality has
been established.
-/

noncomputable section
namespace MatrixSpencer.RectangularRidgeParameters

open RectangularParameters

def size (D n : ℝ) : ℝ := D + n + 1
def q (D n : ℝ) : ℝ := 1 / (dyadicOrder D n : ℝ)
def θ (D n : ℝ) : ℝ := strength D n (q D n)
def ridge (D : ℝ) : ℝ := 1 / D
def densityFloor (D n : ℝ) : ℝ := 1 / (10000 * size D n ^ 4)
def stationarityBound (D n : ℝ) : ℝ :=
  2 * n + 2 * Real.sqrt n + θ D n * D ^ q D n + ridge D * Real.sqrt D

lemma size_pos {D n : ℝ} (hD : 1 ≤ D) (hn : 1 ≤ n) : 0 < size D n := by
  dsimp [size]
  linarith

lemma aspect_le_dimension {D n : ℝ} (hD : 1 ≤ D) (hn : 1 ≤ n) : aspect D n ≤ D := by
  apply max_le hD
  apply (div_le_iff₀ (by linarith : 0 < n)).mpr
  nlinarith

lemma log_aspect_le_dimension {D n : ℝ} (hD : 1 ≤ D) (hn : 1 ≤ n) :
    Real.log (aspect D n) ≤ D :=
  (Real.log_le_self (aspect_pos D n).le).trans (aspect_le_dimension hD hn)

lemma order_le_size {D n : ℝ} (hD : 1 ≤ D) (hn : 1 ≤ n) :
    (dyadicOrder D n : ℝ) ≤ 6 * size D n := by
  have h := dyadicOrder_le_four_add_two_log D n
  have hl := log_aspect_le_dimension hD hn
  dsimp [size]
  linarith

lemma reciprocal_exponent_le {D n : ℝ} (hD : 1 ≤ D) (hn : 1 ≤ n) :
    1 / q D n ≤ 6 * size D n := by
  simpa only [q, one_div_one_div] using order_le_size hD hn

lemma exponent_positive (D n : ℝ) : 0 < q D n := dyadic_reciprocal_pos D n

lemma exponent_le_half (D n : ℝ) : q D n ≤ 1 / 2 := dyadic_reciprocal_le_half D n

lemma weight_positive {D n : ℝ} (hD : 1 ≤ D) (hn : 1 ≤ n) : 0 < θ D n :=
  strength_pos (by linarith) (by linarith) (exponent_positive D n)
    ((exponent_le_half D n).trans_lt (by norm_num))

lemma logarithmic_scale_le_size {D n : ℝ} (hD : 1 ≤ D) (hn : 1 ≤ n) :
    Real.sqrt (n * (1 + Real.log (aspect D n))) ≤ size D n := by
  have hl0 := log_aspect_nonneg D n
  have hl := log_aspect_le_dimension hD hn
  have hb : 0 ≤ n * (1 + Real.log (aspect D n)) := by positivity
  have hs := Real.sq_sqrt hb
  have hsz := size_pos hD hn
  have hprod : n * (1 + Real.log (aspect D n)) ≤ size D n ^ 2 := by
    dsimp [size]
    nlinarith [mul_nonneg (by linarith : 0 ≤ n) (sub_nonneg.mpr hl)]
  nlinarith [Real.sqrt_nonneg (n * (1 + Real.log (aspect D n)))]

lemma regularizer_budget_le {D n : ℝ} (hD : 1 ≤ D) (hn : 1 ≤ n) :
    θ D n * D ^ q D n / (1 - q D n) ≤ 81 * size D n := by
  have h := dyadic_optimized_budget_le (by linarith : 0 < D) (by linarith : 0 < n)
  change Real.sqrt n + θ D n * D ^ q D n / (1 - q D n) +
    (4096 : ℝ) ^ q D n * n ^ (1 - q D n) / (θ D n * q D n) ≤ _ at h
  have ht := weight_positive hD hn
  have hq := exponent_positive D n
  have hlast : 0 ≤ (4096 : ℝ) ^ q D n * n ^ (1 - q D n) /
      (θ D n * q D n) := by positivity
  have hs := logarithmic_scale_le_size hD hn
  nlinarith [Real.sqrt_nonneg n]

lemma stationarity_regularizer_le {D n : ℝ} (hD : 1 ≤ D) (hn : 1 ≤ n) :
    θ D n * D ^ q D n ≤ 81 * size D n := by
  have hq := exponent_positive D n
  have hqh := exponent_le_half D n
  have hsub : 0 < 1 - q D n := by linarith
  have ha : 0 ≤ θ D n * D ^ q D n := by
    exact mul_nonneg (weight_positive hD hn).le (Real.rpow_nonneg (by linarith) _)
  have hle : θ D n * D ^ q D n ≤ θ D n * D ^ q D n / (1 - q D n) := by
    apply (le_div_iff₀ hsub).mpr
    nlinarith
  exact hle.trans (regularizer_budget_le hD hn)

lemma ridge_overhead_le_two {D : ℝ} (hD : 1 ≤ D) : 2 * ridge D * Real.sqrt D ≤ 2 := by
  have hD0 : 0 < D := by linarith
  have hs := Real.sq_sqrt hD0.le
  have hsle : Real.sqrt D ≤ D := by nlinarith [Real.sqrt_nonneg D]
  dsimp [ridge]
  have hratio : Real.sqrt D / D ≤ 1 := (div_le_one hD0).mpr hsle
  nlinarith [show 1 / D * Real.sqrt D = Real.sqrt D / D by ring]

lemma stationarity_bound_positive {D n : ℝ} (hD : 1 ≤ D) (hn : 1 ≤ n) :
    0 < stationarityBound D n := by
  have ht := weight_positive hD hn
  have hD0 : 0 < D := by linarith
  have hn0 : 0 < n := by linarith
  dsimp [stationarityBound, ridge]
  positivity

lemma stationarity_bound_le {D n : ℝ} (hD : 1 ≤ D) (hn : 1 ≤ n) :
    stationarityBound D n ≤ 100 * size D n := by
  have ht := stationarity_regularizer_le hD hn
  have hr := ridge_overhead_le_two hD
  have hs := Real.sq_sqrt (by linarith : 0 ≤ n)
  have hsle : Real.sqrt n ≤ n := by nlinarith [Real.sqrt_nonneg n]
  dsimp [stationarityBound, size] at *
  linarith

lemma densityFloor_positive {D n : ℝ} (hD : 1 ≤ D) (hn : 1 ≤ n) :
    0 < densityFloor D n := by
  have h := size_pos hD hn
  dsimp [densityFloor]
  positivity

/-- The scalar floor supplied by the square-root KKT term is at least a
fixed-degree inverse polynomial for the actual rectangular tuning. -/
theorem densityFloor_le_kkt_floor {D n : ℝ} (hD : 1 ≤ D) (hn : 1 ≤ n) :
    densityFloor D n ≤ (ridge D / stationarityBound D n) ^ 2 := by
  have hD0 : 0 < D := by linarith
  have hs0 := size_pos hD hn
  have hb0 := stationarity_bound_positive hD hn
  have hb := stationarity_bound_le hD hn
  have hDsz : D ≤ size D n := by dsimp [size]; linarith
  have hden : D * stationarityBound D n ≤ 100 * size D n ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hDsz) hb0.le,
      mul_nonneg hs0.le (sub_nonneg.mpr hb)]
  have hratio : 1 / (100 * size D n ^ 2) ≤ ridge D / stationarityBound D n := by
    dsimp [ridge]
    rw [div_div]
    exact one_div_le_one_div_of_le (mul_pos hD0 hb0) hden
  have hsmall : 0 ≤ 1 / (100 * size D n ^ 2) := by positivity
  have hsq := mul_self_le_mul_self hsmall hratio
  have hid : (1 / (100 * size D n ^ 2)) ^ 2 = densityFloor D n := by
    dsimp [densityFloor]
    field_simp
    <;> ring
  simpa only [← pow_two, hid] using hsq

@[simp] theorem reciprocal_densityFloor (D n : ℝ) :
    1 / densityFloor D n = 10000 * size D n ^ 4 := by
  simp [densityFloor]

/-- A scalar eigenvalue consequence, separate from the matrix stationarity
argument. No positive lower bound on an eigenvalue of the physical source is
assumed. -/
theorem eigenvalue_floor_of_kkt {D n s : ℝ} (hD : 1 ≤ D) (hn : 1 ≤ n)
    (hs : 0 < s) (hkkt : ridge D / Real.sqrt s ≤ stationarityBound D n) :
    densityFloor D n ≤ s := by
  have hb := stationarity_bound_positive hD hn
  have hroot := Real.sqrt_pos.mpr hs
  have hridge : 0 < ridge D := by dsimp [ridge]; positivity
  have hratio : ridge D / stationarityBound D n ≤ Real.sqrt s := by
    apply (div_le_iff₀ hb).mpr
    simpa only [mul_comm] using (div_le_iff₀ hroot).mp hkkt
  have hsquare := mul_self_le_mul_self (div_nonneg hridge.le hb.le) hratio
  have hbase := densityFloor_le_kkt_floor hD hn
  nlinarith [Real.sq_sqrt hs.le]

end MatrixSpencer.RectangularRidgeParameters
