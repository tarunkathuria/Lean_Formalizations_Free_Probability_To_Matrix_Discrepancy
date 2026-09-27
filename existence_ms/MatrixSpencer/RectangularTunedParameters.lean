import MatrixSpencer.DyadicGlobalResponseBudget

/-! Natural-count tuned parameters and the final scalar rectangular ledger.
The physical dimension is doubled here for the signed Hermitian lift. -/

noncomputable section
namespace MatrixSpencer
namespace RectangularTunedParameters

def depth (n d : ℕ) : ℕ := RectangularParameters.dyadicDepth (2 * (d : ℝ)) (n : ℝ)

def exponent (n d : ℕ) : ℝ := 1 / (2 : ℝ) ^ depth n d

def weight (n d : ℕ) : ℝ :=
  RectangularParameters.strength (2 * (d : ℝ)) (n : ℝ) (exponent n d)

def coefficient (n d : ℕ) : ℝ :=
  DyadicGlobalResponseBudget.globalCoefficient (depth n d) (weight n d) (n : ℝ)

lemma depth_positive (n d : ℕ) : 1 ≤ depth n d :=
  RectangularParameters.dyadicDepth_pos _ _

lemma exponent_positive (n d : ℕ) : 0 < exponent n d :=
  DyadicGlobalResponseBudget.exponent_pos _

lemma exponent_le_half (n d : ℕ) : exponent n d ≤ 1 / 2 :=
  DyadicGlobalResponseBudget.exponent_le_half _ (depth_positive n d)

lemma exponent_lt_one (n d : ℕ) : exponent n d < 1 :=
  (exponent_le_half n d).trans_lt (by norm_num)

lemma exponent_eq_reciprocal_order (n d : ℕ) :
    exponent n d = 1 / (RectangularParameters.dyadicOrder (2 * (d : ℝ)) (n : ℝ) : ℝ) := by
  simp only [exponent, depth, RectangularParameters.dyadicOrder, Nat.cast_pow, Nat.cast_ofNat]

lemma weight_positive {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d) : 0 < weight n d := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hd' : (0 : ℝ) < 2 * (d : ℝ) := by
    have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
    positivity
  exact RectangularParameters.strength_pos hd' hn' (exponent_positive n d) (exponent_lt_one n d)

lemma coefficient_two_le {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d) : 2 ≤ coefficient n d :=
  DyadicGlobalResponseBudget.globalCoefficient_two_le _ (weight_positive hn hnd) (Nat.cast_nonneg _)

lemma coefficient_eq (n d : ℕ) :
    coefficient n d = 2 +
      6 * (4096 : ℝ) ^ exponent n d / (weight n d * exponent n d) *
        (n : ℝ) ^ (1 / 2 - exponent n d) :=
  DyadicGlobalResponseBudget.globalCoefficient_eq _ _ _

/-- The complete initial-potential and fixed-duration phase ledger has the desired logarithmic scale. -/
theorem ledger_le {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d) {K : ℝ} (hK : 0 ≤ K) :
    2 * Real.sqrt (n : ℝ) + weight n d * (2 * (d : ℝ)) ^ exponent n d / (1 - exponent n d) +
      K * (coefficient n d + 1) * Real.sqrt (n : ℝ) ≤
      (162 * (6 * K + 2)) * Real.sqrt ((n : ℝ) * Real.log (2 * (d : ℝ) / (n : ℝ))) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hdim : 2 * (n : ℝ) ≤ 2 * (d : ℝ) :=
    mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hnd) (by norm_num)
  have h := RectangularParameters.dyadic_global_ledger_le hn' hdim hK
  simpa only [coefficient, DyadicGlobalResponseBudget.globalCoefficient, weight, exponent, depth,
    RectangularParameters.dyadicOrder, Nat.cast_pow, Nat.cast_ofNat] using h

variable {ι j : Type*} [Fintype ι] [Fintype j] [DecidableEq j]

/-- Every restricted epoch inherits the same global tuned scalar response budget. -/
theorem hasResponseBudget (cfg : DyadicEpochConfig ι j) (n d : ℕ)
    (hcount : Fintype.card ι ≤ n) (hdepth : cfg.depth = depth n d)
    (hweight : cfg.weight = weight n d) (hcoefficient : cfg.responseCoefficient = coefficient n d) :
    DyadicEpochPreparation.HasResponseBudget cfg := by
  apply DyadicGlobalResponseBudget.hasResponseBudget_of_original_count cfg n hcount
  rw [hcoefficient, hdepth, hweight]
  rfl

end RectangularTunedParameters
end MatrixSpencer
