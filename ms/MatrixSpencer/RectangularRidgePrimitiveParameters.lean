import MatrixSpencer.RectangularRidgeTuning
import MatrixSpencer.RectangularRidgeOptimizerFloor

/-! Polynomial conditioning for the dyadic exponent selected by the bounded
integer-comparison loop. This connects numerical tuning to the actual mixed
optimizer, without requiring evaluation of a real logarithm. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgePrimitiveParameters
open RectangularRidgeTuning RectangularRidgePotential RectangularRidgeOptimizerFloor

def exponent (N D : ℕ) (hN : 1 ≤ N) : ℝ := 1 / (order N D hN : ℝ)
def weight (N D : ℕ) (hN : 1 ≤ N) : ℝ := RectangularParameters.strength D N (exponent N D hN)

theorem exponent_positive (N D : ℕ) (hN : 1 ≤ N) : 0 < exponent N D hN := by
  have hp : (0 : ℝ) < order N D hN := by exact_mod_cast (show 0 < order N D hN by have := order_two_le N D hN; omega)
  exact one_div_pos.mpr hp

theorem exponent_le_half (N D : ℕ) (hN : 1 ≤ N) : exponent N D hN ≤ 1/2 := by
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast order_two_le N D hN)

theorem weight_positive {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) : 0 < weight N D hN :=
  RectangularParameters.strength_pos
    (by exact_mod_cast (show 0 < D by omega)) (by exact_mod_cast (show 0 < N by omega))
    (exponent_positive N D hN) ((exponent_le_half N D hN).trans_lt (by norm_num))

theorem regularizer_budget_le {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    weight N D hN * (D : ℝ) ^ exponent N D hN / (1 - exponent N D hN) ≤
      81 * RectangularRidgeParameters.size D N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hb := optimized_budget_le hN hND
  change Real.sqrt (N : ℝ) + weight N D hN * (D : ℝ) ^ exponent N D hN /
    (1 - exponent N D hN) + (4096 : ℝ) ^ exponent N D hN *
      (N : ℝ) ^ (1 - exponent N D hN) / (weight N D hN * exponent N D hN) ≤ _ at hb
  have hlast : 0 ≤ (4096 : ℝ) ^ exponent N D hN * (N : ℝ) ^ (1 - exponent N D hN) /
      (weight N D hN * exponent N D hN) := by
    have := weight_positive hN hND
    have := exponent_positive N D hN
    positivity
  have hr1 : (1 : ℝ) ≤ (D : ℝ) / N := by
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < N)).mpr
    simpa using (Nat.cast_le.mpr hND : (N : ℝ) ≤ D)
  have he : RectangularParameters.aspect D N = (D : ℝ) / N := max_eq_right hr1
  have hs := RectangularRidgeParameters.logarithmic_scale_le_size hd hn
  rw [he] at hs
  nlinarith [Real.sqrt_nonneg (N : ℝ)]

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [Fintype ι]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

/-- Primitive polynomial floor, at the optimizer of the potential whose
exponent is selected by the explicit comparison loop. -/
theorem optimizer_polynomial_floor (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (B : ι → Matrix n n ℂ) {N : ℕ} (hN : 1 ≤ N) (hND : N ≤ Fintype.card n)
    (hHn : ‖H‖ ≤ N)
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ (N : ℝ)^2 • (1 : Matrix n n ℂ)) :
    RectangularRidgeParameters.densityFloor (Fintype.card n : ℝ) N • (1 : Matrix n n ℂ) ≤
      optimizer H B (depth N (Fintype.card n) hN) (weight N (Fintype.card n) hN)
        (1 / (Fintype.card n : ℝ)) := by
  let D := Fintype.card n
  let Q := RectangularRidgeParameters.size (D : ℝ) N
  let m := depth N D hN
  let θ := weight N D hN
  let κ : ℝ := 1 / (D : ℝ)
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D from Fintype.card_pos)
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hD0 : (0 : ℝ) < D := by linarith
  have hQ : 0 < Q := RectangularRidgeParameters.size_pos hd hn
  have hm : 1 ≤ m := depth_positive N D hN
  have hθ : 0 < θ := weight_positive hN hND
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hq : 1 / (2 ^ m : ℝ) = exponent N D hN := by simp [m, exponent, order]
  have hin := objective_le_input_bound H hH B m hm hθ.le hκ.le hHn hbudget
    (optimizer_mem H B m θ κ)
  rw [Real.sqrt_sq (Nat.cast_nonneg N), hq] at hin
  have hr := regularizer_budget_le hN hND
  have hroot := RectangularRidgeParameters.ridge_overhead_le_two hd
  have hcap : objective H B m θ κ (optimizer H B m θ κ) + ‖H‖ ≤ 100 * Q := by
    change objective H B m θ κ (optimizer H B m θ κ) ≤
      (N : ℝ) + 2 * N + θ * (D : ℝ) ^ exponent N D hN /
        (1 - exponent N D hN) + 2 * κ * Real.sqrt D at hin
    change θ * (D : ℝ) ^ exponent N D hN / (1 - exponent N D hN) ≤ 81 * Q at hr
    change 2 * κ * Real.sqrt D ≤ 2 at hroot
    have hNQ : (N : ℝ) + 1 ≤ Q := by dsimp [Q, RectangularRidgeParameters.size]; linarith
    linarith
  have hbase := optimizer_floor_of_objective_cap H hH B m hm hθ hκ
    (by positivity : 0 < 100 * Q) hcap
  have hDQ : (D : ℝ) ≤ Q := by dsimp [Q, RectangularRidgeParameters.size]; linarith
  have hden : (D : ℝ) * (100 * Q) ≤ 100 * Q ^ 2 := by nlinarith
  have hratio : 1 / (100 * Q ^ 2) ≤ κ / (100 * Q) := by
    dsimp [κ]
    rw [div_div]
    exact one_div_le_one_div_of_le (by positivity) hden
  have hs := mul_self_le_mul_self (by positivity : 0 ≤ 1 / (100 * Q ^ 2)) hratio
  have hid : (1 / (100 * Q ^ 2)) ^ 2 = RectangularRidgeParameters.densityFloor D N := by
    dsimp [RectangularRidgeParameters.densityFloor]
    change (1 / (100 * Q ^ 2)) ^ 2 = 1 / (10000 * Q ^ 4)
    field_simp
    <;> ring
  have hscalar : RectangularRidgeParameters.densityFloor D N ≤ (κ / (100 * Q)) ^ 2 := by
    simpa only [← pow_two, hid] using hs
  refine le_trans ?_ hbase
  apply Matrix.le_iff.mpr
  rw [← sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hscalar)

end MatrixSpencer.RectangularRidgePrimitiveParameters
