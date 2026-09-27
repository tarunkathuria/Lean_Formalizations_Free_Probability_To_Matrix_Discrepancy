import MatrixSpencer.RectangularRidgePrimitiveParameters
import MatrixSpencer.RectangularRidgeNumericalParameters

/-! The actual primitive-tuned mixed optimizer stays uniformly positive on the
one-unit neighborhood of the cube's center matrices. This covers the real
finite-difference value queries used by the numerical controller. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeOffCenterFloor
open RectangularRidgeTuning RectangularRidgePotential RectangularRidgeOptimizerFloor
open RectangularRidgePrimitiveParameters
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [Fintype ι]
local instance ridgeOffCenterFloorCStar : CStarAlgebra (Matrix n n ℂ) := {}

theorem optimizer_polynomial_floor_off_center (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (B : ι → Matrix n n ℂ) {N : ℕ} (hN : 1 ≤ N) (hND : N ≤ Fintype.card n)
    (hHn : ‖H‖ ≤ (N : ℝ) + 1)
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
      ((N : ℝ) + 1) + 2 * N + θ * (D : ℝ) ^ exponent N D hN /
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
    ring
  have hscalar : RectangularRidgeParameters.densityFloor D N ≤ (κ / (100 * Q)) ^ 2 := by
    simpa only [← pow_two, hid] using hs
  refine le_trans ?_ hbase
  apply Matrix.le_iff.mpr
  rw [← sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hscalar)


/-- The conservative numerical floor applies throughout the one-unit query
neighborhood, at the same exponent and weight as the original input. -/
theorem optimizer_numerical_floor (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (B : ι → Matrix n n ℂ) {N : ℕ} (hN : 1 ≤ N) (hND : N ≤ Fintype.card n)
    (hHn : ‖H‖ ≤ (N : ℝ) + 1)
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ (N : ℝ)^2 • (1 : Matrix n n ℂ)) :
    RectangularRidgeNumericalParameters.densityFloor ((N : ℝ) + Fintype.card n + 2) •
      (1 : Matrix n n ℂ) ≤
      optimizer H B (depth N (Fintype.card n) hN) (weight N (Fintype.card n) hN)
        (1 / (Fintype.card n : ℝ)) := by
  have hs := RectangularRidgeNumericalParameters.densityFloor_le_primitive
    (m := (N : ℝ)) (D := (Fintype.card n : ℝ))
    (by exact_mod_cast hN) (by exact_mod_cast (show 1 ≤ Fintype.card n from Fintype.card_pos))
  refine le_trans ?_ (optimizer_polynomial_floor_off_center H hH B hN hND hHn hbudget)
  apply Matrix.le_iff.mpr
  rw [← sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hs)

/-- Actual covariance input discharges the source budget for off-center value
queries. No derivative, stationarity, or optimizer-floor hypothesis is supplied. -/
theorem covariance_optimizer_numerical_floor [DecidableEq ι]
    (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hAn : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) (hND : N ≤ Fintype.card n)
    (hcount : Fintype.card ι ≤ N) (hHn : ‖H‖ ≤ (N : ℝ) + 1) :
    RectangularRidgeNumericalParameters.densityFloor ((N : ℝ) + Fintype.card n + 2) •
      (1 : Matrix n n ℂ) ≤
      optimizer H (covarianceKraus A C)
        (depth N (Fintype.card n) hN) (weight N (Fintype.card n) hN)
        (1 / (Fintype.card n : ℝ)) := by
  apply optimizer_numerical_floor H hH (covarianceKraus A C) hN hND hHn
  refine (MSManuscriptOptimizerFloor.covariance_budget A hA hAn hC hC1).trans ?_
  apply Matrix.le_iff.mpr
  rw [← sub_smul]
  apply Matrix.PosSemidef.one.smul
  apply sub_nonneg.mpr
  have hc : (Fintype.card ι : ℝ) ≤ N := by exact_mod_cast hcount
  nlinarith [show (0 : ℝ) ≤ (Fintype.card ι : ℝ) from Nat.cast_nonneg _]

end MatrixSpencer.RectangularRidgeOffCenterFloor
