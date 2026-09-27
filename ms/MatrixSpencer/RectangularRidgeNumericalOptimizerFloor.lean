import MatrixSpencer.RectangularRidgePrimitiveParameters
import MatrixSpencer.RectangularRidgeNumericalParameters
import MatrixSpencer.MSManuscriptFrameFamily

/-! The primitive optimizer floor implies the smaller fixed numerical floor.
Coefficient compression preserves the original source budget; the reduced
matrices need not satisfy the original unit norm bound. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeNumericalOptimizerFloor
set_option maxHeartbeats 300000
open RectangularRidgePrimitiveParameters

/-- The numerical input size is the physical dimension plus original count plus two. -/
def size (d N : ℕ) : ℝ := d+N+2

theorem numerical_floor_le_primitive {d N : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N) :
    RectangularRidgeNumericalParameters.densityFloor (size d N) ≤
      RectangularRidgeParameters.densityFloor d N := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let P : ℝ := size d N
  let Q : ℝ := RectangularRidgeParameters.size d N
  have hP : 4 ≤ P := by dsimp [P,size]; linarith
  have hQ : 0 < Q := by dsimp [Q,RectangularRidgeParameters.size]; positivity
  have hQP : Q ≤ P := by dsimp [P,Q,size,RectangularRidgeParameters.size]; linarith
  have hP0 : 0 < P := by linarith
  have hp4 : Q^4 ≤ P^4 := pow_le_pow_left₀ hQ.le hQP 4
  have hp2 : (16 : ℝ) ≤ P^2 := by nlinarith
  have hden : 10000*Q^4 ≤ (2:ℝ)^10*P^6 := by
    calc
      _ ≤ 10000*P^4 := mul_le_mul_of_nonneg_left hp4 (by norm_num)
      _ ≤ ((2:ℝ)^10*P^2)*P^4 := mul_le_mul_of_nonneg_right (by norm_num at *; nlinarith) (by positivity)
      _ = _ := by ring
  change ((2:ℝ)^10*P^6)⁻¹ ≤ 1/(10000*Q^4)
  rw [one_div]
  exact inv_anti₀ (by positivity) hden

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [Fintype ι]
local instance ridgeNumericalFloorCStar : CStarAlgebra (Matrix n n ℂ) := {}
attribute [local irreducible] RectangularRidgePotential.optimizer

/-- Fixed polynomial numerical floor at the exact primitive-tuned optimizer. -/
theorem optimizer_floor (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (B : ι → Matrix n n ℂ) {N : ℕ} (hN : 1 ≤ N) (hND : N ≤ Fintype.card n)
    (hHn : ‖H‖ ≤ N)
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ (N : ℝ)^2 • (1 : Matrix n n ℂ)) :
    RectangularRidgeNumericalParameters.densityFloor (size (Fintype.card n) N) •
      (1 : Matrix n n ℂ) ≤
      RectangularRidgePotential.optimizer H B (RectangularRidgeTuning.depth N (Fintype.card n) hN)
        (weight N (Fintype.card n) hN) (1 / (Fintype.card n : ℝ)) := by
  apply le_trans _ (optimizer_polynomial_floor H hH B hN hND hHn hbudget)
  apply Matrix.le_iff.mpr
  rw [← sub_smul]
  exact Matrix.PosSemidef.one.smul
    (sub_nonneg.mpr (numerical_floor_le_primitive Fintype.card_pos hN))

/-- Original unit contractions give the correct budget after arbitrary finite
coefficient compression, whenever the lifted covariance remains below identity. -/
theorem mixed_covariance_budget {N k d : ℕ}
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (U : Matrix (Fin N) (Fin k) ℝ)
    {C : Matrix (Fin k) (Fin k) ℝ} (hC : C.PosSemidef) (hphysical : covarianceLift U C ≤ 1) :
    (∑ i, (covarianceKraus (mixFamily A U) C i)ᴴ * covarianceKraus (mixFamily A U) C i) ≤
      (N : ℝ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have hmix := mixFamily_isHermitian A U hA
  rw [KSOwnerInputBounds.covarianceKraus_sum_eq (mixFamily A U) hmix hC]
  have hb := MSManuscriptOptimizerFloor.covariance_budget A hA hAn
    (covarianceLift_posSemidef U hC) hphysical
  rw [KSOwnerInputBounds.covarianceKraus_sum_eq A hA (covarianceLift_posSemidef U hC)] at hb
  simpa only [Fintype.card_fin, covarianceSource_rectangular_mixing] using hb

end MatrixSpencer.RectangularRidgeNumericalOptimizerFloor
