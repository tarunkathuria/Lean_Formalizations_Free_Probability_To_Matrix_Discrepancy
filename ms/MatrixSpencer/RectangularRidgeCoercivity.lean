import MatrixSpencer.RectangularRidgeCalculus
import MatrixSpencer.KSOptimizerInverseBound

/-! The added square-root term supplies an explicit coercivity constant and
inverse bound independently of the dyadic exponent and source rank. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeCalculus
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance ridgeCoercivityLocal1 : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeCoercivityLocal2 : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeCoercivityLocal3 : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance ridgeCoercivityLocal4 : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance ridgeCoercivityLocal5 : NormedAddCommGroup (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
local instance ridgeCoercivityLocal6 : NormedSpace ℝ (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
set_option maxHeartbeats 1200000

theorem negativeHessian_ge_ridge (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    realTrace ((X : Matrix n n ℂ) *
      (negativeTsallisHessianEquiv κ hκ.ne' S hS X : Matrix n n ℂ)) ≤
      negativeHessian H B m θ κ S X X := by
  have hd := dyadicDensityNegativeHessian_nonneg H B m hm θ hθ S X hS
  unfold negativeHessian
  rw [fderiv_fderiv_eq_add H B m hm θ κ S hS]
  change _ ≤ -(fderiv ℝ (fun T => fderiv ℝ (hermitianDyadicDensityObjective H B m θ) T) S X X +
    fderiv ℝ (fun T => fderiv ℝ (tsallisPotential κ) T) S X X)
  rw [fderiv_fderiv_tsallisPotential_apply κ hκ.ne' S X X hS, realTrace_mul_comm]
  change 0 ≤ -fderiv ℝ (fun T => fderiv ℝ (hermitianDyadicDensityObjective H B m θ) T) S X X at hd
  linarith

theorem negativeHessian_coercive (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (htr : realTrace (S : Matrix n n ℂ) = 1) :
    κ / 2 * realTrace ((X : Matrix n n ℂ) * (X : Matrix n n ℂ)) ≤
      negativeHessian H B m θ κ S X X := by
  have hSone : (S : Matrix n n ℂ) ≤ 1 := by
    simpa only [htr, map_one] using posSemidef_le_trace_identity hS.posSemidef
  exact (KSObjectiveCurvature.negativeTsallisHessian_ge κ hκ S X hS hSone).trans
    (negativeHessian_ge_ridge H B m hm hθ hκ S X hS)

theorem tangent_hessian_coercive (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (htr : realTrace (S : Matrix n n ℂ) = 1) (X : densityTangent (n := n)) :
    κ / 2 * ‖X‖ ^ 2 ≤ tangentHessianEquiv H B m hm θ κ hθ hκ S hS X X := by
  have hl := negativeHessian_coercive H B m hm hθ hκ S X hS htr
  have hn := KSObjectiveUpper.norm_sq_le_trace_square
    (show (((X : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)).IsHermitian from
      (X : selfAdjoint (Matrix n n ℂ)).property)
  exact (mul_le_mul_of_nonneg_left hn (div_nonneg hκ.le (by norm_num))).trans hl

theorem tangent_hessian_inverse_norm_le (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (htr : realTrace (S : Matrix n n ℂ) = 1) :
    ‖(tangentHessianEquiv H B m hm θ κ hθ hκ S hS).symm.toContinuousLinearMap‖ ≤ 2 / κ := by
  have h := KSOptimizerInverseBound.inverse_norm_le_of_coercivity (E := densityTangent (n := n))
    (tangentHessianEquiv H B m hm θ κ hθ hκ S hS) (div_pos hκ (by norm_num))
    (tangent_hessian_coercive H B m hm θ κ hθ hκ S hS htr)
  simpa only [inv_div] using h

end MatrixSpencer.RectangularRidgeCalculus
