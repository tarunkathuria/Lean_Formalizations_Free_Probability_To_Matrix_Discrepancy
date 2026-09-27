import MatrixSpencer.MSManuscriptComplexSourceNorm
import MatrixSpencer.KSOwnerInputBounds
import MatrixSpencer.KSOptimizerFloor
import MatrixSpencer.KSActualEnvelope

/-! Uniform optimizer floors on bounded MS covariance-query segments. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptOptimizerFloor
set_option maxHeartbeats 1200000
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
open MSManuscriptComplexSourceNorm MSManuscriptComplexCovarianceSource KSOptimizerFloor

theorem covariance_budget (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    (hAn : ∀i, ‖A i‖ ≤ 1) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1) :
    (∑i, (covarianceKraus A C i)ᴴ*covarianceKraus A C i) ≤
      (Fintype.card ι : ℝ)^2 • (1 : Matrix n n ℂ) := by
  rw [KSOwnerInputBounds.covarianceKraus_sum_eq A hA hC]
  have hs : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
    change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (1 : Matrix n n ℂ)‖ ≤ 1
    rw [map_one]
    exact ContinuousLinearMap.norm_id_le
  have hn := source_norm_le_of_caps A hAn (real_coefficient_norm_le_one hC hC1) hs
  have he : source A (realMatrixEmbedding C) 1 = covarianceSource A C 1 := source_real A C 1
  rw [he, mul_one, mul_one] at hn
  have hh := (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg (Fintype.card ι : ℝ))
    (covarianceSource_posSemidef A hA hC Matrix.PosSemidef.one).nonneg).mp hn
  simpa only [Algebra.algebraMap_eq_smul_one] using hh

def floor (k d : ℕ) (R θ : ℝ) : ℝ :=
  min 1 ((θ/(2*R+2*(k : ℝ)+2*θ*Real.sqrt (d : ℝ)))^2)

theorem floor_pos {k d : ℕ} (hd : 0 < d) {R θ : ℝ} (hR : 0 ≤ R) (hθ : 0 < θ) :
    0 < floor k d R θ := by
  unfold floor
  have hh : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  positivity

theorem floor_le_one (k d : ℕ) (R θ : ℝ) : floor k d R θ ≤ 1 := min_le_left _ _

theorem optimizer_floor [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian) (hAn : ∀i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    {θ R : ℝ} (hθ : 0 < θ) (hR : ‖H‖ ≤ R) :
    floor (Fintype.card ι) (Fintype.card n) R θ • (1 : Matrix n n ℂ) ≤
      densityOptimizer H (covarianceKraus A C) θ := by
  have hh := densityOptimizer_floor H hH (covarianceKraus A C) hθ hR (covariance_budget A hA hAn hC hC1)
  have hk : Real.sqrt ((Fintype.card ι : ℝ)^2) = Fintype.card ι :=
    Real.sqrt_sq (Nat.cast_nonneg _)
  simp only [inputDenominator, hk] at hh
  refine le_trans ?_ hh
  apply Matrix.le_iff.mpr
  rw [← sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr (min_le_right _ _))

/-- The explicit density floor applies to the actual canonical branch. -/
theorem branch_floor [Nonempty n] (A : ι → Matrix n n ℂ)
    (hA : ∀i, (A i).IsHermitian) (hAn : ∀i, ‖A i‖ ≤ 1) {θ R : ℝ} (hθ : 0 < θ)
    (H : ℝ → selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ))
    (t : ℝ) (hCt : (C t : Matrix ι ι ℝ).PosSemidef) (hC1 : (C t : Matrix ι ι ℝ) ≤ 1)
    (hR : ‖(H t : Matrix n n ℂ)‖ ≤ R) :
    floor (Fintype.card ι) (Fintype.card n) R θ • (1 : Matrix n n ℂ) ≤
      (KSFrobeniusTangent.chart n (KSActualEnvelope.branch A θ H C t) : Matrix n n ℂ) := by
  rw [KSActualEnvelope.chart_branch]
  exact optimizer_floor (H t : Matrix n n ℂ)
    (show (H t : Matrix n n ℂ).IsHermitian from (H t).property) A hA hAn hCt hC1 hθ hR

end MatrixSpencer.MSManuscriptOptimizerFloor
