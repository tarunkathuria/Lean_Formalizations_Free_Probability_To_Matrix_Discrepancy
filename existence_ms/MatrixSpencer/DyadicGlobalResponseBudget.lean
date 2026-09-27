import MatrixSpencer.DyadicEpochPreparation
import MatrixSpencer.RectangularParameters

/-! One explicit global coefficient supplies the proved dyadic response budget
for every later retained label count. All statements here are scalar bookkeeping
or direct instantiations of the already proved analytic preparation. -/

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer
namespace DyadicGlobalResponseBudget

lemma exponent_pos (m : ℕ) : 0 < 1 / (2 : ℝ) ^ m := by positivity

lemma exponent_le_half (m : ℕ) (hm : 1 ≤ m) : 1 / (2 : ℝ) ^ m ≤ 1 / 2 := by
  calc
    _ = (2 / (2 : ℝ) ^ m) / 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (DyadicHighForcing.paired_exponent_le_one m hm) (by norm_num)

def globalCoefficient (m : ℕ) (θ N : ℝ) : ℝ :=
  RectangularParameters.globalResponseCoefficient (1 / (2 : ℝ) ^ m) θ N

lemma globalCoefficient_eq (m : ℕ) (θ N : ℝ) :
    globalCoefficient m θ N = 2 +
      6 * (4096 : ℝ) ^ (1 / (2 : ℝ) ^ m) / (θ * (1 / (2 : ℝ) ^ m)) *
        N ^ (1 / 2 - 1 / (2 : ℝ) ^ m) :=
  RectangularParameters.globalResponseCoefficient_eq _ _ _

lemma globalCoefficient_two_le (m : ℕ) {θ N : ℝ} (hθ : 0 < θ) (hN : 0 ≤ N) :
    2 ≤ globalCoefficient m θ N :=
  RectangularParameters.globalResponseCoefficient_two_le (exponent_pos m) hθ hN

/-- A single initial-count coefficient dominates every later nonnegative retained count. -/
theorem responseBound_le_globalCoefficient (m : ℕ) (hm : 1 ≤ m)
    {θ k N : ℝ} (hθ : 0 < θ) (hk : 0 ≤ k) (hkN : k ≤ N) :
    DyadicPreparedOwnerResponse.responseBound m θ epochTracePriceScale k ≤
      globalCoefficient m θ N * Real.sqrt k := by
  exact RectangularParameters.response_le_global_coefficient (exponent_pos m) (exponent_le_half m hm)
    hθ hk hkN

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance globalBudgetDyadicCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance globalBudgetDyadicSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

omit [DecidableEq ι] [Nonempty n] in
/-- The epoch's analytic response-budget predicate follows from the explicit global coefficient. -/
theorem hasResponseBudget_of_globalCoefficient (cfg : DyadicEpochConfig ι n) {N : ℝ}
    (hcount : (Fintype.card ι : ℝ) ≤ N)
    (hcoefficient : cfg.responseCoefficient = globalCoefficient cfg.depth cfg.weight N) :
    DyadicEpochPreparation.HasResponseBudget cfg := by
  change DyadicPreparedOwnerResponse.responseBound cfg.depth cfg.weight epochTracePriceScale
    (Fintype.card ι : ℝ) ≤ cfg.responseCoefficient * Real.sqrt (Fintype.card ι : ℝ)
  rw [hcoefficient]
  exact responseBound_le_globalCoefficient cfg.depth cfg.depth_positive cfg.weight_positive
    (Nat.cast_nonneg _) hcount

omit [DecidableEq ι] [Nonempty n] in
/-- Natural original counts may be used directly for any restricted coefficient label type. -/
theorem hasResponseBudget_of_original_count (cfg : DyadicEpochConfig ι n) (N : ℕ)
    (hcount : Fintype.card ι ≤ N)
    (hcoefficient : cfg.responseCoefficient = globalCoefficient cfg.depth cfg.weight (N : ℝ)) :
    DyadicEpochPreparation.HasResponseBudget cfg :=
  hasResponseBudget_of_globalCoefficient cfg (Nat.cast_le.mpr hcount) hcoefficient

/-- The scalar global choice now supplies actual analytic preparation without a budget hypothesis. -/
theorem exists_preparedCovariance_of_globalCoefficient (cfg : DyadicEpochConfig ι n)
    (H : selfAdjoint (Matrix n n ℂ)) {upper : Matrix ι ι ℝ}
    (hupper : upper.PosSemidef) (hupper1 : upper ≤ 1) {N : ℝ}
    (hcount : (Fintype.card ι : ℝ) ≤ N)
    (hcoefficient : cfg.responseCoefficient = globalCoefficient cfg.depth cfg.weight N) :
    ∃ C paid dust, DyadicPreparedCovariance cfg H upper C paid dust :=
  DyadicEpochPreparation.exists_preparedCovariance cfg H hupper hupper1
    (hasResponseBudget_of_globalCoefficient cfg hcount hcoefficient)

end DyadicGlobalResponseBudget
end MatrixSpencer
