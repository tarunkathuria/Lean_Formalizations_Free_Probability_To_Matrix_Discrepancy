import MatrixSpencer.DyadicOwnerDustPreparation
import MatrixSpencer.DyadicEpochState

/-! The analytic construction supplies the concrete finite epoch preparation.
Only the scalar comparison between the proved response formula and the chosen
global epoch coefficient remains an explicit parameter condition. -/

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Set
noncomputable section
namespace MatrixSpencer
namespace DyadicEpochPreparation

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance epochPreparationDyadicCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance epochPreparationDyadicSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- This predicate is a scalar parameter bound, with no analytic or transition oracle. -/
def HasResponseBudget (cfg : DyadicEpochConfig ι n) : Prop :=
  DyadicPreparedOwnerResponse.responseBound cfg.depth cfg.weight epochTracePriceScale (Fintype.card ι : ℝ) ≤
    cfg.responseCoefficient * Real.sqrt (Fintype.card ι : ℝ)

lemma preparedCovariance_of_dustPrepared (cfg : DyadicEpochConfig ι n)
    (H : selfAdjoint (Matrix n n ℂ)) {upper C : Matrix ι ι ℝ} {paid dust : ℝ}
    (hbudget : HasResponseBudget cfg)
    (h : DyadicOwnerDustPreparation.DustPreparedOwner H cfg.matrices cfg.hermitian cfg.depth cfg.weight
      epochTracePriceScale epochDustThreshold upper C paid dust) :
    DyadicPreparedCovariance cfg H upper C paid dust := by
  refine ⟨h.covariance, h.paid_nonneg, h.dust_nonneg, h.trace_account,
    h.dust_budget, h.payment, h.floor, h.response.trans hbudget⟩

/-- The actual compact preparation and finite dust loop construct every epoch preparation field. -/
theorem exists_preparedCovariance (cfg : DyadicEpochConfig ι n)
    (H : selfAdjoint (Matrix n n ℂ)) {upper : Matrix ι ι ℝ}
    (hupper : upper.PosSemidef) (hupper1 : upper ≤ 1) (hbudget : HasResponseBudget cfg) :
    ∃ C paid dust, DyadicPreparedCovariance cfg H upper C paid dust := by
  obtain ⟨C, paid, dust, h⟩ := DyadicOwnerDustPreparation.exists_dust_prepared_owner
    H cfg.matrices cfg.hermitian cfg.contractions hupper hupper1 cfg.depth cfg.depth_positive
    cfg.weight_positive (by norm_num [epochTracePriceScale] : 0 < epochTracePriceScale)
    (by norm_num [epochDustThreshold] : 0 < epochDustThreshold)
    (show 0 < Fintype.card ι by have := cfg.count_large; omega)
  exact ⟨C, paid, dust, preparedCovariance_of_dustPrepared cfg H hbudget h⟩

/-- The same actual construction also retains the total paid withdrawal bound. -/
theorem exists_preparedCovariance_with_paid_budget (cfg : DyadicEpochConfig ι n)
    (H : selfAdjoint (Matrix n n ℂ)) {upper : Matrix ι ι ℝ}
    (hupper : upper.PosSemidef) (hupper1 : upper ≤ 1) (hbudget : HasResponseBudget cfg) :
    ∃ C paid dust, DyadicPreparedCovariance cfg H upper C paid dust ∧
      paid ≤ (Fintype.card ι : ℝ) / 2048 := by
  have hk : 0 < Fintype.card ι := by have := cfg.count_large; omega
  have hL : 0 < epochTracePriceScale := by norm_num [epochTracePriceScale]
  obtain ⟨C, paid, dust, h⟩ := DyadicOwnerDustPreparation.exists_dust_prepared_owner
    H cfg.matrices cfg.hermitian cfg.contractions hupper hupper1 cfg.depth cfg.depth_positive
    cfg.weight_positive hL (by norm_num [epochDustThreshold] : 0 < epochDustThreshold) hk
  refine ⟨C, paid, dust, preparedCovariance_of_dustPrepared cfg H hbudget h, ?_⟩
  have hp := h.paid_le cfg.contractions hupper hupper1 hL hk
  norm_num only [epochTracePriceScale] at hp
  linarith

end DyadicEpochPreparation
end MatrixSpencer
