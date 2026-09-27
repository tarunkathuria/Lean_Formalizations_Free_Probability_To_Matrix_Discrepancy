import HigherRankKS.CarrierPower

/-! The nonlinear carrier dominates its input, which controls the two-frame diagonal. -/

open Matrix MatrixSpencer
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance carrierOrderCStar : CStarAlgebra (Matrix n n ℂ) := {}

theorem matrix_rpow_eq_cfc_real {M : Matrix n n ℂ} (hM : M.PosSemidef)
    (p : ℝ) : CFC.rpow M p = cfc (fun x : ℝ => x ^ p) M := by
  rw [CFC.rpow, cfc_nnreal_eq_real _ _ hM.nonneg]
  apply cfc_congr
  intro x hx
  simp only [NNReal.coe_rpow,
    Real.toNNReal_of_nonneg (spectrum_nonneg_of_nonneg hM.nonneg hx)]
  rfl

theorem le_carrierPower {M : Matrix n n ℂ} (hM : M.PosSemidef)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) : M ≤ carrierPower β M := by
  have hα : 0 ≤ 1 - β := sub_nonneg.mpr hβ1
  rw [carrierPower, matrix_rpow_eq_cfc_real hM]
  change M ≤ (realTrace M) ^ β • cfc (fun x : ℝ => x ^ (1 - β)) M
  rw [← cfc_smul ((realTrace M) ^ β) (fun x : ℝ => x ^ (1 - β)) M
    (Real.continuous_rpow_const hα).continuousOn]
  conv_lhs => rw [← cfc_id' ℝ M]
  refine cfc_mono ?_ continuousOn_id
    (continuousOn_const.smul (Real.continuous_rpow_const hα).continuousOn)
  intro x hx
  have hx0 := spectrum_nonneg_of_nonneg hM.nonneg hx
  have hxT := (le_algebraMap_iff_spectrum_le hM.isHermitian).mp
    (posSemidef_le_trace_identity hM) x hx
  change x ≤ (realTrace M) ^ β * x ^ (1 - β)
  calc
    x = x ^ β * x ^ (1 - β) := by
      rw [← Real.rpow_add_of_nonneg hx0 hβ hα]
      simp
    _ ≤ (realTrace M) ^ β * x ^ (1 - β) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx0 hxT hβ)
        (Real.rpow_nonneg hx0 _)

theorem trace_pairing_le_carrierPower {M Q : Matrix n n ℂ}
    (hM : M.PosSemidef) (hQ : Q.PosSemidef)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    realTrace (M * Q) ≤ realTrace (carrierPower β M * Q) := by
  simpa only [realTrace_mul_comm] using realTrace_mul_mono hQ (le_carrierPower hM hβ hβ1)

end HigherRankKS
