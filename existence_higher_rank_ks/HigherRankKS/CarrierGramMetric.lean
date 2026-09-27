import HigherRankKS.CarrierMetric
import HigherRankKS.KrausPowerMetric

/-! The actual carrier matrix metric bound, including its trace normalization. -/

open Matrix MatrixSpencer Set
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS.CarrierMetric

open PowerGramMetric SylvesterMetric

variable {ι n m : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]
local instance carrierGramInputCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance carrierGramOutputCStar : CStarAlgebra (Matrix m m ℂ) := {}


theorem carrier_energy_le [Nonempty n] {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (K : ι → Matrix m n ℂ) (M U : selfAdjoint (Matrix n n ℂ))
    (hM : (M : Matrix n n ℂ).PosDef)
    (hW : (krausMap K (carrier β M)).PosDef) :
    energy (krausMap K (carrier β M)) hW
      (krausMap K (first β M U -
        (realTrace (U : Matrix n n ℂ) / realTrace (M : Matrix n n ℂ)) • carrier β M)) ≤
      (1 - β) / (2 * β) * (-realTrace (krausMap K (second β M U U))) := by
  let p := realTrace (M : Matrix n n ℂ)
  let a := realTrace (U : Matrix n n ℂ) / p
  let V := U - a • M
  have hp : 0 < p := (Complex.pos_iff.mp hM.trace_pos).1
  have hc : 0 < p ^ β := Real.rpow_pos_of_pos hp β
  have hα : 1 - β ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hβ.2], by linarith [hβ.1]⟩
  have hew : krausMap K (carrier β M) =
      p ^ β • krausMap K (MatrixPowerDifferential.power (1 - β) M) := by
    exact (krausMap K).map_smul (p ^ β) (MatrixPowerDifferential.power (1 - β) M)
  have hwpow : (krausMap K (MatrixPowerDifferential.power (1 - β) M)).PosDef := by
    have h := hW.smul (inv_pos.mpr hc)
    rwa [hew, smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at h
  have hcenter := centered hβ M U hM
  have hr : krausMap K (first β M U - a • carrier β M) =
      p ^ β • krausMap K (MatrixPowerDifferential.first (1 - β) M V) := by
    rw [hcenter.1, map_smul]
  have hh : second β M U U =
      p ^ β • MatrixPowerDifferential.second (1 - β) M V V := hcenter.2
  have hb := power_energy_le hα K M V hM hwpow
  change energy (krausMap K (carrier β M)) hW
    (krausMap K (first β M U - a • carrier β M)) ≤ _
  calc
    energy (krausMap K (carrier β M)) hW
        (krausMap K (first β M U - a • carrier β M)) =
        p ^ β * energy (krausMap K (MatrixPowerDifferential.power (1 - β) M)) hwpow
          (krausMap K (MatrixPowerDifferential.first (1 - β) M V)) := by
      simpa only [← hew, ← hr] using energy_smul_both
        (krausMap K (MatrixPowerDifferential.power (1 - β) M)) hwpow hc
        (krausMap K (MatrixPowerDifferential.first (1 - β) M V))
    _ ≤ p ^ β * ((1 - β) / (2 * (1 - (1 - β))) *
        (-realTrace (krausMap K (MatrixPowerDifferential.second (1 - β) M V V)))) :=
      mul_le_mul_of_nonneg_left hb hc.le
    _ = (1 - β) / (2 * β) * (-realTrace (krausMap K (second β M U U))) := by
      rw [hh, map_smul, realTrace_smul]
      rw [show 1 - (1 - β) = β by ring]
      ring

/-- The actual carrier curvature cost is nonnegative, including singular outputs. -/
theorem carrier_curvature_nonneg [Nonempty n] {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (K : ι → Matrix m n ℂ) (M U : selfAdjoint (Matrix n n ℂ))
    (hM : (M : Matrix n n ℂ).PosDef) :
    0 ≤ -realTrace (krausMap K (second β M U U)) := by
  have hp : 0 < realTrace (M : Matrix n n ℂ) := (Complex.pos_iff.mp hM.trace_pos).1
  rw [(centered hβ M U hM).2, map_smul, realTrace_smul, neg_mul_eq_mul_neg]
  exact mul_nonneg (Real.rpow_nonneg hp.le _) (power_curvature_nonneg
    ⟨by linarith [hβ.2], by linarith [hβ.1]⟩ K M _ hM)

omit [Fintype ι] [Fintype n] [DecidableEq n] [DecidableEq m] in
private theorem variational_smul_both (c : ℝ) (W R Y : Matrix m m ℂ) :
    variational (c • W) (c • R) Y = c * variational W R Y := by
  simp only [variational, sylvester_apply, Matrix.mul_smul, Matrix.smul_mul,
    ← smul_add, realTrace_smul]
  ring

/-- The singular-output form is retained before summing atoms. No individual
output is assumed positive definite. -/
theorem carrier_variational_le [Nonempty n] {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (K : ι → Matrix m n ℂ) (M U : selfAdjoint (Matrix n n ℂ))
    (hM : (M : Matrix n n ℂ).PosDef) {Y : Matrix m m ℂ} (hY : Y.IsHermitian) :
    variational (((1 - β) * β) • krausMap K (carrier β M))
      ((2 * β) • krausMap K (first β M U -
        (realTrace (U : Matrix n n ℂ) / realTrace (M : Matrix n n ℂ)) • carrier β M)) Y ≤
      2 * (-realTrace (krausMap K (second β M U U))) := by
  let p := realTrace (M : Matrix n n ℂ)
  let a := realTrace (U : Matrix n n ℂ) / p
  let V := U - a • M
  have hp : 0 < p := (Complex.pos_iff.mp hM.trace_pos).1
  have hα : 1 - β ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hβ.2], by linarith [hβ.1]⟩
  have hew : krausMap K (carrier β M) =
      p ^ β • krausMap K (MatrixPowerDifferential.power (1 - β) M) :=
    (krausMap K).map_smul (p ^ β) (MatrixPowerDifferential.power (1 - β) M)
  have hcenter := centered hβ M U hM
  have hr : krausMap K (first β M U - a • carrier β M) =
      p ^ β • krausMap K (MatrixPowerDifferential.first (1 - β) M V) := by
    rw [hcenter.1, map_smul]
  have hh : second β M U U =
      p ^ β • MatrixPowerDifferential.second (1 - β) M V V := hcenter.2
  have hw' : ((1 - β) * β) • krausMap K (carrier β M) =
      p ^ β • (((1 - β) * (1 - (1 - β))) •
        krausMap K (MatrixPowerDifferential.power (1 - β) M)) := by
    rw [hew]
    simp only [smul_smul]
    congr 1
    ring
  have hr' : (2 * β) • krausMap K (first β M U - a • carrier β M) =
      p ^ β • ((2 * (1 - (1 - β))) •
        krausMap K (MatrixPowerDifferential.first (1 - β) M V)) := by
    rw [hr]
    simp only [smul_smul]
    congr 1
    ring
  have h := mul_le_mul_of_nonneg_left (kraus_variational_le hα K M V hM hY)
    (Real.rpow_nonneg hp.le β)
  change variational (((1 - β) * β) • krausMap K (carrier β M))
    ((2 * β) • krausMap K (first β M U - a • carrier β M)) Y ≤ _
  rw [hw', hr', variational_smul_both]
  convert h using 1
  rw [hh, map_smul, realTrace_smul]
  ring

end HigherRankKS.CarrierMetric
