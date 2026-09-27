import HigherRankKS.SylvesterMetric

open Matrix MatrixSpencer
open scoped MatrixOrder ComplexOrder
noncomputable section
namespace HigherRankKS.SylvesterMetric
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem inverse_smul_weight (W : Matrix n n ℂ) (hW : W.PosDef)
    {c : ℝ} (hc : 0 < c) (R : Matrix n n ℂ) :
    inverse (c • W) (hW.smul hc) R = c⁻¹ • inverse W hW R := by
  apply sylvester_injective (hW.smul hc)
  rw [inverse_solve]
  have hs : sylvester (c • W) (c⁻¹ • inverse W hW R) =
      (c * c⁻¹) • sylvester W (inverse W hW R) := by
    simp only [sylvester_apply, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add]
    rw [mul_comm c⁻¹ c]
  rw [hs, mul_inv_cancel₀ hc.ne', one_smul, inverse_solve]

theorem energy_smul_weight (W : Matrix n n ℂ) (hW : W.PosDef)
    {c : ℝ} (hc : 0 < c) (R : Matrix n n ℂ) :
    energy (c • W) (hW.smul hc) R = c⁻¹ * energy W hW R := by
  simp only [energy, inverse_smul_weight W hW hc, Matrix.mul_smul, realTrace_smul]

theorem energy_smul_both (W : Matrix n n ℂ) (hW : W.PosDef)
    {c : ℝ} (hc : 0 < c) (R : Matrix n n ℂ) :
    energy (c • W) (hW.smul hc) (c • R) = c * energy W hW R := by
  rw [energy_smul_weight W hW hc, energy_real_smul]
  have hc0 := hc.ne'
  field_simp

end HigherRankKS.SylvesterMetric
