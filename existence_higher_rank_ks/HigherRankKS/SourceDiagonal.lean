import HigherRankKS.SpinSymmetry
import HigherRankKS.TwoFrames
import MatrixSpencer.KSEighthBlocks

/-! The weighted frame diagonal is bounded by the actual nonlinear source probe. -/

open Matrix MatrixSpencer MatrixSpencer.KSEighthBlocks
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem carrier_trace_product {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (S Z : Matrix n n ℂ) :
    realTrace ((CFC.sqrt A * S * CFC.sqrt A) * (CFC.sqrt A * Z * CFC.sqrt A)) =
      realTrace (S * A * Z * A) := by
  calc
    _ = realTrace (CFC.sqrt A * (S * (CFC.sqrt A * CFC.sqrt A) * Z * CFC.sqrt A)) := by
      simp only [Matrix.mul_assoc]
    _ = realTrace ((S * (CFC.sqrt A * CFC.sqrt A) * Z * CFC.sqrt A) * CFC.sqrt A) :=
      realTrace_mul_comm _ _
    _ = _ := by rw [Matrix.mul_assoc _ _ (CFC.sqrt A),
      CFC.sqrt_mul_sqrt_self A hA.nonneg]

theorem sourceBlock_trace_pairing (β : ℝ) (A : Matrix n n ℂ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (Z : Matrix n n ℂ) :
    realTrace (Z * sourceBlock β A S) =
      realTrace (carrierPower β (carrier A S) * (CFC.sqrt A * Z * CFC.sqrt A)) := by
  unfold sourceBlock
  calc
    _ = realTrace ((Z * CFC.sqrt A) * carrierPower β (carrier A S) * CFC.sqrt A) := by
      simp only [Matrix.mul_assoc]
    _ = realTrace ((CFC.sqrt A * (Z * CFC.sqrt A)) * carrierPower β (carrier A S)) :=
      realTrace_mul_cycle _ _ _
    _ = realTrace (carrierPower β (carrier A S) * (CFC.sqrt A * (Z * CFC.sqrt A))) :=
      realTrace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem actual_source_diagonal_bound {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {S Z : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) (hZ : Z.PosSemidef)
    (hblock : S = Matrix.fromBlocks S.toBlocks₁₁ 0 0 S.toBlocks₂₂)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    realTrace (S * KSSpinSource.doubled A * Z * KSSpinSource.doubled A) ≤
      realTrace (Z * sourceTerm β A S) := by
  let R := CFC.sqrt A
  let M₁ := R * S.toBlocks₁₁ * R
  let M₂ := R * S.toBlocks₂₂ * R
  let Q₁ := R * Z.toBlocks₁₁ * R
  let Q₂ := R * Z.toBlocks₂₂ * R
  have hR : R.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hM₁ : M₁.PosSemidef := by
    simpa only [hR.eq] using (hS.submatrix Sum.inl).conjTranspose_mul_mul_same R
  have hM₂ : M₂.PosSemidef := by
    simpa only [hR.eq] using (hS.submatrix Sum.inr).conjTranspose_mul_mul_same R
  have hQ₁ : Q₁.PosSemidef := by
    simpa only [hR.eq] using (hZ.submatrix Sum.inl).conjTranspose_mul_mul_same R
  have hQ₂ : Q₂.PosSemidef := by
    simpa only [hR.eq] using (hZ.submatrix Sum.inr).conjTranspose_mul_mul_same R
  have hleft : realTrace (S * KSSpinSource.doubled A * Z * KSSpinSource.doubled A) =
      realTrace (M₁ * Q₁) + realTrace (M₂ * Q₂) := by
    rw [show realTrace (M₁ * Q₁) = realTrace (S.toBlocks₁₁ * A * Z.toBlocks₁₁ * A) from
      carrier_trace_product hA _ _,
      show realTrace (M₂ * Q₂) = realTrace (S.toBlocks₂₂ * A * Z.toBlocks₂₂ * A) from
      carrier_trace_product hA _ _]
    conv_lhs => arg 1; arg 1; arg 1; rw [hblock]
    conv_lhs => arg 1; arg 1; arg 2; rw [← Matrix.fromBlocks_toBlocks Z]
    simp only [KSSpinSource.doubled, Matrix.fromBlocks_multiply, Matrix.mul_zero,
      Matrix.zero_mul, zero_add, add_zero]
    simp [realTrace, Matrix.trace, Matrix.diag, Fintype.sum_sum_type]
  have hright : realTrace (Z * sourceTerm β A S) =
      realTrace (carrierPower β (M₁ + M₂) * (Q₁ + Q₂)) := by
    change realTrace (Z * blockDiag (sourceBlock β A S) (sourceBlock β A S)) = _
    rw [realTrace_mul_blockDiag, sourceBlock_trace_pairing, sourceBlock_trace_pairing]
    have hm : carrier A S = M₁ + M₂ := by
      simp only [carrier, marginal, Matrix.mul_add, Matrix.add_mul, M₁, M₂, R]
    rw [hm, Matrix.mul_add, realTrace_add]
  rw [hleft, hright]
  exact TwoFrames.cross_spin_trace_le hM₁ hM₂ hQ₁ hQ₂ hβ hβ1

end HigherRankKS
