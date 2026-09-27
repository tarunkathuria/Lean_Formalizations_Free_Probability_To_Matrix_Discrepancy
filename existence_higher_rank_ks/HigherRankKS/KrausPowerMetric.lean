import HigherRankKS.PowerGramMetric
import HigherRankKS.SylvesterScaling

/-!
# Inverse-Sylvester control of the actual fractional-power derivative

Finite rectangular Kraus outputs are combined before the inverse metric
is taken. The estimate is derived from the exact resolvent Gram integral,
with no assumed source or derivative certificate.
-/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS.PowerGramMetric

open MatrixPowerDifferential IntegratedSylvesterMetric SylvesterMetric

variable {ι n m : Type*} [Fintype ι] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- A finite rectangular Kraus output, with no normalization assumption. -/
def krausMap (K : ι → Matrix m n ℂ) : Matrix n n ℂ →L[ℝ] Matrix m m ℂ :=
  ∑ j, sandwich (K j)

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
@[simp] theorem krausMap_apply (K : ι → Matrix m n ℂ) (X : Matrix n n ℂ) :
    krausMap K X = ∑ j, K j * X * (K j)ᴴ := by
  simp only [krausMap, ContinuousLinearMap.sum_apply, sandwich_apply]

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem krausMap_isHermitian (K : ι → Matrix m n ℂ) {X : Matrix n n ℂ}
    (hX : X.IsHermitian) : (krausMap K X).IsHermitian := by
  change (krausMap K X)ᴴ = krausMap K X
  simp only [krausMap_apply, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hX.eq, Matrix.mul_assoc]

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
theorem variational_sum (W R : ι → Matrix m m ℂ) (Y : Matrix m m ℂ) :
    variational (∑ j, W j) (∑ j, R j) Y = ∑ j, variational (W j) (R j) Y := by
  simp only [variational, sylvester_apply, Matrix.sum_mul,
    Matrix.mul_add, realTrace_sum, realTrace_add, Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem kraus_variational_le {α : ℝ} (hα : α ∈ Ioo 0 1)
    (K : ι → Matrix m n ℂ) (M U : selfAdjoint (Matrix n n ℂ))
    (hM : (M : Matrix n n ℂ).PosDef) {Y : Matrix m m ℂ} (hY : Y.IsHermitian) :
    variational ((α * (1 - α)) • krausMap K (power α M))
      ((2 * (1 - α)) • krausMap K (first α M U)) Y ≤
        2 * (-realTrace (krausMap K (second α M U U))) := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun j _ =>
    single_variational_le hα (K j) M U hM hY
  simpa only [krausMap_apply, Finset.smul_sum, variational_sum, sandwich_apply,
    realTrace_neg, realTrace_sum, ← Finset.mul_sum, Finset.sum_neg_distrib] using h

/-- Curvature is nonnegative even if the Kraus output is singular. -/
theorem power_curvature_nonneg {α : ℝ} (hα : α ∈ Ioo 0 1)
    (K : ι → Matrix m n ℂ) (M U : selfAdjoint (Matrix n n ℂ))
    (hM : (M : Matrix n n ℂ).PosDef) :
    0 ≤ -realTrace (krausMap K (second α M U U)) := by
  have h := kraus_variational_le hα K M U hM
    (show (0 : Matrix m m ℂ).IsHermitian from by simp [Matrix.IsHermitian])
  simp only [variational, realTrace_zero, mul_zero,
    sylvester_apply, Matrix.zero_mul, add_zero, sub_zero] at h
  linarith

/-- The actual fractional-power derivative is controlled in the inverse
Sylvester metric by its own actual Hessian, for every finite rectangular
Kraus output whose value is positive definite. -/
theorem power_energy_le {α : ℝ} (hα : α ∈ Ioo 0 1)
    (K : ι → Matrix m n ℂ) (M U : selfAdjoint (Matrix n n ℂ))
    (hM : (M : Matrix n n ℂ).PosDef)
    (hW : (krausMap K (power α M)).PosDef) :
    energy (krausMap K (power α M)) hW (krausMap K (first α M U)) ≤
      α / (2 * (1 - α)) * (-realTrace (krausMap K (second α M U U))) := by
  let W := krausMap K (power α M)
  let R := krausMap K (first α M U)
  let C := -realTrace (krausMap K (second α M U U))
  have hb : 0 < 1 - α := sub_pos.mpr hα.2
  have hc : 0 < α * (1 - α) := mul_pos hα.1 hb
  have hR : R.IsHermitian := krausMap_isHermitian K (first_isHermitian hα M U hM)
  have hRc : ((2 * (1 - α)) • R).IsHermitian := by
    change (((2 * (1 - α)) • R)ᴴ) = _
    simp only [Matrix.conjTranspose_smul, star_trivial, hR.eq]
  have h := kraus_variational_le hα K M U hM
    (inverse_isHermitian ((α * (1 - α)) • W) (hW.smul hc) hRc)
  rw [variational_inverse] at h
  rw [energy_real_smul, energy_smul_weight W hW hc] at h
  change (2 * (1 - α)) ^ 2 * ((α * (1 - α))⁻¹ * energy W hW R) ≤ 2 * C at h
  have he : (2 * (1 - α)) ^ 2 * ((α * (1 - α))⁻¹ * energy W hW R) =
      (4 * (1 - α) / α) * energy W hW R := by
    field_simp [hα.1.ne', hb.ne']
    ring
  rw [he] at h
  calc
    energy W hW R = (α / (4 * (1 - α))) *
        ((4 * (1 - α) / α) * energy W hW R) := by
      field_simp [hα.1.ne', hb.ne']
    _ ≤ (α / (4 * (1 - α))) * (2 * C) :=
      mul_le_mul_of_nonneg_left h (div_nonneg hα.1.le (mul_nonneg (by norm_num) hb.le))
    _ = α / (2 * (1 - α)) * C := by field_simp; ring

end HigherRankKS.PowerGramMetric
