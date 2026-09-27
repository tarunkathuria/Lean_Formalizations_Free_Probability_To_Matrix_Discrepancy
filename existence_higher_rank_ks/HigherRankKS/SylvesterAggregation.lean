import HigherRankKS.KrausPowerMetric
import HigherRankKS.SourceMetricAbsorption
import Mathlib.Algebra.QuadraticDiscriminant

open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section
namespace HigherRankKS.SylvesterMetric

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- At fixed test matrix, the variational expression is linear in its
two source inputs. -/
theorem variational_smul_both (W R Y : Matrix n n ℂ) (c : ℝ) :
    variational (c • W) (c • R) Y = c * variational W R Y := by
  simp only [variational, sylvester_apply, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_add, realTrace_add, realTrace_smul]
  ring

omit [DecidableEq n] in
/-- Weighted sums of source outputs can be combined before taking any
inverse; individual source outputs need not be invertible. -/
theorem variational_weighted_sum (W R : ι → Matrix n n ℂ) (c : ι → ℝ)
    (Y : Matrix n n ℂ) :
    variational (∑ i, c i • W i) (∑ i, c i • R i) Y =
      ∑ i, c i * variational (W i) (R i) Y := by
  rw [PowerGramMetric.variational_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact variational_smul_both _ _ _ _

/-- A variational source estimate gives the actual inverse metric bound.
This algebraic lemma is used only after the concrete carrier estimates
have been summed. -/
theorem energy_le_of_source_variational (W R : Matrix n n ℂ) (hW : W.PosDef)
    (hR : R.IsHermitian) {β C : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hv : ∀ Y : Matrix n n ℂ, Y.IsHermitian →
      variational (((1 - β) * β) • W) ((2 * β) • R) Y ≤ 2 * C) :
    energy W hW R ≤ (1 - β) / (2 * β) * C := by
  have ha : 0 < 1 - β := sub_pos.mpr hβ1
  have hc : 0 < (1 - β) * β := mul_pos ha hβ
  have hRc : ((2 * β) • R).IsHermitian :=
    (IsSelfAdjoint.all (2 * β)).smul hR.isSelfAdjoint
  have h := hv (inverse (((1 - β) * β) • W) (hW.smul hc) ((2 * β) • R))
    (inverse_isHermitian _ (hW.smul hc) hRc)
  rw [variational_inverse, energy_real_smul, energy_smul_weight W hW hc] at h
  have he : (2 * β) ^ 2 * (((1 - β) * β)⁻¹ * energy W hW R) =
      (4 * β / (1 - β)) * energy W hW R := by
    field_simp [hβ.ne', ha.ne']
    ring
  rw [he] at h
  calc
    energy W hW R = ((1 - β) / (4 * β)) *
        ((4 * β / (1 - β)) * energy W hW R) := by field_simp
    _ ≤ ((1 - β) / (4 * β)) * (2 * C) :=
      mul_le_mul_of_nonneg_left h (div_nonneg ha.le (mul_nonneg (by norm_num) hβ.le))
    _ = (1 - β) / (2 * β) * C := by field_simp; ring

/-- Scalar trace control is already contained in the variational source
bound, including when its weight matrix is singular. -/
theorem trace_sq_le_of_source_variational (W R : Matrix n n ℂ)
    {β C : ℝ} (hβ : 0 < β)
    (hv : ∀ Y : Matrix n n ℂ, Y.IsHermitian →
      variational (((1 - β) * β) • W) ((2 * β) • R) Y ≤ 2 * C) :
    (realTrace R) ^ 2 ≤ (1 - β) / β * realTrace W * C := by
  have hpoly : ∀ t : ℝ,
      (-2 * ((1 - β) * β) * realTrace W) * (t * t) +
        (4 * β * realTrace R) * t + (-2 * C) ≤ 0 := by
    intro t
    have h := hv (t • (1 : Matrix n n ℂ))
      ((IsSelfAdjoint.all t).smul (show IsSelfAdjoint (1 : Matrix n n ℂ) from IsSelfAdjoint.one (Matrix n n ℂ)))
    simp only [variational, sylvester_apply, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_add, realTrace_add, realTrace_smul] at h
    nlinarith
  have hd := discrim_le_zero_of_nonpos hpoly
  unfold discrim at hd
  have hs : β * (realTrace R) ^ 2 ≤ (1 - β) * realTrace W * C := by
    apply (mul_le_mul_iff_right₀ hβ).mp
    nlinarith [hd]
  apply (mul_le_mul_iff_right₀ hβ).mp
  calc
    β * realTrace R ^ 2 ≤ (1 - β) * realTrace W * C := hs
    _ = β * ((1 - β) / β * realTrace W * C) := by field_simp

omit [DecidableEq n] in
/-- Scaling a Hermitian test is the same as scaling the two variational
inputs quadratically and linearly. -/
theorem variational_smul_test (W R Y : Matrix n n ℂ) (b : ℝ) :
    variational (b ^ 2 • W) (b • R) Y = variational W R (b • Y) := by
  simp only [variational, sylvester_apply, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_add, realTrace_add, realTrace_smul]
  ring

/-- Scalar probes may have arbitrary signs; only the source coefficients
must be nonnegative. This is the aggregation form used for mixed terms. -/
theorem trace_probe_sq_le_of_variational (W R : ι → Matrix n n ℂ) (C c b : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) {β : ℝ} (hβ : 0 < β)
    (hv : ∀ i, ∀ Y : Matrix n n ℂ, Y.IsHermitian →
      variational (((1 - β) * β) • W i) ((2 * β) • R i) Y ≤ 2 * C i) :
    (∑ i, c i * b i * realTrace (R i)) ^ 2 ≤ (1 - β) / β *
      (∑ i, c i * b i ^ 2 * realTrace (W i)) * (∑ i, c i * C i) := by
  have hagg : ∀ Y : Matrix n n ℂ, Y.IsHermitian →
      variational (((1 - β) * β) • ∑ i, c i • (b i ^ 2 • W i))
        ((2 * β) • ∑ i, c i • (b i • R i)) Y ≤ 2 * ∑ i, c i * C i := by
    intro Y hY
    have hs : variational (((1 - β) * β) • ∑ i, c i • (b i ^ 2 • W i))
        ((2 * β) • ∑ i, c i • (b i • R i)) Y =
        ∑ i, c i * variational (((1 - β) * β) • W i) ((2 * β) • R i) (b i • Y) := by
      simp only [Finset.smul_sum, smul_comm ((1 - β) * β), smul_comm (2 * β)]
      rw [variational_weighted_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [variational_smul_test]
    rw [hs, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left
      (hv i (b i • Y) ((IsSelfAdjoint.all (b i)).smul hY.isSelfAdjoint)) (hc i)
    nlinarith
  have h := trace_sq_le_of_source_variational _ _ hβ hagg
  simpa only [realTrace_sum, realTrace_smul, mul_assoc] using h

end HigherRankKS.SylvesterMetric
