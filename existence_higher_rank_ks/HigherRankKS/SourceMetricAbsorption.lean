import HigherRankKS.SylvesterMetric

/-! Absorbing the internal source response in the actual inverse-Sylvester metric. -/

open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section
namespace HigherRankKS.SylvesterMetric

variable {n : Type*} [Fintype n] [DecidableEq n]

@[simp] theorem inverse_add (W : Matrix n n ℂ) (hW : W.PosDef)
    (X Y : Matrix n n ℂ) :
    inverse W hW (X + Y) = inverse W hW X + inverse W hW Y :=
  (sylvesterEquiv W hW).symm.map_add X Y

theorem energy_smul_add (W : Matrix n n ℂ) (hW : W.PosDef)
    (X Y : Matrix n n ℂ) (a b : ℝ) :
    energy W hW (a • X + b • Y) =
      a ^ 2 * energy W hW X +
        2 * a * b * realTrace (X * inverse W hW Y) +
        b ^ 2 * energy W hW Y := by
  simp only [energy, inverse_add, inverse_real_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    realTrace_add, realTrace_smul]
  rw [← trace_inverse_selfAdjoint W hW X Y]
  ring

/-- Exact quadratic absorption; the source estimate pays one half of its
curvature and changes the remaining transport coefficient to beta. -/
theorem source_metric_absorption (W : Matrix n n ℂ) (hW : W.PosDef)
    {X R : Matrix n n ℂ} (hX : X.IsHermitian) (hR : R.IsHermitian)
    {β C : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hsource : energy W hW R ≤ (1 - β) / (2 * β) * C) :
    β * energy W hW X ≤ energy W hW (X - R) + C / 2 := by
  have hα : 0 < 1 - β := sub_pos.mpr hβ1
  have hXR : ((1 - β) • X + (-1 : ℝ) • R).IsHermitian := by
    change ((1 - β) • X + (-1 : ℝ) • R)ᴴ = (1 - β) • X + (-1 : ℝ) • R
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      star_trivial, hX.eq, hR.eq]
  have hpos := energy_nonneg W hW hXR
  rw [energy_smul_add] at hpos
  have hsub : energy W hW (X - R) =
      energy W hW X - 2 * realTrace (X * inverse W hW R) + energy W hW R := by
    have h := energy_smul_add W hW X R 1 (-1)
    simp only [one_smul, neg_one_smul, ← sub_eq_add_neg, one_pow, neg_one_sq,
      mul_one, one_mul, mul_neg] at h
    linarith
  have hweighted : β * energy W hW R ≤ (1 - β) / 2 * C := by
    calc
      _ ≤ β * ((1 - β) / (2 * β) * C) :=
        mul_le_mul_of_nonneg_left hsource hβ.le
      _ = (1 - β) / 2 * C := by field_simp
  apply (mul_le_mul_iff_right₀ hα).mp
  rw [hsub]
  nlinarith

end HigherRankKS.SylvesterMetric
