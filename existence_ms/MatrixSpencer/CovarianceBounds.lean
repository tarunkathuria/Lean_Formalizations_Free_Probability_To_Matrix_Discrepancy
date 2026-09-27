import MatrixSpencer.CovarianceSource
import MatrixSpencer.Statement

/-!
# Source budgets from the original contractions

The covariance remains real and bounded by the coefficient identity. All
matrix norms in this module are Euclidean operator norms.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

local instance covarianceBoundsCStarAlgebra : CStarAlgebra (Matrix n n ℂ) := {}

omit [Fintype ι] [DecidableEq ι] in
/-- A Hermitian Euclidean contraction has its square bounded by the identity. -/
theorem hermitian_square_le_one {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hN : ‖A‖ ≤ 1) : A * A ≤ 1 := by
  have hp : (A * A).PosSemidef := by
    simpa only [hA.eq] using Matrix.posSemidef_conjTranspose_mul_self A
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg (A * A) hp.nonneg).mp
  calc
    ‖A * A‖ ≤ ‖A‖ * ‖A‖ := norm_mul_le _ _
    _ ≤ 1 * 1 := mul_le_mul hN hN (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The actual source variance bound uses the count of original labels. -/
theorem covarianceSource_identity_le_card (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC : C ≤ 1) :
    covarianceSource A C (1 : Matrix n n ℂ) ≤ (Fintype.card ι : ℝ) • 1 := by
  calc
    _ ≤ covarianceSource A 1 1 := covarianceSource_mono A hA hC Matrix.PosSemidef.one
    _ = ∑ i, A i * A i := covarianceSource_one_one A
    _ ≤ ∑ _ : ι, (1 : Matrix n n ℂ) :=
      Finset.sum_le_sum fun i _ => hermitian_square_le_one (hA i) (hN i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

/-- The trace budget is valid for every positive density, normalized or not. -/
theorem realTrace_covarianceSource_le_card (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    realTrace (covarianceSource A C S) ≤ (Fintype.card ι : ℝ) * realTrace S := by
  have hid := realTrace_covarianceSource_selfadjoint A hA hC0 S 1
  rw [Matrix.mul_one] at hid
  rw [hid]
  have h := realTrace_mul_mono hS (covarianceSource_identity_le_card A hA hN hC1)
  simpa only [Matrix.mul_smul, Matrix.mul_one, realTrace_smul] using h

/-- On trace-one densities, the source trace is at most the retained label count. -/
theorem density_covarianceSource_trace_le_card (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    realTrace (covarianceSource A C S) ≤ (Fintype.card ι : ℝ) := by
  simpa only [hS.2, mul_one] using realTrace_covarianceSource_le_card A hA hN hC0 hC1 hS.1

end MatrixSpencer
