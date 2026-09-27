import MatrixSpencer.KSObjectiveUpper
import MatrixSpencer.KSOwnerRetirement

/-!
# Input-entry budgets for the actual covariance owner objective

The scalar budgets use only finite sums, absolute values, scalar square roots,
and the real and imaginary input entries. In particular, the positive matrix
square root defining the analytic Kraus family is not evaluated by these
budget formulas. Its covariance identity is used only in their proofs.
-/

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace MatrixSpencer.KSOwnerInputBounds

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

/-- Squared Frobenius energy computed directly from real and imaginary entries. -/
def matrixEnergy (A : Matrix n n ℂ) : ℝ :=
  ∑ i, ∑ j, ((A i j).re ^ 2 + (A i j).im ^ 2)

/-- A strictly positive arithmetic bound for a Hermitian input matrix. -/
def matrixBound (A : Matrix n n ℂ) : ℝ := 1 + Real.sqrt (matrixEnergy A)

omit [DecidableEq n] in
theorem matrixEnergy_nonneg (A : Matrix n n ℂ) : 0 ≤ matrixEnergy A :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)))

omit [DecidableEq n] in
theorem matrixBound_pos (A : Matrix n n ℂ) : 0 < matrixBound A := by
  unfold matrixBound
  positivity

omit [DecidableEq n] in
theorem matrixEnergy_eq_entryEnergy (A : Matrix n n ℂ) : matrixEnergy A = entryEnergy A := by
  simp only [matrixEnergy, entryEnergy, Complex.normSq_apply, pow_two]

omit [DecidableEq n] in
theorem matrixEnergy_eq_trace_square (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    matrixEnergy A = realTrace (A * A) := by
  rw [matrixEnergy_eq_entryEnergy, entryEnergy_eq_realTrace_adjoint_mul, hA.eq]

/-- The computed Frobenius bound controls the physical operator norm. -/
theorem norm_le_matrixBound (A : Matrix n n ℂ) (hA : A.IsHermitian) : ‖A‖ ≤ matrixBound A := by
  have hn := KSObjectiveUpper.norm_sq_le_trace_square hA
  rw [← matrixEnergy_eq_trace_square A hA] at hn
  have hs := Real.sq_sqrt (matrixEnergy_nonneg A)
  have hnorm : ‖A‖ ≤ Real.sqrt (matrixEnergy A) := by
    nlinarith [norm_nonneg A, Real.sqrt_nonneg (matrixEnergy A)]
  unfold matrixBound
  linarith

/-- The center radius is computed by the same entry formula. -/
def centerBound (H : Matrix n n ℂ) : ℝ := matrixBound H

/-- An arithmetic covariance/Kraus budget, without evaluating a covariance square root. -/
def krausBudget (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) : ℝ :=
  1 + ∑ i, ∑ j, |C i j| * matrixBound (A i) * matrixBound (A j)

omit [DecidableEq ι] [DecidableEq n] in
theorem krausBudget_pos (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) : 0 < krausBudget A C := by
  have hs : 0 ≤ ∑ i, ∑ j, |C i j| * matrixBound (A i) * matrixBound (A j) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (matrixBound_pos _).le) (matrixBound_pos _).le))
  unfold krausBudget
  linarith

theorem centerBound_spec (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    0 < centerBound H ∧ ‖H‖ ≤ centerBound H :=
  ⟨matrixBound_pos H, norm_le_matrixBound H hH⟩

omit [DecidableEq ι] in
/-- A triangle estimate bounds the original covariance expression directly. -/
theorem covarianceSource_one_norm (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) : ‖covarianceSource A C 1‖ ≤ krausBudget A C := by
  unfold covarianceSource
  simp only [Matrix.mul_one]
  calc
    ‖∑ i, ∑ j, C i j • (A i * A j)‖ ≤ ∑ i, ‖∑ j, C i j • (A i * A j)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, |C i j| * matrixBound (A i) * matrixBound (A j) := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs]
      have hmul : ‖A i * A j‖ ≤ matrixBound (A i) * matrixBound (A j) :=
        (norm_mul_le _ _).trans (mul_le_mul (norm_le_matrixBound _ (hA i))
          (norm_le_matrixBound _ (hA j)) (norm_nonneg _) (matrixBound_pos _).le)
      have h := mul_le_mul_of_nonneg_left hmul (abs_nonneg (C i j))
      simpa only [mul_assoc] using h
    _ ≤ krausBudget A C := by unfold krausBudget; linarith

/-- The exact source-adjoint identity identifies the analytic Kraus budget matrix. -/
theorem covarianceKraus_sum_eq (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    (∑ i, (covarianceKraus A C i)ᴴ * covarianceKraus A C i) = covarianceSource A C 1 := by
  simpa only [KSSafeRetirement.sourceAdjoint, Matrix.mul_one] using
    KSOwnerRetirement.sourceAdjoint_covarianceKraus A hA hC 1

/-- Fully discharged arithmetic Kraus budget for the actual owner objective. -/
theorem covarianceKraus_budget (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    (∑ i, (covarianceKraus A C i)ᴴ * covarianceKraus A C i) ≤
      krausBudget A C • (1 : Matrix n n ℂ) := by
  rw [covarianceKraus_sum_eq A hA hC]
  have hP := covarianceSource_posSemidef A hA hC Matrix.PosSemidef.one
  have h := (CStarAlgebra.norm_le_iff_le_algebraMap (covarianceSource A C 1)
    (krausBudget_pos A C).le hP.nonneg).mp (covarianceSource_one_norm A hA C)
  simpa only [Algebra.algebraMap_eq_smul_one] using h

/-- The pair of bounds needed by the optimizer floor and quantitative Hessian. -/
theorem owner_input_bounds (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    0 < centerBound H ∧ 0 < krausBudget A C ∧ ‖H‖ ≤ centerBound H ∧
      (∑ i, (covarianceKraus A C i)ᴴ * covarianceKraus A C i) ≤
        krausBudget A C • (1 : Matrix n n ℂ) :=
  ⟨(centerBound_spec H hH).1, krausBudget_pos A C, (centerBound_spec H hH).2,
    covarianceKraus_budget A hA hC⟩

end MatrixSpencer.KSOwnerInputBounds
