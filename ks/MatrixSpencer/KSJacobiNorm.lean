import MatrixSpencer.KSJacobiMatrixSqrt

/-!
# A finite Jacobi upper report for the real operator norm

The routine performs the specified finite Jacobi run, scans the absolute
diagonal entries using real comparisons, and adds its residual tolerance.
No matrix norm or spectral vector is evaluated by the definition of the
report. Its correctness is proved against the Euclidean operator norm.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSJacobiNorm

open KSJacobiRayleigh
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem orthogonal_conjugation_norm (A U : Matrix ι ι ℝ)
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) : ‖Uᵀ * A * U‖ = ‖A‖ := by
  have h₁ := KSJacobiMatrixSqrt.orthogonal_conjugation_operatorNorm_le A Uᵀ
    (by simpa only [Matrix.transpose_transpose] using hU')
    (by simpa only [Matrix.transpose_transpose] using hU)
  simp only [Matrix.transpose_transpose] at h₁
  have h₂ := KSJacobiMatrixSqrt.orthogonal_conjugation_operatorNorm_le (Uᵀ * A * U) U hU hU'
  have hid : U * (Uᵀ * A * U) * Uᵀ = A := by
    calc
      _ = (U * Uᵀ) * A * (U * Uᵀ) := by noncomm_ring
      _ = A := by rw [hU']; simp
  rw [hid] at h₂
  exact le_antisymm h₁ h₂

variable {d : ℕ}

theorem finalMatrix_norm (A : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) :
    ‖finalMatrix A ν‖ = ‖A‖ := by
  unfold finalMatrix
  rw [KSJacobiIteration.run_eq_conjugation]
  exact orthogonal_conjugation_norm A _
    (KSJacobiIteration.accumulatedBasis_transpose_mul A _)
    (KSJacobiIteration.accumulatedBasis_mul_transpose A _)

/-- A comparison scan, with value zero for the empty diagonal. -/
def maxAbsDiagonal (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  match KSJacobiIteration.maxScan (fun i => |A i i|) (List.finRange d) with
  | none => 0
  | some i => |A i i|

theorem maxAbsDiagonal_nonneg (A : Matrix (Fin d) (Fin d) ℝ) :
    0 ≤ maxAbsDiagonal A := by
  unfold maxAbsDiagonal
  split <;> positivity

theorem diagonal_le_maxAbsDiagonal (A : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    |A j j| ≤ maxAbsDiagonal A := by
  cases hs : KSJacobiIteration.maxScan (fun i => |A i i|) (List.finRange d) with
  | none =>
    have hnil := (KSJacobiIteration.maxScan_none_iff _ _).mp hs
    have hj := List.mem_finRange j
    rw [hnil] at hj
    exact False.elim (List.not_mem_nil hj)
  | some i =>
    simpa only [maxAbsDiagonal, hs] using
      KSJacobiIteration.maxScan_maximal _ _ hs (List.mem_finRange j)

theorem maxAbsDiagonal_le_norm (A : Matrix (Fin d) (Fin d) ℝ) :
    maxAbsDiagonal A ≤ ‖A‖ := by
  cases hs : KSJacobiIteration.maxScan (fun i => |A i i|) (List.finRange d) with
  | none => simpa only [maxAbsDiagonal, hs] using norm_nonneg A
  | some i =>
    have h := KSRayleighAccuracy.realRayleigh_abs_le_norm A (EuclideanSpace.single i 1)
      (by simp only [EuclideanSpace.norm_single, norm_one])
    simpa only [maxAbsDiagonal, hs, realRayleigh_single] using h

theorem diagonalPart_norm_le (A : Matrix (Fin d) (Fin d) ℝ) :
    ‖diagonalPart A‖ ≤ maxAbsDiagonal A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (maxAbsDiagonal_nonneg A)
  intro v
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (maxAbsDiagonal_nonneg A) (norm_nonneg _))).mp
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, mul_pow]
  change (∑ i, ((diagonalPart A) *ᵥ WithLp.ofLp v) i ^ 2) ≤
    maxAbsDiagonal A ^ 2 * ∑ i, v i ^ 2
  simp only [diagonalPart, Matrix.mulVec_diagonal]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (A i i))
    (diagonal_le_maxAbsDiagonal A i) 2

/-- Entirely real finite computation: Jacobi, a diagonal comparison scan,
and addition of the requested tolerance. -/
def report (A : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) : ℝ :=
  maxAbsDiagonal (finalMatrix A ν) + ν

/-- The additive error is at most one tolerance. The upper certificate
includes the actual off-diagonal residual; the lower estimate uses diagonal
Rayleigh values in the actually computed orthogonal basis. -/
theorem report_accuracy (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm)
    {ν : ℝ} (hν : 0 < ν) : ‖A‖ ≤ report A ν ∧ report A ν ≤ ‖A‖ + ν := by
  have hr : ‖finalMatrix A ν - diagonalPart (finalMatrix A ν)‖ ≤ ν :=
    (residual_operatorNorm _).trans
      (KSJacobiIteration.run_offDiagonalFrobenius_accuracy A hA hν)
  constructor
  · calc
      ‖A‖ = ‖finalMatrix A ν‖ := (finalMatrix_norm A ν).symm
      _ ≤ ‖finalMatrix A ν - diagonalPart (finalMatrix A ν)‖ +
          ‖diagonalPart (finalMatrix A ν)‖ := norm_le_norm_sub_add _ _
      _ ≤ ν + maxAbsDiagonal (finalMatrix A ν) := add_le_add hr (diagonalPart_norm_le _)
      _ = report A ν := by unfold report; ring
  · exact add_le_add_right ((maxAbsDiagonal_le_norm _).trans_eq (finalMatrix_norm A ν)) ν

end MatrixSpencer.KSJacobiNorm
