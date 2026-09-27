import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# Complex contraction for a positive matrix partition of the identity

The coefficients are genuinely complex. The resulting weighted matrix need
not be Hermitian or normal. An explicit square-root dilation factors the
weighted sum through a diagonal complex contraction, proving the sharp
uniform coefficient bound in Euclidean operator norm.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSComplexRelativeSource

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

/-- Stack the positive square roots in disjoint row blocks. -/
def dilation (E : ι → Matrix n n ℂ) : Matrix (ι × n) n ℂ :=
  fun ik j => CFC.sqrt (E ik.1) ik.2 j

omit [DecidableEq ι] in
theorem dilation_gram (E : ι → Matrix n n ℂ) (hE : ∀ i, (E i).PosSemidef) :
    (dilation E)ᴴ * dilation E = ∑ i, E i := by
  have he (i : ι) : (CFC.sqrt (E i))ᴴ * CFC.sqrt (E i) = E i := by
    rw [(CFC.sqrt_nonneg (E i)).posSemidef.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self (E i) (hE i).nonneg]
  calc
    _ = ∑ i, (CFC.sqrt (E i))ᴴ * CFC.sqrt (E i) := by
      ext j k
      simp [Matrix.sum_apply, Matrix.mul_apply, dilation, Fintype.sum_prod_type]
    _ = _ := by simp only [he]

/-- The complex coefficients act diagonally on the enlarged space. -/
def coefficientDiagonal (a : ι → ℂ) : Matrix (ι × n) (ι × n) ℂ :=
  Matrix.diagonal (fun ik => a ik.1)

theorem dilation_factorization (E : ι → Matrix n n ℂ) (hE : ∀ i, (E i).PosSemidef)
    (a : ι → ℂ) :
    (dilation E)ᴴ * coefficientDiagonal (n := n) a * dilation E = ∑ i, a i • E i := by
  have he (i : ι) : (CFC.sqrt (E i))ᴴ * CFC.sqrt (E i) = E i := by
    rw [(CFC.sqrt_nonneg (E i)).posSemidef.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self (E i) (hE i).nonneg]
  calc
    _ = ∑ i, a i • ((CFC.sqrt (E i))ᴴ * CFC.sqrt (E i)) := by
      ext j k
      rw [Matrix.mul_apply]
      simp only [coefficientDiagonal, Matrix.mul_diagonal]
      simp only [Matrix.mul_apply,
        Matrix.conjTranspose_apply, dilation, Fintype.sum_prod_type,
        Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by simp only [he]

/-- The diagonal coefficient matrix has the supplied operator bound. -/
theorem coefficientDiagonal_norm_le (a : ι → ℂ) {R : ℝ}
    (hR : 0 ≤ R) (ha : ∀ i, ‖a i‖ ≤ R) : ‖coefficientDiagonal (n := n) a‖ ≤ R := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (coefficientDiagonal (n := n) a)‖ ≤ R
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg x))).mp
  simp only [EuclideanSpace.norm_sq_eq, mul_pow]
  change (∑ j : ι × n, ‖(coefficientDiagonal a *ᵥ WithLp.ofLp x) j‖ ^ 2) ≤
    R ^ 2 * ∑ j : ι × n, ‖x j‖ ^ 2
  simp only [coefficientDiagonal, Matrix.mulVec_diagonal, norm_mul, mul_pow]
  calc
    _ ≤ ∑ j : ι × n, R ^ 2 * ‖x j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha j.1) 2)
        (sq_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

omit [DecidableEq ι] in
theorem dilation_norm_one [Nonempty n] (E : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).PosSemidef) (hsum : (∑ i, E i) = 1) : ‖dilation E‖ = 1 := by
  have hh := Matrix.l2_opNorm_conjTranspose_mul_self (dilation E)
  rw [dilation_gram E hE, hsum, norm_one] at hh
  nlinarith [norm_nonneg (dilation E)]

/-- The sharp complex coefficient contraction. No self-adjointness or
normality of the weighted sum is assumed. Empty physical dimensions are
included, with the conventional zero operator norm. -/
theorem partition_contraction (E : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).PosSemidef) (hsum : (∑ i, E i) = 1)
    (a : ι → ℂ) {R : ℝ} (hR : 0 ≤ R) (ha : ∀ i, ‖a i‖ ≤ R) :
    ‖∑ i, a i • E i‖ ≤ R := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    letI := hn
    rw [show (∑ i, a i • E i) = 0 from Subsingleton.elim _ _, norm_zero]
    exact hR
  | inr hn =>
    letI := hn
    rw [← dilation_factorization E hE a]
    calc
      _ ≤ ‖(dilation E)ᴴ * coefficientDiagonal (n := n) a‖ * ‖dilation E‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ (‖(dilation E)ᴴ‖ * ‖coefficientDiagonal (n := n) a‖) * ‖dilation E‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = ‖coefficientDiagonal (n := n) a‖ := by
        rw [Matrix.l2_opNorm_conjTranspose, dilation_norm_one E hE hsum]
        ring
      _ ≤ R := coefficientDiagonal_norm_le a hR ha

/-- The finite function norm is the maximum absolute complex coefficient. -/
theorem partition_contraction_sup_norm (E : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).PosSemidef) (hsum : (∑ i, E i) = 1) (a : ι → ℂ) :
    ‖∑ i, a i • E i‖ ≤ ‖a‖ :=
  partition_contraction E hE hsum a (norm_nonneg _) (fun i => norm_le_pi_norm a i)

/-- The same bound with the Euclidean operator-norm map spelled out. -/
theorem partition_operatorNorm_contraction (E : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).PosSemidef) (hsum : (∑ i, E i) = 1)
    (a : ι → ℂ) {R : ℝ} (hR : 0 ≤ R) (ha : ∀ i, ‖a i‖ ≤ R) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (∑ i, a i • E i)‖ ≤ R :=
  partition_contraction E hE hsum a hR ha

/-- The relative perturbation version of the complex contraction. -/
theorem partition_perturbation (E : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).PosSemidef) (hsum : (∑ i, E i) = 1)
    (e : ι → ℂ) {R : ℝ} (hR : 0 ≤ R) (he : ∀ i, ‖e i‖ ≤ R) :
    ‖(∑ i, (1 + e i) • E i) - 1‖ ≤ R := by
  have hid : (∑ i, (1 + e i) • E i) - 1 = ∑ i, e i • E i := by
    simp only [add_smul, one_smul, Finset.sum_add_distrib, hsum]
    abel
  rw [hid]
  exact partition_contraction E hE hsum e hR he

variable {m : Type*} [Fintype m] [DecidableEq m]

omit [DecidableEq ι] [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem conjugate_complex_sum (A : ι → Matrix n n ℂ) (W : Matrix m n ℂ) (a : ι → ℂ) :
    W * (∑ i, a i • A i) * Wᴴ = ∑ i, a i • (W * A i * Wᴴ) := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Exact compression and whitening of arbitrary positive source pieces.
Only the normalization identity on the target support is required. The
source pieces may have arbitrary kernels; no smallest eigenvalue appears. -/
theorem whitened_source_contraction (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (W : Matrix m n ℂ)
    (hnormalized : W * (∑ i, A i) * Wᴴ = 1)
    (a : ι → ℂ) {R : ℝ} (hR : 0 ≤ R) (ha : ∀ i, ‖a i‖ ≤ R) :
    ‖W * (∑ i, a i • A i) * Wᴴ‖ ≤ R := by
  rw [conjugate_complex_sum]
  apply partition_contraction (fun i => W * A i * Wᴴ)
    (fun i => (hA i).mul_mul_conjTranspose_same W) _ a hR ha
  rwa [Matrix.mul_sum, Matrix.sum_mul] at hnormalized

/-- Complex relative perturbation after exact compression and whitening. -/
theorem whitened_source_perturbation (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (W : Matrix m n ℂ)
    (hnormalized : W * (∑ i, A i) * Wᴴ = 1)
    (e : ι → ℂ) {R : ℝ} (hR : 0 ≤ R) (he : ∀ i, ‖e i‖ ≤ R) :
    ‖W * (∑ i, (1 + e i) • A i) * Wᴴ - 1‖ ≤ R := by
  rw [conjugate_complex_sum]
  apply partition_perturbation (fun i => W * A i * Wᴴ)
    (fun i => (hA i).mul_mul_conjTranspose_same W) _ e hR he
  rwa [Matrix.mul_sum, Matrix.sum_mul] at hnormalized

end MatrixSpencer.KSComplexRelativeSource
