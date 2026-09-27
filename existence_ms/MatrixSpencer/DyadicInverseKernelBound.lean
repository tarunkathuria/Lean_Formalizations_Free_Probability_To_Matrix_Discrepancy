import MatrixSpencer.DyadicRootInverseDerivative
import MatrixSpencer.ReciprocalPowerKernel
import MatrixSpencer.DyadicCurvatureCompression
import MatrixSpencer.DyadicTraceBounds

/-! The actual finite polynomial inverse-root operator and its scalar-kernel
bound on Hermitian trace forms. No Hessian bound is assumed. -/

open Matrix
open scoped BigOperators ComplexConjugate MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer
namespace DyadicInverseKernelBound

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance inverseKernelBoundCStar : CStarAlgebra (Matrix n n ℂ) := {}

def polynomialInverse (p : ℕ) (Q B : Matrix n n ℂ) : Matrix n n ℂ :=
  matrixPowerDerivative p Q (Q * B * Q)

lemma polynomialInverse_sum (p : ℕ) (Q B : Matrix n n ℂ) :
    polynomialInverse p Q B = ∑ j ∈ Finset.range p, Q ^ (p - j) * B * Q ^ (j + 1) := by
  rw [polynomialInverse, matrixPowerDerivative_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have he : p - 1 - j + 1 = p - j := by have := Finset.mem_range.mp hj; omega
  calc
    _ = (Q ^ (p - 1 - j) * Q) * B * (Q * Q ^ j) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← pow_succ, ← pow_succ', he]

lemma posDef_natPower {Q : Matrix n n ℂ} (hQ : Q.PosDef) (r : ℕ) : (Q ^ r).PosDef :=
  (hQ.posSemidef.pow r).posDef_iff_isUnit.mpr (hQ.isUnit.pow r)

/-- Strict positivity holds on full complex matrix space. -/
theorem polynomialInverse_quadratic_pos {p : ℕ} (hp : 0 < p)
    {Q B : Matrix n n ℂ} (hQ : Q.PosDef) (hB : B ≠ 0) :
    0 < realTrace (Bᴴ * polynomialInverse p Q B) := by
  rw [polynomialInverse_sum, Matrix.mul_sum, realTrace_sum]
  apply Finset.sum_pos _ (Finset.nonempty_range_iff.mpr hp.ne')
  intro j _
  exact realTrace_twoSided_pos (posDef_natPower hQ (p - j)) (posDef_natPower hQ (j + 1)) hB

/-- Diagonal left/right multiplication weights every actual matrix entry. -/
lemma trace_diagonal_pair (a b : n → ℝ) (B : Matrix n n ℂ) :
    realTrace (Bᴴ * (Matrix.diagonal (fun i => (a i : ℂ)) * B *
      Matrix.diagonal (fun i => (b i : ℂ)))) =
      ∑ i, ∑ j, (a i * b j) * Complex.normSq (B i j) := by
  simp only [realTrace, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply, map_sum]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (conj (B i j) * ((a i : ℂ) * B i j * (b j : ℂ))).re = _
  have he : conj (B i j) * ((a i : ℂ) * B i j * (b j : ℂ)) =
      ((a i * b j : ℝ) : ℂ) * (conj (B i j) * B i j) := by push_cast; ring
  rw [he, ← Complex.normSq_eq_conj_mul_self]
  simp

def eigenCoordinates {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) (B : Matrix n n ℂ) : Matrix n n ℂ :=
  (hQ.eigenvectorUnitary : Matrix n n ℂ)ᴴ * B * (hQ.eigenvectorUnitary : Matrix n n ℂ)

lemma trace_power_pair {Q : Matrix n n ℂ} (hQ : Q.IsHermitian)
    (B : Matrix n n ℂ) (r s : ℕ) :
    realTrace (Bᴴ * (Q ^ r * B * Q ^ s)) =
      ∑ i, ∑ j, (hQ.eigenvalues i ^ r * hQ.eigenvalues j ^ s) *
        Complex.normSq (eigenCoordinates hQ B i j) := by
  let U := (hQ.eigenvectorUnitary : Matrix n n ℂ)
  have hpow (a : ℕ) : Q ^ a = U * Matrix.diagonal (fun i => ((hQ.eigenvalues i ^ a : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hQ.spectral_theorem]
    rw [unitary_conjugate_natPower, Matrix.diagonal_pow]
    simp only [U, Function.comp_def, Complex.ofReal_pow]
    rfl
  rw [hpow r, hpow s]
  have he : realTrace (Bᴴ * ((U * Matrix.diagonal (fun i => ((hQ.eigenvalues i ^ r : ℝ) : ℂ)) * Uᴴ) * B *
      (U * Matrix.diagonal (fun i => ((hQ.eigenvalues i ^ s : ℝ) : ℂ)) * Uᴴ))) =
      realTrace ((eigenCoordinates hQ B)ᴴ *
        (Matrix.diagonal (fun i => ((hQ.eigenvalues i ^ r : ℝ) : ℂ)) * eigenCoordinates hQ B *
          Matrix.diagonal (fun i => ((hQ.eigenvalues i ^ s : ℝ) : ℂ)))) := by
    calc
      _ = realTrace ((Bᴴ * U * Matrix.diagonal (fun i => ((hQ.eigenvalues i ^ r : ℝ) : ℂ)) * Uᴴ * B *
          U * Matrix.diagonal (fun i => ((hQ.eigenvalues i ^ s : ℝ) : ℂ))) * Uᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [realTrace_mul_comm]
        simp only [eigenCoordinates, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc, U]
  rw [he]
  exact trace_diagonal_pair _ _ _

/-- The actual polynomial trace form has the previously proved scalar kernel on every entry. -/
theorem polynomialInverse_quadratic_kernel {Q : Matrix n n ℂ} (hQ : Q.IsHermitian)
    (p : ℕ) (B : Matrix n n ℂ) :
    realTrace (Bᴴ * polynomialInverse p Q B) =
      ∑ i, ∑ j, ReciprocalPowerKernel.kernel p (hQ.eigenvalues i) (hQ.eigenvalues j) *
        Complex.normSq (eigenCoordinates hQ B i j) := by
  rw [polynomialInverse_sum, Matrix.mul_sum, realTrace_sum]
  simp_rw [trace_power_pair hQ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul]
  congr 1
  calc
    _ = ReciprocalPowerKernel.kernel p (hQ.eigenvalues j) (hQ.eigenvalues i) := by
      rw [ReciprocalPowerKernel.kernel_eq_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := ReciprocalPowerKernel.kernel_symm p _ _

/-- Positive eigenvalues and the scalar endpoint inequality give the operator quadratic bound. -/
theorem polynomialInverse_quadratic_le {p : ℕ} (hp : 0 < p)
    {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) (B : Matrix n n ℂ) :
    realTrace (Bᴴ * polynomialInverse p Q B) ≤ (p : ℝ) / 2 *
      realTrace (Bᴴ * (Q ^ p * B * Q + Q * B * Q ^ p)) := by
  have h1 := trace_power_pair hQ.isHermitian B p 1
  have h2 := trace_power_pair hQ.isHermitian B 1 p
  simp only [pow_one] at h1 h2
  rw [polynomialInverse_quadratic_kernel hQ.isHermitian]
  calc
    _ ≤ ∑ i, ∑ j, ((p : ℝ) / 2 *
        (hQ.isHermitian.eigenvalues i ^ p * hQ.isHermitian.eigenvalues j +
          hQ.isHermitian.eigenvalues i * hQ.isHermitian.eigenvalues j ^ p)) *
        Complex.normSq (eigenCoordinates hQ.isHermitian B i j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (ReciprocalPowerKernel.kernel_le_endpoint_products hp
          (hQ.eigenvalues_nonneg i) (hQ.eigenvalues_nonneg j)) (Complex.normSq_nonneg _)
    _ = _ := by
      rw [Matrix.mul_add, realTrace_add, h1, h2]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem polynomialInverse_hermitian_quadratic_le {p : ℕ} (hp : 0 < p)
    {Q B : Matrix n n ℂ} (hQ : Q.PosSemidef) (hB : B.IsHermitian) :
    realTrace (B * polynomialInverse p Q B) ≤ (p : ℝ) / 2 *
      realTrace (B * (Q ^ p * B * Q + Q * B * Q ^ p)) := by
  simpa only [hB.eq] using polynomialInverse_quadratic_le hp hQ B

/-- Specialization to the actual positive dyadic root gives the compressed-curvature model. -/
theorem dyadic_polynomialInverse_quadratic_le (m : ℕ) {S B : Matrix n n ℂ}
    (hS : S.PosSemidef) (hB : B.IsHermitian) :
    realTrace (B * polynomialInverse (2 ^ m) (dyadicRoot m S) B) ≤
      realTrace (B * DyadicCurvatureCompression.inverseModel m ((2 ^ m : ℕ) : ℝ) S B) / 2 := by
  have h := polynomialInverse_hermitian_quadratic_le (pow_pos (by norm_num : (0 : ℕ) < 2) m)
    (dyadicRoot_posSemidef m hS) hB
  rw [dyadicRoot_pow m hS] at h
  simpa only [DyadicCurvatureCompression.inverseModel, Matrix.mul_smul, realTrace_smul,
    div_mul_eq_mul_div] using h

/-- The same bound with coefficient p/2 inside the actual linear model. -/
theorem dyadic_polynomialInverse_le_model (m : ℕ) {S B : Matrix n n ℂ}
    (hS : S.PosSemidef) (hB : B.IsHermitian) :
    realTrace (B * polynomialInverse (2 ^ m) (dyadicRoot m S) B) ≤
      realTrace (B * DyadicCurvatureCompression.inverseModel m (((2 ^ m : ℕ) : ℝ) / 2) S B) := by
  have h := dyadic_polynomialInverse_quadratic_le m hS hB
  simpa only [DyadicCurvatureCompression.inverseModel, Matrix.mul_smul, realTrace_smul,
    div_mul_eq_mul_div] using h

/-- Every summand is self-adjoint for the complex Hilbert--Schmidt pairing. -/
theorem polynomialInverse_adjoint_trace_symmetric (p : ℕ)
    {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) (X Y : Matrix n n ℂ) :
    realTrace (Xᴴ * polynomialInverse p Q Y) =
      realTrace ((polynomialInverse p Q X)ᴴ * Y) := by
  simp only [polynomialInverse_sum, Matrix.mul_sum, Matrix.conjTranspose_sum,
    Matrix.sum_mul, realTrace_sum, Matrix.conjTranspose_mul,
    (hQ.pow _).eq]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = realTrace ((Xᴴ * Q ^ (p - j) * Y) * Q ^ (j + 1)) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [realTrace_mul_comm]; simp only [Matrix.mul_assoc]

/-- Reflection of the power index proves preservation of Hermitian matrices. -/
theorem polynomialInverse_isHermitian (p : ℕ) {Q B : Matrix n n ℂ}
    (hQ : Q.IsHermitian) (hB : B.IsHermitian) :
    (polynomialInverse p Q B).IsHermitian := by
  change (polynomialInverse p Q B)ᴴ = polynomialInverse p Q B
  simp only [polynomialInverse_sum, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    (hQ.pow _).eq, hB.eq]
  rw [← Finset.sum_range_reflect (fun j => Q ^ (p - j) * B * Q ^ (j + 1)) p]
  apply Finset.sum_congr rfl
  intro j hj
  have hjp := Finset.mem_range.mp hj
  have h1 : p - (p - 1 - j) = j + 1 := by omega
  have h2 : p - 1 - j + 1 = p - j := by omega
  rw [h1, h2]
  simp only [Matrix.mul_assoc]

/-- On Hermitian matrices the Hilbert--Schmidt symmetry is ordinary trace symmetry. -/
theorem polynomialInverse_trace_symmetric (p : ℕ) {Q X : Matrix n n ℂ}
    (hQ : Q.IsHermitian) (hX : X.IsHermitian) (Y : Matrix n n ℂ) :
    realTrace (X * polynomialInverse p Q Y) =
      realTrace (polynomialInverse p Q X * Y) := by
  simpa only [hX.eq, (polynomialInverse_isHermitian p hQ hX).eq] using
    polynomialInverse_adjoint_trace_symmetric p hQ X Y

theorem polynomialInverse_hermitian_quadratic_pos {p : ℕ} (hp : 0 < p)
    {Q B : Matrix n n ℂ} (hQ : Q.PosDef) (hB : B.IsHermitian) (hB0 : B ≠ 0) :
    0 < realTrace (B * polynomialInverse p Q B) := by
  simpa only [hB.eq] using polynomialInverse_quadratic_pos hp hQ hB0

theorem dyadic_polynomialInverse_quadratic_pos (m : ℕ) {S B : Matrix n n ℂ}
    (hS : S.PosDef) (hB : B.IsHermitian) (hB0 : B ≠ 0) :
    0 < realTrace (B * polynomialInverse (2 ^ m) (dyadicRoot m S) B) :=
  polynomialInverse_hermitian_quadratic_pos (pow_pos (by norm_num : (0 : ℕ) < 2) m)
    (dyadicRoot_posDef m hS) hB hB0

end DyadicInverseKernelBound
end MatrixSpencer
