import MatrixSpencer.TraceGeometry
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

/-!
# Four-index realignment in the observed Kraus tensor argument

The definitions distinguish the channel matrix from its Choi matrix.
The energy is the sum of squared moduli of all entries, so no implicit
operator norm or matrix norm instance enters the realignment identity.
-/

open scoped BigOperators ComplexConjugate MatrixOrder ComplexOrder Matrix

noncomputable section

namespace MatrixSpencer

variable {ι m n : Type*} [Fintype ι] [Fintype m] [Fintype n]

/-- Squared Frobenius energy, written entrywise to make its metric explicit. -/
def entryEnergy (A : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

theorem entryEnergy_nonneg (A : Matrix m n ℂ) : 0 ≤ entryEnergy A := by
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

open scoped Matrix.Norms.Frobenius in
/-- The entrywise energy is the squared Frobenius norm, explicitly scoped. -/
theorem entryEnergy_eq_frobeniusNorm_sq (A : Matrix m n ℂ) :
    entryEnergy A = ‖A‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two, ← Complex.normSq_eq_norm_sq,
    ← Real.sqrt_eq_rpow]
  exact (Real.sq_sqrt (entryEnergy_nonneg A)).symm

/-- The Choi Gram matrix of a rectangular Kraus family. -/
def krausChoi (K : ι → Matrix m n ℂ) : Matrix (m × n) (m × n) ℂ :=
  fun ij kl => ∑ a, K a ij.1 ij.2 * conj (K a kl.1 kl.2)

/-- The channel as a matrix on pairs of input and output indices. -/
def krausSuper (K : ι → Matrix m n ℂ) : Matrix (m × m) (n × n) ℂ :=
  fun ik jl => ∑ a, K a ik.1 jl.1 * conj (K a ik.2 jl.2)

/-- Realignment is an exact permutation of four indices, including complex entries. -/
theorem krausSuper_entryEnergy_eq_choi (K : ι → Matrix m n ℂ) :
    entryEnergy (krausSuper K) = entryEnergy (krausChoi K) := by
  simp only [entryEnergy, krausSuper, krausChoi, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

omit [Fintype m] [Fintype n] in
/-- The explicit Choi matrix is Hermitian; no real-coefficient restriction is needed. -/
theorem krausChoi_conjTranspose (K : ι → Matrix m n ℂ) :
    (krausChoi K).conjTranspose = krausChoi K := by
  ext ij kl
  simp [krausChoi, Matrix.conjTranspose_apply, mul_comm]

/-- Columns are vectorized Kraus matrices, without any transpose convention hidden. -/
def krausSynthesis (K : ι → Matrix m n ℂ) : Matrix (m × n) ι ℂ :=
  fun ij a => K a ij.1 ij.2

omit [Fintype m] [Fintype n] in
theorem krausChoi_eq_synthesis_mul_adjoint (K : ι → Matrix m n ℂ) :
    krausChoi K = krausSynthesis K * (krausSynthesis K).conjTranspose := by
  ext ij kl
  simp [krausChoi, krausSynthesis, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Positivity follows from the actual complex Gram factorization. -/
theorem krausChoi_posSemidef (K : ι → Matrix m n ℂ) :
    (krausChoi K).PosSemidef := by
  rw [krausChoi_eq_synthesis_mul_adjoint]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- Entry energy agrees with the unnormalized Hilbert--Schmidt trace. -/
theorem entryEnergy_eq_realTrace_adjoint_mul (A : Matrix m n ℂ) :
    entryEnergy A = realTrace (A.conjTranspose * A) := by
  simp only [entryEnergy, realTrace, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change Complex.normSq (A j i) = (conj (A j i) * A j i).re
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

/-- The Choi trace is the sum of Kraus energies. -/
theorem realTrace_krausChoi (K : ι → Matrix m n ℂ) :
    realTrace (krausChoi K) = ∑ a, entryEnergy (K a) := by
  simp only [realTrace, Matrix.trace, Matrix.diag, krausChoi, map_sum,
    Complex.mul_conj, RCLike.re_eq_complex_re, Complex.ofReal_re, entryEnergy,
    Fintype.sum_prod_type]
  calc
    _ = ∑ i, ∑ a, ∑ j, Complex.normSq (K a i j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- A positive Choi cap controls the full channel's squared HS norm via realignment. -/
theorem krausSuper_entryEnergy_le [DecidableEq m] [DecidableEq n]
    (K : ι → Matrix m n ℂ) {κ : ℝ}
    (hcap : krausChoi K ≤ κ • (1 : Matrix (m × n) (m × n) ℂ)) :
    entryEnergy (krausSuper K) ≤ κ * ∑ a, entryEnergy (K a) := by
  rw [krausSuper_entryEnergy_eq_choi, entryEnergy_eq_realTrace_adjoint_mul,
    krausChoi_conjTranspose]
  have h := realTrace_mul_mono (krausChoi_posSemidef K) hcap
  simpa only [mul_smul_comm, Matrix.mul_one, realTrace_smul,
    realTrace_krausChoi] using h

/-- The completely positive channel with the same rectangular Kraus operators. -/
def krausChannel (K : ι → Matrix m n ℂ) (X : Matrix n n ℂ) : Matrix m m ℂ :=
  ∑ a, K a * X * (K a).conjTranspose

omit [Fintype m] in
/-- The four-index superoperator really acts as the asserted Kraus channel. -/
theorem krausSuper_mulVec (K : ι → Matrix m n ℂ) (X : Matrix n n ℂ) (i k : m) :
    (krausSuper K *ᵥ (fun jl => X jl.1 jl.2)) (i, k) = krausChannel K X i k := by
  simp only [Matrix.mulVec, dotProduct, krausSuper, krausChannel, Matrix.mul_apply,
    Matrix.sum_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j, ∑ a, ∑ l, K a i l * conj (K a k j) * X l j := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ l, K a i l * conj (K a k j) * X l j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      change K a i l * conj (K a k j) * X l j =
        K a i l * X l j * conj (K a k j)
      ring

end MatrixSpencer
