import MatrixSpencer.KSFullHermitianChart

/-!
# Explicit physical directions for numerical Hermitian gradients

The directions use only matrix units and the fixed scalar `I`. Central
differences in these directions recover the real and imaginary entries of
the Frobenius gradient. No chosen orthonormal basis is an algorithm input.
-/

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace MatrixSpencer.KSHermitianDirections

variable {n : Type*} [Fintype n] [DecidableEq n]

def realDirection (i j : n) : Matrix n n ℂ :=
  (1 / 2 : ℝ) • (Matrix.single i j 1 + Matrix.single j i 1)

def imagDirection (i j : n) : Matrix n n ℂ :=
  (1 / 2 : ℝ) • (Matrix.single i j Complex.I - Matrix.single j i Complex.I)

theorem realDirection_isHermitian (i j : n) : (realDirection i j).IsHermitian := by
  unfold realDirection Matrix.IsHermitian
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add,
    Matrix.conjTranspose_single, star_one]
  rw [add_comm]

theorem imagDirection_isHermitian (i j : n) : (imagDirection i j).IsHermitian := by
  have hsingle (k l : n) : (Matrix.single k l (-Complex.I) : Matrix n n ℂ) =
      -(Matrix.single k l Complex.I) := by
    ext r s
    simp [Matrix.single, apply_ite]
  unfold imagDirection Matrix.IsHermitian
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_single, Complex.star_def, Complex.conj_I, hsingle]
  congr 1
  abel

theorem realDirection_swap (i j : n) : realDirection j i = realDirection i j := by
  unfold realDirection
  rw [add_comm]

theorem imagDirection_swap (i j : n) : imagDirection j i = -imagDirection i j := by
  unfold imagDirection
  rw [← smul_neg, neg_sub]

/-- A real physical direction extracts exactly one real gradient entry. -/
theorem trace_realDirection (G : Matrix n n ℂ) (hG : G.IsHermitian) (i j : n) :
    realTrace (G * realDirection i j) = (G i j).re := by
  have hji : G j i = star (G i j) := (hG.apply j i).symm
  simp only [realDirection, Matrix.mul_smul, Matrix.mul_add, realTrace_smul, realTrace_add]
  simp [realTrace, Matrix.trace_mul_single, hji, Complex.mul_re]
  <;> ring

/-- The skew imaginary direction extracts the imaginary gradient entry. -/
theorem trace_imagDirection (G : Matrix n n ℂ) (hG : G.IsHermitian) (i j : n) :
    realTrace (G * imagDirection i j) = (G i j).im := by
  have hji : G j i = star (G i j) := (hG.apply j i).symm
  simp only [imagDirection, Matrix.mul_smul, Matrix.mul_sub, realTrace_smul, realTrace_sub]
  simp [realTrace, Matrix.trace_mul_single, hji, Complex.mul_re]
  <;> ring

theorem realDirection_trace_square_le (i j : n) :
    realTrace (realDirection i j * realDirection i j) ≤ 1 := by
  rw [trace_realDirection _ (realDirection_isHermitian i j)]
  by_cases hij : i = j
  · subst j
    norm_num [realDirection, Matrix.single]
  · norm_num [realDirection, Matrix.single, hij, Ne.symm hij]

theorem imagDirection_trace_square_le (i j : n) :
    realTrace (imagDirection i j * imagDirection i j) ≤ 1 := by
  rw [trace_imagDirection _ (imagDirection_isHermitian i j)]
  by_cases hij : i = j
  · subst j
    norm_num [imagDirection, Matrix.single]
  · norm_num [imagDirection, Matrix.single, hij, Ne.symm hij]

end MatrixSpencer.KSHermitianDirections
