import MatrixSpencer.KSJacobiRotation
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# An explicit Jacobi step at two labels of a finite real matrix

The embedded rotation acts as the identity outside the two chosen coordinates.
The update is its actual matrix conjugation. All identities are finite sums
and scalar arithmetic; no spectral decomposition is chosen.
-/

open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSJacobiStep

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def embedding (i j : ι) (c s : ℝ) : Matrix ι ι ℝ := fun k l =>
  if l = i then (if k = i then c else 0) + (if k = j then -s else 0)
  else if l = j then (if k = i then s else 0) + (if k = j then c else 0)
  else if k = l then 1 else 0

theorem mul_embedding (K : Matrix ι ι ℝ) (i j : ι) (c s : ℝ) (k l : ι) :
    (K * embedding i j c s) k l =
      if l = i then c * K k i - s * K k j
      else if l = j then s * K k i + c * K k j else K k l := by
  by_cases hi : l = i
  · subst l
    simp [embedding, Matrix.mul_apply, mul_add, mul_ite, Finset.sum_add_distrib]
    ring
  · by_cases hj : l = j
    · subst l
      simp [embedding, Matrix.mul_apply, hi, mul_add, mul_ite, Finset.sum_add_distrib]
      ring
    · simp [embedding, Matrix.mul_apply, hi, hj, mul_ite]

theorem embedding_transpose_mul (K : Matrix ι ι ℝ) (i j : ι) (c s : ℝ) (k l : ι) :
    ((embedding i j c s)ᵀ * K) k l =
      if k = i then c * K i l - s * K j l
      else if k = j then s * K i l + c * K j l else K k l := by
  have h := mul_embedding Kᵀ i j c s l k
  calc
    _ = ((Kᵀ * embedding i j c s)ᵀ) k l := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = _ := by simpa only [Matrix.transpose_apply] using h

theorem embedding_transpose_mul_self (i j : ι) (hij : i ≠ j) (c s : ℝ)
    (hunit : c ^ 2 + s ^ 2 = 1) :
    (embedding i j c s)ᵀ * embedding i j c s = 1 := by
  ext k l
  rw [mul_embedding]
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
    simp_all [embedding, Matrix.transpose_apply, Matrix.one_apply, eq_comm] <;> nlinarith

theorem embedding_mul_transpose_self (i j : ι) (hij : i ≠ j) (c s : ℝ)
    (hunit : c ^ 2 + s ^ 2 = 1) :
    embedding i j c s * (embedding i j c s)ᵀ = 1 := by
  exact Matrix.mul_eq_one_comm.mp (embedding_transpose_mul_self i j hij c s hunit)

def rotation (K : Matrix ι ι ℝ) (i j : ι) : Matrix ι ι ℝ :=
  embedding i j (KSJacobiRotation.cosine (K i i) (K i j) (K j j))
    (KSJacobiRotation.sine (K i i) (K i j) (K j j))

def step (K : Matrix ι ι ℝ) (i j : ι) : Matrix ι ι ℝ :=
  (rotation K i j)ᵀ * K * rotation K i j

theorem rotation_transpose_mul_self (K : Matrix ι ι ℝ) (i j : ι) (hij : i ≠ j) :
    (rotation K i j)ᵀ * rotation K i j = 1 :=
  embedding_transpose_mul_self i j hij _ _ (KSJacobiRotation.coefficients_unit _ _ _)

theorem rotation_mul_transpose_self (K : Matrix ι ι ℝ) (i j : ι) (hij : i ≠ j) :
    rotation K i j * (rotation K i j)ᵀ = 1 :=
  embedding_mul_transpose_self i j hij _ _ (KSJacobiRotation.coefficients_unit _ _ _)

theorem step_symmetric (K : Matrix ι ι ℝ) (hK : K.IsSymm) (i j : ι) :
    (step K i j).IsSymm := by
  change (step K i j)ᵀ = step K i j
  simp only [step, Matrix.transpose_mul, Matrix.transpose_transpose, hK.eq,
    Matrix.mul_assoc]

def frobeniusEnergy (K : Matrix ι ι ℝ) : ℝ := ∑ k, ∑ l, K k l ^ 2

def diagonalEnergy (K : Matrix ι ι ℝ) : ℝ := ∑ k, K k k ^ 2

def offDiagonalEnergy (K : Matrix ι ι ℝ) : ℝ :=
  ∑ k, ∑ l, if k = l then 0 else K k l ^ 2

omit [DecidableEq ι] in
theorem frobeniusEnergy_eq_trace (K : Matrix ι ι ℝ) :
    frobeniusEnergy K = Matrix.trace (Kᵀ * K) := by
  simp only [frobeniusEnergy, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, ← pow_two]
  exact Finset.sum_comm

/-- Orthogonal conjugation preserves the actual full sum of squared entries. -/
theorem frobeniusEnergy_conjugation (K R : Matrix ι ι ℝ)
    (hR : R * Rᵀ = 1) : frobeniusEnergy (Rᵀ * K * R) = frobeniusEnergy K := by
  rw [frobeniusEnergy_eq_trace, frobeniusEnergy_eq_trace]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = Matrix.trace (Rᵀ * (Kᵀ * (R * Rᵀ) * K) * R) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Rᵀ * (Kᵀ * K) * R) := by rw [hR, Matrix.mul_one]
    _ = _ := by rw [Matrix.trace_mul_cycle, hR, Matrix.one_mul]

theorem step_frobeniusEnergy (K : Matrix ι ι ℝ) (i j : ι) (hij : i ≠ j) :
    frobeniusEnergy (step K i j) = frobeniusEnergy K :=
  frobeniusEnergy_conjugation K (rotation K i j) (rotation_mul_transpose_self K i j hij)

/-- Every entry outside the two pivot rows and columns is unchanged. -/
theorem step_apply_away (K : Matrix ι ι ℝ) (i j k l : ι)
    (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j) :
    step K i j k l = K k l := by
  unfold step rotation
  rw [mul_embedding]
  simp only [if_neg hli, if_neg hlj]
  rw [embedding_transpose_mul]
  simp only [if_neg hki, if_neg hkj]

theorem step_other_diagonal (K : Matrix ι ι ℝ) (i j k : ι)
    (hki : k ≠ i) (hkj : k ≠ j) : step K i j k k = K k k :=
  step_apply_away K i j k k hki hkj hki hkj

theorem step_pivot_ii (K : Matrix ι ι ℝ) (hK : K.IsSymm) (i j : ι) :
    step K i j i i =
      K i i * KSJacobiRotation.cosine (K i i) (K i j) (K j j) ^ 2 -
      2 * K i j * KSJacobiRotation.cosine (K i i) (K i j) (K j j) *
        KSJacobiRotation.sine (K i i) (K i j) (K j j) +
      K j j * KSJacobiRotation.sine (K i i) (K i j) (K j j) ^ 2 := by
  unfold step rotation
  rw [mul_embedding]
  simp only [if_true]
  rw [embedding_transpose_mul, embedding_transpose_mul]
  simp only [if_true, hK.apply i j]
  ring

theorem step_pivot_jj (K : Matrix ι ι ℝ) (hK : K.IsSymm) (i j : ι) (hij : i ≠ j) :
    step K i j j j =
      K i i * KSJacobiRotation.sine (K i i) (K i j) (K j j) ^ 2 +
      2 * K i j * KSJacobiRotation.cosine (K i i) (K i j) (K j j) *
        KSJacobiRotation.sine (K i i) (K i j) (K j j) +
      K j j * KSJacobiRotation.cosine (K i i) (K i j) (K j j) ^ 2 := by
  unfold step rotation
  rw [mul_embedding]
  simp only [if_neg hij.symm, if_true]
  rw [embedding_transpose_mul, embedding_transpose_mul]
  simp only [if_neg hij.symm, if_true, hK.apply i j]
  ring

/-- Both target off-diagonal entries become exactly zero. -/
theorem step_pivot_zero (K : Matrix ι ι ℝ) (hK : K.IsSymm) (i j : ι) (hij : i ≠ j) :
    step K i j i j = 0 ∧ step K i j j i = 0 := by
  have hz : step K i j i j = 0 := by
    unfold step rotation
    rw [mul_embedding]
    simp only [if_neg hij.symm, if_true]
    rw [embedding_transpose_mul, embedding_transpose_mul]
    simp only [if_true, hK.apply i j]
    convert KSJacobiRotation.coefficients_annihilate (K i i) (K i j) (K j j) using 1
    ring
  exact ⟨hz, ((step_symmetric K hK i j).apply i j).trans hz⟩

theorem frobeniusEnergy_split (K : Matrix ι ι ℝ) :
    frobeniusEnergy K = diagonalEnergy K + offDiagonalEnergy K := by
  simp only [frobeniusEnergy, diagonalEnergy, offDiagonalEnergy, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hdiag : K k k ^ 2 = ∑ l, if k = l then K k l ^ 2 else 0 := by simp
  rw [hdiag, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hkl : k = l <;> simp [hkl]

theorem pivot_diagonal_energy_gain (K : Matrix ι ι ℝ) (hK : K.IsSymm)
    (i j : ι) (hij : i ≠ j) :
    step K i j i i ^ 2 + step K i j j j ^ 2 =
      K i i ^ 2 + K j j ^ 2 + 2 * K i j ^ 2 := by
  have he := frobeniusEnergy_conjugation
    (KSJacobiRotation.symmetricBlock (K i i) (K i j) (K j j))
    (KSJacobiRotation.rotation (K i i) (K i j) (K j j))
    (KSJacobiRotation.rotation_mul_transpose _ _ _)
  rw [KSJacobiRotation.diagonalization] at he
  simp [frobeniusEnergy, KSJacobiRotation.symmetricBlock, Fin.sum_univ_two] at he
  rw [step_pivot_ii K hK i j, step_pivot_jj K hK i j hij]
  nlinarith [he]

theorem step_diagonalEnergy (K : Matrix ι ι ℝ) (hK : K.IsSymm)
    (i j : ι) (hij : i ≠ j) :
    diagonalEnergy (step K i j) = diagonalEnergy K + 2 * K i j ^ 2 := by
  have hterm (k : ι) : step K i j k k ^ 2 - K k k ^ 2 =
      (if k = i then step K i j i i ^ 2 - K i i ^ 2 else 0) +
      (if k = j then step K i j j j ^ 2 - K j j ^ 2 else 0) := by
    by_cases hki : k = i
    · subst k
      simp [hij]
    · by_cases hkj : k = j
      · subst k
        simp [hij.symm]
      · simp [hki, hkj, step_other_diagonal K i j k hki hkj]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun k _ => hterm k)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hs
  have hp := pivot_diagonal_energy_gain K hK i j hij
  unfold diagonalEnergy
  linarith

/-- The full off-diagonal squared Frobenius energy decreases by exactly twice
the square of the chosen symmetric pivot. -/
theorem step_offDiagonalEnergy (K : Matrix ι ι ℝ) (hK : K.IsSymm)
    (i j : ι) (hij : i ≠ j) :
    offDiagonalEnergy (step K i j) = offDiagonalEnergy K - 2 * K i j ^ 2 := by
  have hfull := step_frobeniusEnergy K i j hij
  rw [frobeniusEnergy_split, frobeniusEnergy_split, step_diagonalEnergy K hK i j hij] at hfull
  linarith

theorem offDiagonalEnergy_nonneg (K : Matrix ι ι ℝ) : 0 ≤ offDiagonalEnergy K := by
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro l _
  split_ifs <;> positivity

theorem step_offDiagonalEnergy_le (K : Matrix ι ι ℝ) (hK : K.IsSymm)
    (i j : ι) (hij : i ≠ j) :
    offDiagonalEnergy (step K i j) ≤ offDiagonalEnergy K := by
  rw [step_offDiagonalEnergy K hK i j hij]
  nlinarith [sq_nonneg (K i j)]

end MatrixSpencer.KSJacobiStep
