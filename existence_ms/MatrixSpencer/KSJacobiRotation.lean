import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# An explicit real symmetric two-coordinate Jacobi rotation

The rotation is defined using comparisons, arithmetic, and real square roots.
The `b = 0` branch is the identity. In the other branch a concrete normalized
quadratic-root vector is used; no spectral theorem or arbitrary eigenvector
selection is involved. The proof establishes exact real-arithmetic identities,
not finite-precision stability, a pivot-selection routine, or convergence of
a sequence of rotations in larger dimension.
-/

open Matrix
open scoped BigOperators

noncomputable section
namespace MatrixSpencer.KSJacobiRotation

def shift (a b d : ℝ) : ℝ :=
  (d - a + Real.sqrt ((d - a) ^ 2 + 4 * b ^ 2)) / 2

def radius (a b d : ℝ) : ℝ := Real.sqrt (b ^ 2 + shift a b d ^ 2)

def cosine (a b d : ℝ) : ℝ := if b = 0 then 1 else b / radius a b d

def sine (a b d : ℝ) : ℝ := if b = 0 then 0 else -shift a b d / radius a b d

def rotationMatrix (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c, s; -s, c]

def rotation (a b d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  rotationMatrix (cosine a b d) (sine a b d)

def symmetricBlock (a b d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, d]

theorem shift_equation (a b d : ℝ) :
    shift a b d ^ 2 - (d - a) * shift a b d - b ^ 2 = 0 := by
  have hroot := Real.sq_sqrt (show 0 ≤ (d - a) ^ 2 + 4 * b ^ 2 by positivity)
  dsimp [shift]
  nlinarith

theorem radius_pos (a b d : ℝ) (hb : b ≠ 0) : 0 < radius a b d := by
  apply Real.sqrt_pos.2
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  positivity

theorem radius_sq (a b d : ℝ) : radius a b d ^ 2 = b ^ 2 + shift a b d ^ 2 := by
  exact Real.sq_sqrt (by positivity)

/-- The defined coefficients form a unit vector, also in the zero-pivot case. -/
theorem coefficients_unit (a b d : ℝ) : cosine a b d ^ 2 + sine a b d ^ 2 = 1 := by
  by_cases hb : b = 0
  · simp [cosine, sine, hb]
  · simp only [cosine, sine, if_neg hb, div_pow, neg_sq]
    rw [← add_div, ← radius_sq, div_self]
    exact pow_ne_zero _ (radius_pos a b d hb).ne'

/-- The explicit coefficient formula annihilates the off-diagonal entry. -/
theorem coefficients_annihilate (a b d : ℝ) :
    (a - d) * cosine a b d * sine a b d +
      b * (cosine a b d ^ 2 - sine a b d ^ 2) = 0 := by
  by_cases hb : b = 0
  · simp [cosine, sine, hb]
  · have hr := (radius_pos a b d hb).ne'
    simp only [cosine, sine, if_neg hb]
    field_simp
    linear_combination -b * shift_equation a b d

theorem rotation_zero_pivot (a d : ℝ) : rotation a 0 d = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation, rotationMatrix, cosine, sine]

/-- The actual rotation has orthonormal columns. -/
theorem rotation_transpose_mul (a b d : ℝ) : (rotation a b d)ᵀ * rotation a b d = 1 := by
  have hunit := coefficients_unit a b d
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith

/-- The actual rotation also has orthonormal rows. -/
theorem rotation_mul_transpose (a b d : ℝ) : rotation a b d * (rotation a b d)ᵀ = 1 := by
  have hunit := coefficients_unit a b d
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith

theorem conjugation_formula (a b d c s : ℝ) :
    (rotationMatrix c s)ᵀ * symmetricBlock a b d * rotationMatrix c s =
      !![a * c ^ 2 - 2 * b * c * s + d * s ^ 2,
          (a - d) * c * s + b * (c ^ 2 - s ^ 2);
        (a - d) * c * s + b * (c ^ 2 - s ^ 2),
          a * s ^ 2 + 2 * b * c * s + d * c ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, symmetricBlock, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Exact diagonalization by the explicitly defined real-arithmetic rotation. -/
theorem diagonalization (a b d : ℝ) :
    (rotation a b d)ᵀ * symmetricBlock a b d * rotation a b d =
      !![a * cosine a b d ^ 2 - 2 * b * cosine a b d * sine a b d +
          d * sine a b d ^ 2, 0;
        0, a * sine a b d ^ 2 + 2 * b * cosine a b d * sine a b d +
          d * cosine a b d ^ 2] := by
  rw [rotation, conjugation_formula, coefficients_annihilate]

theorem rotated_offDiagonal_zero (a b d : ℝ) :
    ((rotation a b d)ᵀ * symmetricBlock a b d * rotation a b d) 0 1 = 0 ∧
      ((rotation a b d)ᵀ * symmetricBlock a b d * rotation a b d) 1 0 = 0 := by
  rw [diagonalization]
  simp

/-- The squared Frobenius norm of the off-diagonal entries in dimension two. -/
def offDiagonalEnergy (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := A 0 1 ^ 2 + A 1 0 ^ 2

theorem offDiagonalEnergy_drop (a b d : ℝ) :
    offDiagonalEnergy (symmetricBlock a b d) -
      offDiagonalEnergy ((rotation a b d)ᵀ * symmetricBlock a b d * rotation a b d) =
      2 * b ^ 2 := by
  rcases rotated_offDiagonal_zero a b d with ⟨h01, h10⟩
  simp only [offDiagonalEnergy, h01, h10, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, add_zero, sub_zero]
  simp [symmetricBlock]
  ring

/-- This scalar identity supplies the unchanged energy of every pair of
off-pivot entries when a rotation is embedded in a larger matrix. -/
theorem rotated_pair_energy (a b d u v : ℝ) :
    (cosine a b d * u - sine a b d * v) ^ 2 +
      (sine a b d * u + cosine a b d * v) ^ 2 = u ^ 2 + v ^ 2 := by
  calc
    _ = (cosine a b d ^ 2 + sine a b d ^ 2) * (u ^ 2 + v ^ 2) := by ring
    _ = _ := by rw [coefficients_unit, one_mul]

end MatrixSpencer.KSJacobiRotation
