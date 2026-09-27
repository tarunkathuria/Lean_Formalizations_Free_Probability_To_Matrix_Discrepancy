import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-!
# Positive square-root compression

The proof first compares squares under a contractive compression, then applies
operator monotonicity of the positive square root. No differentiability or
commutation assumption is used.
-/

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MatrixSpencer

variable {m n : Type*}
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Positive square roots satisfy the compression inequality for any matrix
whose product with its adjoint is at most the identity. -/
theorem sqrt_compression_le {S : Matrix n n ℂ} (hS : S.PosSemidef)
    (V : Matrix n m ℂ) (hV : V * Vᴴ ≤ 1) :
    Vᴴ * CFC.sqrt S * V ≤ CFC.sqrt (Vᴴ * S * V) := by
  letI : CStarAlgebra (Matrix m m ℂ) := {}
  have hroot : (CFC.sqrt S).IsHermitian :=
    (CFC.sqrt_nonneg S).posSemidef.isHermitian
  have hcomp : (Vᴴ * CFC.sqrt S * V).PosSemidef :=
    (CFC.sqrt_nonneg S).posSemidef.conjTranspose_mul_mul_same V
  have hdiff : (1 - V * Vᴴ).PosSemidef := Matrix.le_iff.mp hV
  have hmul : CFC.sqrt S * (CFC.sqrt S * V) = S * V := by
    rw [← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self S hS.nonneg]
  have hsq : (Vᴴ * CFC.sqrt S * V) ^ 2 ≤ Vᴴ * S * V := by
    apply Matrix.le_iff.mpr
    have h := hdiff.conjTranspose_mul_mul_same (CFC.sqrt S * V)
    simpa only [Matrix.conjTranspose_mul, hroot.eq, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.mul_assoc, hmul,
      pow_two] using h
  have h := CFC.sqrt_le_sqrt ((Vᴴ * CFC.sqrt S * V) ^ 2) (Vᴴ * S * V) hsq
  simpa only [CFC.sqrt_sq _ hcomp.nonneg] using h

/-- A Hermitian idempotent is at most the identity in Loewner order. -/
theorem isHermitian_idempotent_le_one {P : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) : P ≤ 1 := by
  apply Matrix.le_iff.mpr
  have h := Matrix.posSemidef_conjTranspose_mul_self (1 - P)
  simpa only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.eq,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    hPP, sub_self, sub_zero] using h

/-- The square-root compression inequality for a rectangular isometry. -/
theorem sqrt_isometry_compression_le {S : Matrix n n ℂ} (hS : S.PosSemidef)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) :
    Vᴴ * CFC.sqrt S * V ≤ CFC.sqrt (Vᴴ * S * V) := by
  have hVV : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
    calc
      (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by
        simp only [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  exact sqrt_compression_le hS V
    (isHermitian_idempotent_le_one
      (Matrix.posSemidef_self_mul_conjTranspose V).isHermitian hVV)

/-- Square orthogonal projections give an unconditional compression corollary. -/
theorem sqrt_projection_compression_le {S P : Matrix n n ℂ}
    (hS : S.PosSemidef) (hP : P.IsHermitian) (hPP : P * P = P) :
    P * CFC.sqrt S * P ≤ CFC.sqrt (P * S * P) := by
  have hV : P * Pᴴ ≤ 1 := by
    simpa only [hP.eq, hPP] using isHermitian_idempotent_le_one hP hPP
  simpa only [hP.eq] using sqrt_compression_le hS P hV

end MatrixSpencer
