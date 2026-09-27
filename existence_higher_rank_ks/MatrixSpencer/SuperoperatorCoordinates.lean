import MatrixSpencer.Sylvester
import MatrixSpencer.Realignment
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Explicit Hilbert--Schmidt coordinates

Vectorization uses the ordered pair of physical indices. Its trace-pairing
identity fixes the adjoint and transpose conventions for superoperators.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section

namespace MatrixSpencer

variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixVector (X : Matrix n n ℂ) : n × n → ℂ := fun ij => X ij.1 ij.2

def matrixUnvector (x : n × n → ℂ) : Matrix n n ℂ := fun i j => x (i, j)

omit [Fintype n] [DecidableEq n] in
@[simp] theorem matrixUnvector_vector (X : Matrix n n ℂ) : matrixUnvector (matrixVector X) = X := rfl
omit [Fintype n] [DecidableEq n] in
@[simp] theorem matrixVector_unvector (x : n × n → ℂ) : matrixVector (matrixUnvector x) = x := rfl

def matrixVectorEquiv : Matrix n n ℂ ≃ₗ[ℂ] (n × n → ℂ) where
  toFun := matrixVector
  invFun := matrixUnvector
  left_inv := matrixUnvector_vector
  right_inv := matrixVector_unvector
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq n] in
/-- The trace pairing is the ordinary complex Euclidean pairing after vectorization. -/
theorem matrixVector_dotProduct (X Y : Matrix n n ℂ) :
    star (matrixVector X) ⬝ᵥ matrixVector Y = Matrix.trace (Xᴴ * Y) := by
  simp only [dotProduct, matrixVector, Pi.star_apply, Fintype.sum_prod_type,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_comm

omit [DecidableEq n] in
/-- Squared Euclidean coordinate length equals the previously used explicit Frobenius energy. -/
theorem matrixVector_energy (X : Matrix n n ℂ) :
    (∑ ij, Complex.normSq (matrixVector X ij)) = entryEnergy X := by
  simp only [matrixVector, entryEnergy, Fintype.sum_prod_type]

/-- A concrete coordinate matrix for any complex-linear operator on physical matrices. -/
def matrixSuper (L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  LinearMap.toMatrix' (matrixVectorEquiv.toLinearMap.comp (L.comp matrixVectorEquiv.symm.toLinearMap))

@[simp] theorem matrixSuper_mulVec (L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (x : n × n → ℂ) :
    matrixSuper L *ᵥ x = matrixVector (L (matrixUnvector x)) := by
  exact LinearMap.toMatrix'_mulVec _ x

theorem matrixSuper_quadratic (L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (x : n × n → ℂ) :
    star x ⬝ᵥ (matrixSuper L *ᵥ x) =
      Matrix.trace ((matrixUnvector x)ᴴ * L (matrixUnvector x)) := by
  rw [matrixSuper_mulVec]
  exact matrixVector_dotProduct (matrixUnvector x) _

/-- The Jordan operator is represented in the same fixed coordinates as the Kraus channel. -/
def jordanSuper (P : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ := matrixSuper (sylvester P)

@[simp] theorem jordanSuper_mulVec (P : Matrix n n ℂ) (x : n × n → ℂ) :
    jordanSuper P *ᵥ x = matrixVector (P * matrixUnvector x + matrixUnvector x * P) :=
  matrixSuper_mulVec (sylvester P) x

/-- The explicit two-index formula keeps the transpose on the right-multiplication factor. -/
theorem jordanSuper_entry (P : Matrix n n ℂ) (ij kl : n × n) :
    jordanSuper P ij kl = (if ij.2 = kl.2 then P ij.1 kl.1 else 0) +
      (if ij.1 = kl.1 then P kl.2 ij.2 else 0) := by
  classical
  rcases ij with ⟨i, j⟩
  rcases kl with ⟨k, l⟩
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [jordanSuper, matrixSuper, LinearMap.toMatrix'_apply, matrixVectorEquiv,
      matrixVector, matrixUnvector, sylvester_apply, Matrix.mul_apply,
      Prod.mk.injEq, and_comm, eq_comm, hik, hjl]

theorem jordanSuper_isHermitian {P : Matrix n n ℂ} (hP : P.IsHermitian) :
    (jordanSuper P).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro ij kl
  by_cases h₁ : ij.1 = kl.1 <;> by_cases h₂ : ij.2 = kl.2 <;>
    simp [jordanSuper_entry, h₁, h₂, eq_comm, hP.apply ij.1 kl.1, hP.apply kl.2 ij.2]
  simp only [← Complex.star_def, hP.apply kl.1 kl.1, hP.apply kl.2 kl.2]

/-- The actual Jordan coordinate matrix is strictly positive on every nonzero complex vector. -/
theorem jordanSuper_posDef {P : Matrix n n ℂ} (hP : P.PosDef) :
    (jordanSuper P).PosDef := by
  have hh := jordanSuper_isHermitian hP.isHermitian
  refine ⟨hh, ?_⟩
  intro x hx
  apply RCLike.pos_iff.mpr
  refine ⟨?_, hh.im_star_dotProduct_mulVec_self x⟩
  have hX : matrixUnvector x ≠ 0 := by
    intro h
    apply hx
    have hv := congrArg matrixVector h
    simpa only [matrixVector_unvector] using hv
  have hp := sylvester_quadratic_pos hP hX
  change 0 < RCLike.re (star x ⬝ᵥ matrixSuper (sylvester P) *ᵥ x)
  rw [matrixSuper_quadratic]
  exact hp

/-- The coordinate inverse is exactly the already-proved physical Sylvester inverse. -/
theorem jordanSuper_inv_mulVec {P : Matrix n n ℂ} (hP : P.PosDef) (x : n × n → ℂ) :
    (jordanSuper P)⁻¹ *ᵥ x = matrixVector ((sylvesterEquiv P hP).symm (matrixUnvector x)) := by
  letI : Invertible (jordanSuper P) := (jordanSuper_posDef hP).isUnit.invertible
  apply Matrix.mulVec_injective_iff_isUnit.mpr (jordanSuper_posDef hP).isUnit
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  change x = matrixSuper (sylvester P) *ᵥ matrixVector ((sylvesterEquiv P hP).symm (matrixUnvector x))
  rw [matrixSuper_mulVec, matrixUnvector_vector, sylvester_inverse_solve, matrixVector_unvector]

end MatrixSpencer
