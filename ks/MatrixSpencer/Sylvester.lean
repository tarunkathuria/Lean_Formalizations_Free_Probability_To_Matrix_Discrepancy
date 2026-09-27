import MatrixSpencer.TraceGeometry
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The positive Sylvester operator

For a positive definite matrix `Q`, the complex-linear map `X ↦ QX + XQ`
is positive in the real trace pairing and is bijective. Its inverse commutes
with conjugate transpose, so Hermitian right-hand sides have Hermitian solutions.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace MatrixSpencer

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Left plus right multiplication by the same physical matrix. -/
noncomputable def sylvester (Q : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
  LinearMap.mulLeft ℂ Q + LinearMap.mulRight ℂ Q

omit [DecidableEq n] in
@[simp] theorem sylvester_apply (Q X : Matrix n n ℂ) :
    sylvester Q X = Q * X + X * Q := rfl

/-- A positive definite weight has a strictly positive trace pairing on every
nonzero matrix, even when that matrix is not Hermitian. -/
theorem realTrace_weighted_square_pos {Q X : Matrix n n ℂ}
    (hQ : Q.PosDef) (hX : X ≠ 0) : 0 < realTrace (Xᴴ * Q * X) := by
  have hroot : (CFC.sqrt Q).IsHermitian := hQ.posDef_sqrt.isHermitian
  have hne : CFC.sqrt Q * X ≠ 0 := by
    intro h
    apply hX
    exact hQ.posDef_sqrt.isUnit.mul_left_cancel (by simpa using h)
  have hpos : 0 < realTrace ((CFC.sqrt Q * X)ᴴ * (CFC.sqrt Q * X)) := by
    have hn := realTrace_conjTranspose_mul_self_nonneg (CFC.sqrt Q * X)
    have hz : realTrace ((CFC.sqrt Q * X)ᴴ * (CFC.sqrt Q * X)) ≠ 0 :=
      mt (realTrace_conjTranspose_mul_self_eq_zero_iff _).mp hne
    exact lt_of_le_of_ne hn (Ne.symm hz)
  have hid : (CFC.sqrt Q * X)ᴴ * (CFC.sqrt Q * X) = Xᴴ * Q * X := by
    rw [Matrix.conjTranspose_mul, hroot.eq]
    calc
      Xᴴ * CFC.sqrt Q * (CFC.sqrt Q * X) =
          Xᴴ * (CFC.sqrt Q * CFC.sqrt Q) * X := by
        simp only [Matrix.mul_assoc]
      _ = Xᴴ * Q * X := by rw [CFC.sqrt_mul_sqrt_self Q hQ.posSemidef.nonneg]
  rwa [hid] at hpos

/-- Strict positivity of the Sylvester quadratic response on full complex matrix space. -/
theorem sylvester_quadratic_pos {Q X : Matrix n n ℂ}
    (hQ : Q.PosDef) (hX : X ≠ 0) : 0 < realTrace (Xᴴ * sylvester Q X) := by
  have hp := realTrace_weighted_square_pos hQ hX
  have hn := realTrace_mul_nonneg
    (Matrix.posSemidef_conjTranspose_mul_self X) hQ.posSemidef
  simp only [sylvester_apply, Matrix.mul_add, realTrace_add]
  simp only [Matrix.mul_assoc] at hp hn ⊢
  linarith

theorem sylvester_injective {Q : Matrix n n ℂ} (hQ : Q.PosDef) :
    Function.Injective (sylvester Q) := by
  intro X Y hXY
  by_contra hne
  have hpos := sylvester_quadratic_pos hQ (sub_ne_zero.mpr hne)
  have hz : sylvester Q (X - Y) = 0 := by rw [map_sub, hXY, sub_self]
  rw [hz, Matrix.mul_zero, realTrace_zero] at hpos
  exact (lt_irrefl 0) hpos

theorem sylvester_bijective {Q : Matrix n n ℂ} (hQ : Q.PosDef) :
    Function.Bijective (sylvester Q) :=
  ⟨sylvester_injective hQ, LinearMap.injective_iff_surjective.mp (sylvester_injective hQ)⟩

/-- The Sylvester inverse is obtained from proved finite-dimensional bijectivity. -/
noncomputable def sylvesterEquiv (Q : Matrix n n ℂ) (hQ : Q.PosDef) :
    Matrix n n ℂ ≃ₗ[ℂ] Matrix n n ℂ :=
  LinearEquiv.ofBijective (sylvester Q) (sylvester_bijective hQ)

@[simp] theorem sylvesterEquiv_apply (Q : Matrix n n ℂ) (hQ : Q.PosDef)
    (X : Matrix n n ℂ) : sylvesterEquiv Q hQ X = Q * X + X * Q := rfl

@[simp] theorem sylvester_inverse_solve (Q : Matrix n n ℂ) (hQ : Q.PosDef)
    (B : Matrix n n ℂ) : sylvester Q ((sylvesterEquiv Q hQ).symm B) = B :=
  (sylvesterEquiv Q hQ).apply_symm_apply B

omit [DecidableEq n] in
theorem sylvester_conjTranspose {Q : Matrix n n ℂ} (hQ : Q.IsHermitian)
    (X : Matrix n n ℂ) : sylvester Q Xᴴ = (sylvester Q X)ᴴ := by
  simp only [sylvester_apply, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hQ.eq]
  exact add_comm _ _

/-- The unique inverse solution respects conjugate transpose. -/
theorem sylvester_inverse_conjTranspose (Q : Matrix n n ℂ) (hQ : Q.PosDef)
    (B : Matrix n n ℂ) :
    ((sylvesterEquiv Q hQ).symm B)ᴴ = (sylvesterEquiv Q hQ).symm Bᴴ := by
  apply sylvester_injective hQ
  rw [sylvester_conjTranspose hQ.isHermitian, sylvester_inverse_solve,
    sylvester_inverse_solve]

theorem sylvester_inverse_isHermitian (Q : Matrix n n ℂ) (hQ : Q.PosDef)
    {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    ((sylvesterEquiv Q hQ).symm B).IsHermitian := by
  change ((sylvesterEquiv Q hQ).symm B)ᴴ = (sylvesterEquiv Q hQ).symm B
  rw [sylvester_inverse_conjTranspose, hB.eq]

open scoped Matrix.Norms.Frobenius in
/-- The Sylvester equivalence is continuous for Frobenius matrix geometry. -/
noncomputable def sylvesterContinuousEquiv (Q : Matrix n n ℂ) (hQ : Q.PosDef) :
    Matrix n n ℂ ≃L[ℂ] Matrix n n ℂ :=
  (sylvesterEquiv Q hQ).toContinuousLinearEquiv

/-- The same inverse on the real vector space of Hermitian matrices. -/
noncomputable def sylvesterHermitianEquiv (Q : Matrix n n ℂ) (hQ : Q.PosDef) :
    selfAdjoint (Matrix n n ℂ) ≃ₗ[ℝ] selfAdjoint (Matrix n n ℂ) where
  toFun X := ⟨sylvester Q X, by
    change (sylvester Q (X : Matrix n n ℂ))ᴴ = sylvester Q X
    rw [← sylvester_conjTranspose hQ.isHermitian]
    exact congrArg (sylvester Q) X.property⟩
  invFun B := ⟨(sylvesterEquiv Q hQ).symm B,
    sylvester_inverse_isHermitian Q hQ B.property⟩
  left_inv X := Subtype.ext ((sylvesterEquiv Q hQ).symm_apply_apply X)
  right_inv B := Subtype.ext (sylvester_inverse_solve Q hQ B)
  map_add' X Y := Subtype.ext ((sylvester Q).map_add X Y)
  map_smul' r X := Subtype.ext (((sylvester Q).restrictScalars ℝ).map_smul r X)

@[simp] theorem sylvesterHermitianEquiv_apply (Q : Matrix n n ℂ) (hQ : Q.PosDef)
    (X : selfAdjoint (Matrix n n ℂ)) :
    ↑(sylvesterHermitianEquiv Q hQ X) = sylvester Q X := rfl

@[simp] theorem sylvesterHermitianEquiv_symm_apply (Q : Matrix n n ℂ) (hQ : Q.PosDef)
    (B : selfAdjoint (Matrix n n ℂ)) :
    ↑((sylvesterHermitianEquiv Q hQ).symm B) = (sylvesterEquiv Q hQ).symm B := rfl

open scoped Matrix.Norms.Frobenius in
/-- Continuous invertibility on the real Hermitian space used by the square-root calculus. -/
noncomputable def sylvesterHermitianContinuousEquiv (Q : Matrix n n ℂ) (hQ : Q.PosDef) :
    selfAdjoint (Matrix n n ℂ) ≃L[ℝ] selfAdjoint (Matrix n n ℂ) := by
  letI : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
    inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
  exact (sylvesterHermitianEquiv Q hQ).toContinuousLinearEquiv

end MatrixSpencer
