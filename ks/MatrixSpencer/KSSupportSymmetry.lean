import MatrixSpencer.KSSpinSymmetry
import MatrixSpencer.KrausReducedFamily

/-! Induced sign involution and transport symmetry on a possibly proper physical support. -/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer.KSSupportSymmetry

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def compress (V : Matrix n m ℂ) (X : Matrix n n ℂ) : Matrix m m ℂ := Vᴴ * X * V

theorem compress_isHermitian (V : Matrix n m ℂ) {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    (compress V X).IsHermitian := by
  simpa only [Matrix.conjTranspose_conjTranspose] using
    Matrix.isHermitian_mul_mul_conjTranspose Vᴴ hX

theorem compress_posSemidef (V : Matrix n m ℂ) {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    (compress V X).PosSemidef := hX.conjTranspose_mul_mul_same V

theorem compress_posDef (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {X : Matrix n n ℂ} (hX : X.PosDef) : (compress V X).PosDef :=
  posDef_isometry_compression V hV hX

theorem compression_nonzero (V : Matrix n m ℂ) {X : Matrix n n ℂ}
    (hX : X ≠ 0) (hreconstruct : V * compress V X * Vᴴ = X) : compress V X ≠ 0 := by
  intro hzero
  rw [hzero, Matrix.mul_zero, Matrix.zero_mul] at hreconstruct
  exact hX hreconstruct.symm

theorem intertwine (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) (J : Matrix n n ℂ)
    (hPJ : Commute (V * Vᴴ) J) : V * compress V J = J * V := by
  calc
    V * compress V J = (V * Vᴴ) * J * V := by simp only [compress, Matrix.mul_assoc]
    _ = J * (V * Vᴴ) * V := by rw [hPJ.eq]
    _ = J * V := by simp only [Matrix.mul_assoc, hV, Matrix.mul_one]

theorem intertwine_adjoint (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) {J : Matrix n n ℂ}
    (hJ : J.IsHermitian) (hPJ : Commute (V * Vᴴ) J) : compress V J * Vᴴ = Vᴴ * J := by
  have h := congrArg Matrix.conjTranspose (intertwine V hV J hPJ)
  simpa only [Matrix.conjTranspose_mul, hJ.eq, (compress_isHermitian V hJ).eq] using h

theorem compressed_involution (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) {J : Matrix n n ℂ}
    (hJJ : J * J = 1) (hPJ : Commute (V * Vᴴ) J) : compress V J * compress V J = 1 := by
  calc
    _ = Vᴴ * J * (V * compress V J) := by simp only [compress, Matrix.mul_assoc]
    _ = Vᴴ * J * (J * V) := by rw [intertwine V hV J hPJ]
    _ = Vᴴ * (J * J) * V := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hJJ, Matrix.mul_one, hV]

theorem compressed_commute (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) {J X : Matrix n n ℂ}
    (hJ : J.IsHermitian) (hPJ : Commute (V * Vᴴ) J) (hJX : Commute J X) :
    Commute (compress V J) (compress V X) := by
  change compress V J * compress V X = compress V X * compress V J
  calc
    _ = (compress V J * Vᴴ) * X * V := by simp only [compress, Matrix.mul_assoc]
    _ = Vᴴ * J * X * V := by rw [intertwine_adjoint V hV hJ hPJ]
    _ = Vᴴ * X * J * V := by rw [Matrix.mul_assoc Vᴴ J X, hJX.eq, ← Matrix.mul_assoc]
    _ = Vᴴ * X * (V * compress V J) := by rw [intertwine V hV J hPJ]; simp only [Matrix.mul_assoc]
    _ = compress V X * compress V J := by simp only [compress, Matrix.mul_assoc]

theorem commute_of_conjugate_fixed {J X : Matrix n n ℂ}
    (hJJ : J * J = 1) (hX : KSSignSymmetry.conjugate J X = X) : Commute J X := by
  change J * X = X * J
  have h := congrArg (fun M : Matrix n n ℂ => M * J) hX
  simpa only [KSSignSymmetry.conjugate, Matrix.mul_assoc, hJJ, Matrix.mul_one] using h

theorem commute_sqrt {J X : Matrix n n ℂ} (hJ : J.IsHermitian)
    (hJJ : J * J = 1) (hX : X.PosSemidef) (hJX : Commute J X) : Commute J (CFC.sqrt X) := by
  apply commute_of_conjugate_fixed hJJ
  have h := KSSignSymmetry.sqrt_conjugate hJ hJJ hX
  rw [KSSignSymmetry.conjugate_eq_of_commute hJJ hJX] at h
  exact h.symm

theorem commute_inv {J X : Matrix n n ℂ} (hX : X.PosDef) (hJX : Commute J X) :
    Commute J X⁻¹ := by
  letI : Invertible X := hX.isUnit.invertible
  change J * X⁻¹ = X⁻¹ * J
  calc
    J * X⁻¹ = (X⁻¹ * X) * J * X⁻¹ := by rw [Matrix.inv_mul_of_invertible, Matrix.one_mul]
    _ = X⁻¹ * (X * J) * X⁻¹ := by simp only [Matrix.mul_assoc]
    _ = X⁻¹ * (J * X) * X⁻¹ := by rw [hJX.eq]
    _ = X⁻¹ * J := by simp only [← Matrix.mul_assoc, Matrix.mul_inv_cancel_right_of_invertible]

/-- The explicitly constructed actual transport inherits the sign symmetry. -/
theorem commute_transport {J S M : Matrix n n ℂ} (hJ : J.IsHermitian)
    (hJJ : J * J = 1) (hS : S.PosDef) (hM : M.PosDef)
    (hJS : Commute J S) (hJM : Commute J M) : Commute J (transportOptimizer S M) := by
  have hroot := commute_sqrt hJ hJJ hS.posSemidef hJS
  have hp : (CFC.sqrt S * M * CFC.sqrt S).PosSemidef := by
    simpa only [(CFC.sqrt_nonneg S).posSemidef.isHermitian.eq] using
      hM.posSemidef.mul_mul_conjTranspose_same (CFC.sqrt S)
  have hcore := commute_sqrt hJ hJJ hp
    ((hroot.mul_right hJM).mul_right hroot)
  have hcore' : Commute J (fidelityCore S M) := by
    simpa only [(CFC.sqrt_nonneg S).posSemidef.isHermitian.eq, fidelityCore] using hcore
  exact (hroot.mul_right (commute_inv (fidelityCore_posDef hS hM) hcore')).mul_right hroot

variable {ι : Type*} [Fintype ι]

theorem supportProjection_inverse_factor (B : ι → Matrix n n ℂ) :
    (krausSupportEmbedding B * (krausCompressedSource B 1)⁻¹ * (krausSupportEmbedding B)ᴴ) *
      krausChannel B 1 = krausSupportProjection B := by
  letI : Invertible (krausCompressedSource B 1) :=
    (krausCompressedSource_posDef B Matrix.PosDef.one).isUnit.invertible
  conv_lhs => rhs; rw [← krausCompressedSource_reconstruct B Matrix.PosSemidef.one]
  calc
    _ = krausSupportEmbedding B * (krausCompressedSource B 1)⁻¹ *
        ((krausSupportEmbedding B)ᴴ * krausSupportEmbedding B) * krausCompressedSource B 1 *
          (krausSupportEmbedding B)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [krausSupportEmbedding_isometry, Matrix.mul_one,
        Matrix.inv_mul_cancel_right_of_invertible]
      rfl

/-- Commutation with a source implies commutation with its actual range
projection. The proof uses its positive compressed inverse, with no gap bound. -/
theorem supportProjection_commute (B : ι → Matrix n n ℂ) {J : Matrix n n ℂ}
    (hJ : J.IsHermitian) (hJM : Commute J (krausChannel B 1)) :
    Commute (krausSupportProjection B) J := by
  let P := krausSupportProjection B
  have hMP : krausChannel B 1 * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, kraus_identity_source_projection, sub_self]
  have hMJP : krausChannel B 1 * (J * (1 - P)) = 0 := by
    rw [← Matrix.mul_assoc, ← hJM.eq, Matrix.mul_assoc, hMP, Matrix.mul_zero]
  have hPJP : P * (J * (1 - P)) = 0 := by
    change krausSupportProjection B * (J * (1 - P)) = 0
    rw [← supportProjection_inverse_factor B, Matrix.mul_assoc, hMJP, Matrix.mul_zero]
  have hrow : P * J * P = P * J := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one] at hPJP
    exact (sub_eq_zero.mp hPJP).symm
  have hcol : P * J * P = J * P := by
    have h := congrArg Matrix.conjTranspose hrow
    change (krausSupportProjection B * J * krausSupportProjection B)ᴴ =
      (krausSupportProjection B * J)ᴴ at h
    simpa only [Matrix.conjTranspose_mul, (krausSupportProjection_isHermitian B).eq,
      hJ.eq, Matrix.mul_assoc] using h
  exact hrow.symm.trans hcol

end MatrixSpencer.KSSupportSymmetry
