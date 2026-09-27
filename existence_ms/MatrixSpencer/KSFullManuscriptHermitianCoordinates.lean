import MatrixSpencer.KSFullManuscriptSDPIdentity
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Fixed entry coordinates for Hermitian matrices

A real square array stores the real upper triangle and diagonal; its strict
lower triangle stores the imaginary upper triangle. Decoding uses only entry
selection, signs, and the fixed complex unit. The resulting maps are inverse
on the entire Hermitian space. These explicit coordinates do not invoke a
chosen orthonormal basis.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptHermitianCoordinates

variable {n : Type*} [LinearOrder n]

def decode (x : n × n → ℝ) : Matrix n n ℂ := fun i j =>
  if i = j then (x (i, i) : ℂ)
  else if i < j then (x (i, j) : ℂ) + (x (j, i) : ℂ) * Complex.I
  else (x (j, i) : ℂ) - (x (i, j) : ℂ) * Complex.I

def encode (A : Matrix n n ℂ) : n × n → ℝ := fun p =>
  if p.1 ≤ p.2 then (A p.1 p.2).re else (A p.2 p.1).im

theorem decode_diagonal (x : n × n → ℝ) (i : n) : decode x i i = x (i, i) := by
  simp [decode]

theorem decode_isHermitian (x : n × n → ℝ) : (decode x).IsHermitian := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [Matrix.conjTranspose_apply, decode, hij, hij.ne, hij.ne', not_lt.mpr hij.le,
      sub_eq_add_neg]
  · simp [Matrix.conjTranspose_apply, decode]
  · simp [Matrix.conjTranspose_apply, decode, hji, hji.ne, hji.ne', not_lt.mpr hji.le,
      sub_eq_add_neg]

theorem encode_decode (x : n × n → ℝ) : encode (decode x) = x := by
  funext p
  rcases p with ⟨i,j⟩
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [encode, decode, hij, hij.le, hij.ne]
  · simp [encode, decode]
  · simp [encode, decode, hji, hji.ne, not_le.mpr hji]

theorem decode_encode (A : Matrix n n ℂ) (hA : A.IsHermitian) : decode (encode A) = A := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp only [decode, if_neg hij.ne, if_pos hij, encode, if_pos hij.le,
      if_neg (not_le.mpr hij)]
    exact Complex.re_add_im _
  · simp only [decode, encode, if_pos le_rfl]
    exact hA.coe_re_apply_self i
  · have ha : star (A j i) = A i j := hA.apply i j
    simp only [decode, if_neg hji.ne', if_neg (not_lt.mpr hji.le), encode,
      if_pos hji.le, if_neg (not_le.mpr hji)]
    rw [← ha]
    apply Complex.ext <;> simp

theorem decode_add (x y : n × n → ℝ) : decode (x + y) = decode x + decode y := by
  ext i j
  simp only [decode, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> push_cast <;> ring

theorem decode_smul (a : ℝ) (x : n × n → ℝ) : decode (a • x) = a • decode x := by
  ext i j
  simp only [decode, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> simp only [Complex.real_smul] <;> ring

def linear : (n × n → ℝ) →ₗ[ℝ] selfAdjoint (Matrix n n ℂ) where
  toFun x := ⟨decode x, decode_isHermitian x⟩
  map_add' x y := Subtype.ext (decode_add x y)
  map_smul' a x := Subtype.ext (decode_smul a x)

/-- A fixed finite-entry linear equivalence, with an explicit inverse. -/
def equiv : (n × n → ℝ) ≃ₗ[ℝ] selfAdjoint (Matrix n n ℂ) where
  __ := linear
  invFun A := encode A
  left_inv := encode_decode
  right_inv A := Subtype.ext (decode_encode (A : Matrix n n ℂ) A.property)

variable [Fintype n]

theorem decode_trace (x : n × n → ℝ) : realTrace (decode x) = ∑ i, x (i, i) := by
  simp [realTrace, Matrix.trace, Matrix.diag, decode_diagonal]

end MatrixSpencer.KSFullManuscriptHermitianCoordinates
