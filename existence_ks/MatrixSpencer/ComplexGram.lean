import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Complex Gram caps and synthesis caps

All matrix inequalities use the positive-semidefinite order. All matrix
norms in this file use the Euclidean operator norm.
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MatrixSpencer

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Complexification of the entries of a real square matrix as a ring homomorphism. -/
def realMatrixEmbedding : Matrix ι ι ℝ →+* Matrix ι ι ℂ :=
  Complex.ofRealHom.mapMatrix

@[simp] theorem realMatrixEmbedding_apply (A : Matrix ι ι ℝ) (i j : ι) :
    realMatrixEmbedding A i j = (A i j : ℂ) :=
  rfl

/-- Entrywise complexification preserves positive semidefiniteness. -/
theorem realMatrixEmbedding_posSemidef (A : Matrix ι ι ℝ)
    (hA : A.PosSemidef) : (realMatrixEmbedding A).PosSemidef := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hB, map_mul]
  have hstar : realMatrixEmbedding (star B) = (realMatrixEmbedding B)ᴴ := by
    ext i j
    simp [realMatrixEmbedding, Matrix.star_eq_conjTranspose]
  rw [hstar]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Entrywise complexification preserves the positive-semidefinite matrix order. -/
theorem realMatrixEmbedding_mono {A B : Matrix ι ι ℝ} (hAB : A ≤ B) :
    realMatrixEmbedding A ≤ realMatrixEmbedding B := by
  apply Matrix.le_iff.mpr
  have h := realMatrixEmbedding_posSemidef (B - A) (Matrix.le_iff.mp hAB)
  simpa only [map_sub] using h

@[simp] theorem realMatrixEmbedding_algebraMap (t : ℝ) :
    realMatrixEmbedding (algebraMap ℝ (Matrix ι ι ℝ) t) =
      algebraMap ℝ (Matrix ι ι ℂ) t := by
  ext i j
  by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]

omit [DecidableEq ι] in
/-- A positive complex matrix is bounded by itself plus its transpose. -/
theorem complexGram_le_add_transpose (G : Matrix ι ι ℂ)
    (hG : G.PosSemidef) : G ≤ G + Gᵀ := by
  exact le_add_of_nonneg_right hG.transpose.nonneg

/-- The real Gram cap written without introducing an entrywise real-part map. -/
theorem complexGram_cap_of_symmetrized_cap (G : Matrix ι ι ℂ)
    (hG : G.PosSemidef) (t : ℝ)
    (hcap : G + Gᵀ ≤ algebraMap ℝ (Matrix ι ι ℂ) (2 * t)) :
    G ≤ algebraMap ℝ (Matrix ι ι ℂ) (2 * t) :=
  (complexGram_le_add_transpose G hG).trans hcap

/-- For a Hermitian matrix, adding the transpose doubles its embedded real part. -/
theorem hermitian_add_transpose_eq_realPart (G : Matrix ι ι ℂ)
    (hG : G.IsHermitian) :
    G + Gᵀ = realMatrixEmbedding (G.map Complex.re) +
      realMatrixEmbedding (G.map Complex.re) := by
  ext i j
  have hij : G j i = star (G i j) := (hG.apply j i).symm
  apply Complex.ext <;>
    simp [Matrix.add_apply, Matrix.transpose_apply, hij]

/-- A cap on the real part of a positive complex Gram matrix loses only a factor two. -/
theorem complexGram_cap_of_realPart_cap (G : Matrix ι ι ℂ)
    (hG : G.PosSemidef) (t : ℝ)
    (hcap : G.map Complex.re ≤ algebraMap ℝ (Matrix ι ι ℝ) t) :
    G ≤ algebraMap ℝ (Matrix ι ι ℂ) (2 * t) := by
  apply complexGram_cap_of_symmetrized_cap G hG t
  rw [hermitian_add_transpose_eq_realPart G hG.isHermitian]
  have h := realMatrixEmbedding_mono hcap
  rw [realMatrixEmbedding_algebraMap] at h
  calc
    _ ≤ algebraMap ℝ (Matrix ι ι ℂ) t + algebraMap ℝ (Matrix ι ι ℂ) t :=
      add_le_add h h
    _ = algebraMap ℝ (Matrix ι ι ℂ) (2 * t) := by rw [← map_add, two_mul]

/-- The two Gram products of a rectangular matrix have the same Euclidean operator norm. -/
theorem gramProducts_l2_norm_eq (V : Matrix ι κ ℂ) :
    ‖V * Vᴴ‖ = ‖Vᴴ * V‖ := by
  calc
    ‖V * Vᴴ‖ = ‖Vᴴ‖ * ‖Vᴴ‖ := by
      simpa only [Matrix.conjTranspose_conjTranspose] using
        Matrix.l2_opNorm_conjTranspose_mul_self Vᴴ
    _ = ‖V‖ * ‖V‖ := by rw [Matrix.l2_opNorm_conjTranspose]
    _ = ‖Vᴴ * V‖ := (Matrix.l2_opNorm_conjTranspose_mul_self V).symm

set_option maxHeartbeats 1000000 in
/-- A Gram bound on coefficients is the same bound on the actual synthesis frame. -/
theorem synthesis_cap_of_gram_cap (V : Matrix ι κ ℂ) {t : ℝ}
    (ht : 0 ≤ t)
    (hcap : Vᴴ * V ≤ algebraMap ℝ (Matrix κ κ ℂ) t) :
    V * Vᴴ ≤ algebraMap ℝ (Matrix ι ι ℂ) t := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := { }
  letI : CStarAlgebra (Matrix κ κ ℂ) := { }
  have hleft : 0 ≤ V * Vᴴ := (Matrix.posSemidef_self_mul_conjTranspose V).nonneg
  have hright : 0 ≤ Vᴴ * V := (Matrix.posSemidef_conjTranspose_mul_self V).nonneg
  apply (CStarAlgebra.norm_le_iff_le_algebraMap (V * Vᴴ) ht hleft).mp
  rw [gramProducts_l2_norm_eq]
  exact (CStarAlgebra.norm_le_iff_le_algebraMap (Vᴴ * V) ht hright).mpr hcap

/-- Coefficient Gram and synthesis frame caps are equivalent for rectangular matrices. -/
theorem gram_cap_iff_synthesis_cap (V : Matrix ι κ ℂ) {t : ℝ}
    (ht : 0 ≤ t) :
    Vᴴ * V ≤ algebraMap ℝ (Matrix κ κ ℂ) t ↔
      V * Vᴴ ≤ algebraMap ℝ (Matrix ι ι ℂ) t := by
  constructor
  · exact synthesis_cap_of_gram_cap V ht
  · intro h
    simpa only [Matrix.conjTranspose_conjTranspose] using
      synthesis_cap_of_gram_cap Vᴴ ht
        (by simpa only [Matrix.conjTranspose_conjTranspose] using h)

/-- The actual synthesis-frame estimate obtained from a real Gram cap. -/
theorem synthesis_cap_of_realGram_cap (V : Matrix ι κ ℂ) {t : ℝ}
    (ht : 0 ≤ t)
    (hcap : (Vᴴ * V).map Complex.re ≤ algebraMap ℝ (Matrix κ κ ℝ) t) :
    V * Vᴴ ≤ algebraMap ℝ (Matrix ι ι ℂ) (2 * t) := by
  apply synthesis_cap_of_gram_cap V (mul_nonneg zero_le_two ht)
  exact complexGram_cap_of_realPart_cap (Vᴴ * V)
    (Matrix.posSemidef_conjTranspose_mul_self V) t hcap

end MatrixSpencer
