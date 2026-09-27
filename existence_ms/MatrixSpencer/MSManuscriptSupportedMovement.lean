import MatrixSpencer.CovarianceFaceDomination
import MatrixSpencer.MSManuscriptSupportedOwner

/-!
# Exact supported coordinates of the actual movement covariance

Every PSD covariance dominated by the stored physical owner is reconstructed
exactly in its stored isometric frame. Compression preserves both positivity
and the upper covariance bound, including zero-dimensional support. These
are consequences of the already proved covariance-face domination algebra;
no range, factorization, or reduced-covariance oracle is assumed.
-/

open Matrix
open scoped MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptSupportedMovement

variable {N k : ℕ}

def reduced (Q : Matrix (Fin N) (Fin N) ℝ) (V : Matrix (Fin N) (Fin k) ℝ) :
    Matrix (Fin k) (Fin k) ℝ := Vᵀ * Q * V

theorem reduced_posSemidef {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Q.PosSemidef)
    (V : Matrix (Fin N) (Fin k) ℝ) : (reduced Q V).PosSemidef :=
  covarianceFace_compress_posSemidef V hQ

theorem reduced_le (Q : Matrix (Fin N) (Fin N) ℝ) (V : Matrix (Fin N) (Fin k) ℝ)
    (K : Matrix (Fin k) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (hQC : Q ≤ covarianceLift V K) : reduced Q V ≤ K :=
  covarianceFace_compress_le V hV K hQC

theorem reconstruct (V : Matrix (Fin N) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (K : Matrix (Fin k) (Fin k) ℝ) {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.PosSemidef) (hQC : Q ≤ covarianceLift V K) :
    covarianceLift V (reduced Q V) = Q := covarianceFace_reconstruct_of_le V hV K hQ hQC

theorem reduced_bounds (V : Matrix (Fin N) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (K : Matrix (Fin k) (Fin k) ℝ) {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.PosSemidef) (hQC : Q ≤ covarianceLift V K) (hK : K ≤ 1) :
    (reduced Q V).PosSemidef ∧ reduced Q V ≤ K ∧ reduced Q V ≤ 1 ∧
      covarianceLift V (reduced Q V) = Q :=
  ⟨reduced_posSemidef hQ V, reduced_le Q V K hV hQC,
    (reduced_le Q V K hV hQC).trans hK, reconstruct V hV K hQ hQC⟩

open MSManuscriptSupportedOwner

/-- The physical upper bound also implies the upper bound on the stored
reduced matrix; the lower support floor is not needed for this implication. -/
theorem owner_matrix_le_one (O : Owner N) {δ : ℝ} (hO : O.Valid δ)
    (hcap : O.physical ≤ 1) : O.matrix ≤ 1 := by
  have h := covarianceLift_mono O.frameᵀ hcap
  change O.frameᵀ * covarianceLift O.frame O.matrix * O.frame ≤ O.frameᵀ * 1 * O.frame at h
  rwa [covarianceLift_compress O.frame hO.1, Matrix.mul_one, hO.1] at h

/-- All input fields needed by the actual supported movement/drift theorem,
obtained from the physical covariance domination and stored owner invariant. -/
theorem owner_supported (O : Owner N) {δ : ℝ} (hO : O.Valid δ)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Q.PosSemidef)
    (hQC : Q ≤ O.physical) (hcap : O.physical ≤ 1) :
    (reduced Q O.frame).PosSemidef ∧ reduced Q O.frame ≤ O.matrix ∧
      reduced Q O.frame ≤ 1 ∧ covarianceLift O.frame (reduced Q O.frame) = Q :=
  reduced_bounds O.frame hO.1 O.matrix hQ hQC (owner_matrix_le_one O hO hcap)

end MatrixSpencer.MSManuscriptSupportedMovement
