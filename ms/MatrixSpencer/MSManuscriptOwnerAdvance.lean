import MatrixSpencer.MSManuscriptSupportedMovement
import MatrixSpencer.CovarianceMovement

/-! Actual covariance withdrawal stored in the existing numerical owner frame.
The frame is unchanged by movement. The factorization, support preservation,
and restored δ floor are consequences of the actual computed reduced Q. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptOwnerAdvance
open MSManuscriptSupportedOwner MSManuscriptSupportedMovement
variable {N : ℕ}

def advance (O : Owner N) (Q : Matrix (Fin N) (Fin N) ℝ) (h : ℝ) : Owner N where
  dim := O.dim
  frame := O.frame
  matrix := O.matrix-h^2 • reduced Q O.frame

theorem physical (O : Owner N) {δ : ℝ} (hO : O.Valid δ)
    (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : Q.PosSemidef) (hQC : Q≤O.physical) (h : ℝ) :
    (advance O Q h).physical=O.physical-h^2 • Q := by
  have he := reconstruct O.frame hO.1 O.matrix hQ hQC
  change O.frame*(O.matrix-h^2 • reduced Q O.frame)*O.frameᵀ=O.frame*O.matrix*O.frameᵀ-h^2 • Q
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul]
  rw [show O.frame*reduced Q O.frame*O.frameᵀ=Q from he]

theorem valid (O : Owner N) {δ h : ℝ} (hδ : 0≤δ) (hO : O.Valid (2*δ))
    (Q : Matrix (Fin N) (Fin N) ℝ) (hQC : Q≤O.physical) (hh : h^2≤1/2) :
    (advance O Q h).Valid δ := by
  have hred := reduced_le Q O.frame O.matrix hO.1 hQC
  have hlow := covarianceMovement_lower hred h
  have hcoef : 0≤1-h^2 := by linarith
  have hscaled : ((1-h^2)*(2*δ)) • (1 : Matrix (Fin O.dim) (Fin O.dim) ℝ)≤(1-h^2) • O.matrix := by
    apply Matrix.le_iff.mpr
    have hp := (Matrix.le_iff.mp hO.2).smul hcoef
    convert hp using 1
    module
  have hscalar : δ • (1 : Matrix (Fin O.dim) (Fin O.dim) ℝ)≤((1-h^2)*(2*δ)) • 1 := by
    apply Matrix.le_iff.mpr
    rw [←sub_smul]
    exact Matrix.PosSemidef.one.smul (by nlinarith)
  exact ⟨hO.1,hscalar.trans (hscaled.trans hlow)⟩

theorem below (O : Owner N) {δ : ℝ} (hO : O.Valid δ)
    (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : Q.PosSemidef) (hQC : Q≤O.physical) (h : ℝ) :
    (advance O Q h).physical≤O.physical := by
  rw [physical O hO Q hQ hQC h]
  exact sub_le_self _ (hQ.smul (sq_nonneg h)).nonneg

theorem support (O : Owner N) {δ h : ℝ} (hδ : 0≤δ) (hO : O.Valid δ)
    (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : Q.PosSemidef) (hQC : Q≤O.physical) (hh : h^2<1) :
    LinearMap.range (Matrix.toEuclideanCLM (𝕜:=ℝ) (advance O Q h).physical).toLinearMap=
      LinearMap.range (Matrix.toEuclideanCLM (𝕜:=ℝ) O.physical).toLinearMap := by
  rw [physical O hO Q hQ hQC h]
  exact (covarianceMovement_posSemidef_range (hO.physical_posSemidef O hδ) hQ hQC hh).2.2

theorem trace (O : Owner N) {δ : ℝ} (hO : O.Valid δ)
    (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : Q.PosSemidef) (hQC : Q≤O.physical) (h : ℝ) :
    realTrace (advance O Q h).physical=realTrace O.physical-h^2*realTrace Q := by
  rw [physical O hO Q hQ hQC h]
  exact covarianceMovement_trace _ _ _

end MatrixSpencer.MSManuscriptOwnerAdvance
