import MatrixSpencer.MSManuscriptAnchorDensity



open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptCertificateReport
open MSManuscriptAnchorDensity KSOwnerInputBounds
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}

def baseReport (H : Matrix (Fin d) (Fin d) ℂ) (θ : ℝ) (hd : 0 < d) (ε : ℝ) : ℝ :=
  KSNumericalOwnerPotential.report H emptyFamily 0 θ hd ε

theorem empty_owner_eq_base [Nonempty (Fin d)] (H : Matrix (Fin d) (Fin d) ℂ) (θ : ℝ) :
    ownerPotential H emptyFamily 0 θ = baseDensityPotential H θ := by
  rw [ownerPotential_eq_densityPotential H emptyFamily (fun i => i.elim) Matrix.PosSemidef.zero]
  have hB : covarianceKraus (emptyFamily (d := d)) 0 = emptyFamily := by
    funext i
    exact i.elim
  rw [hB]
  rfl

theorem baseReport_accuracy [Nonempty (Fin d)] (H : Matrix (Fin d) (Fin d) ℂ)
    (hH : H.IsHermitian) {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) (hd : 0 < d) :
    |baseReport H θ hd ε - baseDensityPotential H θ| ≤ ε := by
  rw [← empty_owner_eq_base]
  exact KSNumericalOwnerPotential.report_accuracy H hH emptyFamily (fun i => i.elim)
    Matrix.PosSemidef.zero hθ hε hd

def anchorTolerance (R ε : ℝ) : ℝ := ε / (3*(R+1))

theorem anchorTolerance_pos {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    0 < anchorTolerance R ε := by unfold anchorTolerance; positivity

theorem anchorTolerance_budget {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 ≤ ε) :
    anchorTolerance R ε * R ≤ ε/3 := by
  unfold anchorTolerance
  have hden : 0 < 3*(R+1) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith

/-- R can be fixed at epoch start to retain the same computed anchor density. -/
def tangentReport (Hstar D : Matrix (Fin d) (Fin d) ℂ)
    (θ R ε : ℝ) (hd : 0 < d) : ℝ :=
  realTrace (saved Hstar θ (anchorTolerance R ε) hd * D)

theorem tangentReport_accuracy [Nonempty (Fin d)]
    (Hstar D : Matrix (Fin d) (Fin d) ℂ) (hHstar : Hstar.IsHermitian) (hD : D.IsHermitian)
    {θ R ε : ℝ} (hθ : 0 < θ) (hR : 0 ≤ R) (hε : 0 < ε) (hd : 0 < d)
    (hDnorm : Real.sqrt (matrixEnergy D) ≤ R) :
    |tangentReport Hstar D θ R ε hd - realTrace (ownerCertificateDensity Hstar θ * D)| ≤ ε/3 :=
  (saved_tangent_error Hstar hHstar hθ (anchorTolerance_pos hR hε) hd D hD).trans
    ((mul_le_mul_of_nonneg_left hDnorm (anchorTolerance_pos hR hε).le).trans
      (anchorTolerance_budget hR hε.le))

def report (Hstar H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ)
    (θ R ε : ℝ) (hd : 0 < d) : ℝ :=
  KSNumericalOwnerPotential.report H A C θ hd (ε/3) - baseReport Hstar θ hd (ε/3) -
    tangentReport Hstar (H-Hstar) θ R ε hd

theorem report_accuracy [Nonempty (Fin d)]
    (Hstar H : Matrix (Fin d) (Fin d) ℂ) (hHstar : Hstar.IsHermitian) (hH : H.IsHermitian)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ R ε : ℝ}
    (hθ : 0 < θ) (hR : 0 ≤ R) (hε : 0 < ε) (hd : 0 < d)
    (hDnorm : Real.sqrt (matrixEnergy (H-Hstar)) ≤ R) :
    |report Hstar H A C θ R ε hd - ownerCertificate Hstar A θ H C| ≤ ε := by
  have hv := KSNumericalOwnerPotential.report_accuracy H hH A hA hC hθ (by linarith : 0<ε/3) hd
  have hb := baseReport_accuracy Hstar hHstar hθ (by linarith : 0<ε/3) hd
  have ht := tangentReport_accuracy Hstar (H-Hstar) hHstar (hH.sub hHstar) hθ hR hε hd hDnorm
  have htri := abs_sub (KSNumericalOwnerPotential.report H A C θ hd (ε/3)-ownerPotential H A C θ)
    (baseReport Hstar θ hd (ε/3)-baseDensityPotential Hstar θ)
  have htri' := abs_sub
    ((KSNumericalOwnerPotential.report H A C θ hd (ε/3)-ownerPotential H A C θ) -
      (baseReport Hstar θ hd (ε/3)-baseDensityPotential Hstar θ))
    (tangentReport Hstar (H-Hstar) θ R ε hd-realTrace (ownerCertificateDensity Hstar θ*(H-Hstar)))
  have he : report Hstar H A C θ R ε hd - ownerCertificate Hstar A θ H C =
      ((KSNumericalOwnerPotential.report H A C θ hd (ε/3)-ownerPotential H A C θ) -
        (baseReport Hstar θ hd (ε/3)-baseDensityPotential Hstar θ)) -
      (tangentReport Hstar (H-Hstar) θ R ε hd-realTrace (ownerCertificateDensity Hstar θ*(H-Hstar))) := by
    unfold report ownerCertificate ownerCertificateTangent
    ring
  rw [he]
  linarith

/-- A report with its displacement budget computed directly from the input entries. -/
def automaticReport (Hstar H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ)
    (θ ε : ℝ) (hd : 0 < d) : ℝ :=
  report Hstar H A C θ (Real.sqrt (matrixEnergy (H-Hstar))) ε hd

/-- No numerical report-accuracy or displacement-budget hypothesis remains. -/
theorem automaticReport_accuracy [Nonempty (Fin d)]
    (Hstar H : Matrix (Fin d) (Fin d) ℂ) (hHstar : Hstar.IsHermitian) (hH : H.IsHermitian)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ ε : ℝ}
    (hθ : 0 < θ) (hε : 0 < ε) (hd : 0 < d) :
    |automaticReport Hstar H A C θ ε hd - ownerCertificate Hstar A θ H C| ≤ ε :=
  report_accuracy Hstar H hHstar hH A hA hC hθ (Real.sqrt_nonneg _) hε hd le_rfl

/-- Accumulated tangent error for a fixed saved density along a finite list of movements. -/
theorem saved_movement_sum_error [Nonempty (Fin d)] {T : ℕ}
    (Hstar : Matrix (Fin d) (Fin d) ℂ) (hHstar : Hstar.IsHermitian)
    (D : Fin T → Matrix (Fin d) (Fin d) ℂ) (hD : ∀ i, (D i).IsHermitian)
    {θ τ : ℝ} (hθ : 0 < θ) (hτ : 0 < τ) (hd : 0 < d) :
    |(∑ i, realTrace (saved Hstar θ τ hd * D i)) -
      (∑ i, realTrace (ownerCertificateDensity Hstar θ * D i))| ≤
      τ * ∑ i, Real.sqrt (matrixEnergy (D i)) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ =>
    saved_tangent_error Hstar hHstar hθ hτ hd (D i) (hD i)))

end MatrixSpencer.MSManuscriptCertificateReport
