import MatrixSpencer.MSManuscriptCertificateReport
import MatrixSpencer.MSConvexOwnerValue

/-! The original square walk with convex owner-value queries substituted.
The state, invariants, tuning constants and non-query primitives remain original. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexCertificateReport
open MSManuscriptCertificateReport MSManuscriptAnchorDensity KSOwnerInputBounds
variable [MSConvexOwnerValue.Oracle]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
attribute [local irreducible] ownerPotential ownerCertificate

def baseReport (H : Matrix (Fin d) (Fin d) ℂ) (θ : ℝ) (hd : 0 < d) (ε : ℝ) : ℝ :=
  MSConvexOwnerValue.report H emptyFamily 0 θ hd ε

theorem baseReport_accuracy [Nonempty (Fin d)] (H : Matrix (Fin d) (Fin d) ℂ)
    (hH : H.IsHermitian) {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) (hd : 0 < d) :
    |baseReport H θ hd ε - baseDensityPotential H θ| ≤ ε := by
  rw [← empty_owner_eq_base]
  exact MSConvexOwnerValue.report_accuracy H hH emptyFamily (fun i => i.elim)
    Matrix.PosSemidef.zero hθ hε hd

def report (Hstar H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ)
    (θ R ε : ℝ) (hd : 0 < d) : ℝ :=
  MSConvexOwnerValue.report H A C θ hd (ε/3) - baseReport Hstar θ hd (ε/3) -
    tangentReport Hstar (H-Hstar) θ R ε hd

theorem report_accuracy [Nonempty (Fin d)]
    (Hstar H : Matrix (Fin d) (Fin d) ℂ) (hHstar : Hstar.IsHermitian) (hH : H.IsHermitian)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ R ε : ℝ}
    (hθ : 0 < θ) (hR : 0 ≤ R) (hε : 0 < ε) (hd : 0 < d)
    (hDnorm : Real.sqrt (matrixEnergy (H-Hstar)) ≤ R) :
    |report Hstar H A C θ R ε hd - ownerCertificate Hstar A θ H C| ≤ ε := by
  have hv := MSConvexOwnerValue.report_accuracy H hH A hA hC hθ (by linarith : 0<ε/3) hd
  have hb := baseReport_accuracy Hstar hHstar hθ (by linarith : 0<ε/3) hd
  have ht := tangentReport_accuracy Hstar (H-Hstar) hHstar (hH.sub hHstar) hθ hR hε hd hDnorm
  have htri := abs_sub (MSConvexOwnerValue.report H A C θ hd (ε/3)-ownerPotential H A C θ)
    (baseReport Hstar θ hd (ε/3)-baseDensityPotential Hstar θ)
  have htri' := abs_sub
    ((MSConvexOwnerValue.report H A C θ hd (ε/3)-ownerPotential H A C θ) -
      (baseReport Hstar θ hd (ε/3)-baseDensityPotential Hstar θ))
    (tangentReport Hstar (H-Hstar) θ R ε hd-realTrace (ownerCertificateDensity Hstar θ*(H-Hstar)))
  have he : report Hstar H A C θ R ε hd - ownerCertificate Hstar A θ H C =
      ((MSConvexOwnerValue.report H A C θ hd (ε/3)-ownerPotential H A C θ) -
        (baseReport Hstar θ hd (ε/3)-baseDensityPotential Hstar θ)) -
      (tangentReport Hstar (H-Hstar) θ R ε hd-realTrace (ownerCertificateDensity Hstar θ*(H-Hstar))) := by
    unfold report ownerCertificate ownerCertificateTangent
    ring
  rw [he]
  linarith


end MatrixSpencer.MSConvexCertificateReport
