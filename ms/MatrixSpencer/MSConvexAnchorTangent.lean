import MatrixSpencer.MSConvexCertificateReport
import MatrixSpencer.KSOptimizerInverseBound
import MatrixSpencer.KSGradientQueryGeometry
import MatrixSpencer.KSFirstDifference

/-! The fixed supporting plane is evaluated by two source-free convex-value
queries along a real line through its saved center. The uniform Hessian bound
and the actual Taylor remainder are proved, so no primal optimizer is required
from the value-only solver. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexAnchorTangent
open MSManuscriptAnchorDensity KSOwnerInputBounds KSGradientQueryGeometry
variable {d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

abbrev SA (d : ℕ) := selfAdjoint (Matrix (Fin d) (Fin d) ℂ)

def curvature (θ R : ℝ) : ℝ := (2/θ)*R^2

def spacing (θ R ε : ℝ) : ℝ := ε/(6*(curvature θ R+1))

def precision (θ R ε : ℝ) : ℝ := ε*spacing θ R ε/6

theorem curvature_nonneg {θ R : ℝ} (hθ : 0<θ) : 0≤curvature θ R := by
  unfold curvature
  positivity

theorem spacing_pos {θ R ε : ℝ} (hθ : 0<θ) (hε : 0<ε) : 0<spacing θ R ε := by
  unfold spacing
  have hc := curvature_nonneg (R:=R) hθ
  positivity

theorem precision_pos {θ R ε : ℝ} (hθ : 0<θ) (hε : 0<ε) : 0<precision θ R ε := by
  unfold precision
  have hs := spacing_pos (R:=R) hθ hε
  positivity

theorem curvature_bound [Nonempty (Fin d)] (H D : SA d) {θ R : ℝ}
    (hθ : 0<θ) (hR : 0≤R) (hD : Real.sqrt (matrixEnergy (D : Matrix (Fin d) (Fin d) ℂ))≤R) :
    |fderiv ℝ (fderiv ℝ (hermitianDensityPotential (emptyFamily (d:=d)) θ)) H D D|≤
      curvature θ R := by
  rw [fderiv_fderiv_hermitianDensityPotential_apply_source_unrestricted H D D emptyFamily hθ]
  let U := densityResponseDerivative_source_unrestricted (H : Matrix (Fin d) (Fin d) ℂ)
    emptyFamily θ hθ (hermitianDensityOptimizer (H : Matrix (Fin d) (Fin d) ℂ) emptyFamily θ)
    (hermitianDensityOptimizer_posDef (H : Matrix (Fin d) (Fin d) ℂ) emptyFamily hθ) D
  have hp := KSOptimizerInverseBound.trace_pairing_le_frobenius U D
  have hu := KSOptimizerInverseBound.response_frobenius_le (H : Matrix (Fin d) (Fin d) ℂ) emptyFamily θ hθ
    (hermitianDensityOptimizer (H : Matrix (Fin d) (Fin d) ℂ) emptyFamily θ)
    (hermitianDensityOptimizer_posDef (H : Matrix (Fin d) (Fin d) ℂ) emptyFamily hθ)
    (hermitianDensityOptimizer_trace (H : Matrix (Fin d) (Fin d) ℂ) emptyFamily θ) D
  change Real.sqrt (realTrace ((U : Matrix (Fin d) (Fin d) ℂ)*(U : Matrix (Fin d) (Fin d) ℂ)))≤_ at hu
  have hd' : Real.sqrt (realTrace ((D : Matrix (Fin d) (Fin d) ℂ)*(D : Matrix (Fin d) (Fin d) ℂ)))≤R := by
    rwa [← matrixEnergy_eq_trace_square _ D.property]
  have hx := Real.sqrt_nonneg (realTrace ((D : Matrix (Fin d) (Fin d) ℂ)*(D : Matrix (Fin d) (Fin d) ℂ)))
  have hsq : (Real.sqrt (realTrace ((D : Matrix (Fin d) (Fin d) ℂ)*(D : Matrix (Fin d) (Fin d) ℂ))))^2≤R^2 := by
    nlinarith
  exact hp.trans ((mul_le_mul_of_nonneg_right hu hx).trans (by
    dsimp only [curvature]
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0≤2/θ by positivity)]))

theorem line_contDiff [Nonempty (Fin d)] (H D : SA d) {θ : ℝ} (hθ : 0<θ) :
    ContDiff ℝ 2 (fun t:ℝ => baseDensityPotential ((H+t•D : SA d) : Matrix (Fin d) (Fin d) ℂ) θ) := by
  have hf : ContDiff ℝ 2 (hermitianDensityPotential (emptyFamily (d:=d)) θ) :=
    (contDiff_hermitianDensityPotential_source_unrestricted (emptyFamily (d:=d)) hθ).of_le (WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))
  exact hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))

theorem line_deriv [Nonempty (Fin d)] (H D : SA d) {θ : ℝ} (hθ : 0<θ) :
    deriv (fun t:ℝ => baseDensityPotential ((H+t•D : SA d) : Matrix (Fin d) (Fin d) ℂ) θ) 0 =
      realTrace (ownerCertificateDensity H θ * (D : Matrix (Fin d) (Fin d) ℂ)) := by
  change deriv (fun t:ℝ => hermitianDensityPotential emptyFamily θ (H+t•D)) 0 = _
  rw [deriv_affine_comp]
  · simp only [zero_smul,add_zero]
    rw [(hasFDerivAt_hermitianDensityPotential_source_unrestricted H emptyFamily hθ).fderiv]
    rfl
  · exact (hasFDerivAt_hermitianDensityPotential_source_unrestricted _ emptyFamily hθ).differentiableAt

theorem line_second_bound [Nonempty (Fin d)] (H D : SA d) {θ R : ℝ}
    (hθ : 0<θ) (hR : 0≤R) (hD : Real.sqrt (matrixEnergy (D : Matrix (Fin d) (Fin d) ℂ))≤R)
    (u : ℝ) :
    |iteratedDeriv 2 (fun t:ℝ => baseDensityPotential ((H+t•D : SA d) : Matrix (Fin d) (Fin d) ℂ) θ) u|≤
      curvature θ R := by
  change |iteratedDeriv 2 (fun t:ℝ => hermitianDensityPotential emptyFamily θ (H+t•D)) u|≤_
  rw [iteratedDeriv_two_affine_comp]
  · exact curvature_bound (H+u•D) D hθ hR hD
  · exact (show ContDiffAt ℝ 2 (hermitianDensityPotential (emptyFamily (d:=d)) θ) (H+u•D) from
      (contDiffAt_hermitianDensityPotential_source_unrestricted (H+u•D) emptyFamily hθ).of_le (WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top)))

variable [MSConvexOwnerValue.Oracle]

def tangentReport (Hstar D : Matrix (Fin d) (Fin d) ℂ) (θ R ε : ℝ) (hd : 0<d) : ℝ :=
  KSFirstDifference.sampleSlope
    (MSConvexCertificateReport.baseReport (Hstar+spacing θ R ε•D) θ hd (precision θ R ε))
    (MSConvexCertificateReport.baseReport (Hstar-spacing θ R ε•D) θ hd (precision θ R ε))
    (spacing θ R ε)

theorem tangentReport_accuracy [Nonempty (Fin d)]
    (Hstar D : Matrix (Fin d) (Fin d) ℂ) (hHstar : Hstar.IsHermitian) (hD : D.IsHermitian)
    {θ R ε : ℝ} (hθ : 0<θ) (hR : 0≤R) (hε : 0<ε) (hd : 0<d)
    (hDnorm : Real.sqrt (matrixEnergy D)≤R) :
    |tangentReport Hstar D θ R ε hd - realTrace (ownerCertificateDensity Hstar θ*D)|≤ε/3 := by
  let H : SA d := ⟨Hstar,hHstar⟩
  let V : SA d := ⟨D,hD⟩
  let f : SA d → ℝ := fun K=>baseDensityPotential (K : Matrix (Fin d) (Fin d) ℂ) θ
  let r : SA d → ℝ := fun K=>MSConvexCertificateReport.baseReport (K : Matrix (Fin d) (Fin d) ℂ) θ hd (precision θ R ε)
  have hp := MSConvexCertificateReport.baseReport_accuracy
    (Hstar+spacing θ R ε•D) (H+spacing θ R ε•V).property hθ (precision_pos (R:=R) hθ hε) hd
  have hm := MSConvexCertificateReport.baseReport_accuracy
    (Hstar-spacing θ R ε•D) (H-spacing θ R ε•V).property hθ (precision_pos (R:=R) hθ hε) hd
  have hb := KSFirstDifference.directionalStencil_error f r H V (spacing_pos (R:=R) hθ hε)
    (line_contDiff H V hθ).contDiffOn
    (fun u _=>line_second_bound H V hθ hR hDnorm u) hp hm
  rw [line_deriv H V hθ] at hb
  change |tangentReport Hstar D θ R ε hd-realTrace (ownerCertificateDensity Hstar θ*D)|≤_ at hb
  apply hb.trans
  have hc := curvature_nonneg (R:=R) hθ
  have hs := spacing_pos (R:=R) hθ hε
  have he : precision θ R ε/spacing θ R ε=ε/6 := by
    unfold precision
    field_simp
  rw [he]
  have ht : curvature θ R*spacing θ R ε≤ε/3 := by
    unfold spacing
    rw [← mul_div_assoc,div_le_iff₀ (by positivity : 0<6*(curvature θ R+1))]
    nlinarith
  linarith

end MatrixSpencer.MSConvexAnchorTangent
