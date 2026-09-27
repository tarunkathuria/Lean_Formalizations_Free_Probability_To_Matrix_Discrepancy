import MatrixSpencer.MSManuscriptPolynomialQueryAcceptance
import MatrixSpencer.MSConvexAnchorTangent

/-! Primitive-input precision bounds for the two real, source-free convex
queries used to evaluate the saved supporting plane. -/
noncomputable section
namespace MatrixSpencer.MSConvexPolynomialTangentParameters
open MSManuscriptPolynomialQueryParameters MSManuscriptPolynomialQueryAcceptance

def spacingInv (N d : ℕ) : ℕ := 600*(2*(acceptanceRadius N d)^2+1)
def precisionInv (N d : ℕ) : ℕ := 360000*(2*(acceptanceRadius N d)^2+1)

theorem inverse_formulas (R ε : ℝ) :
    (MSConvexAnchorTangent.spacing 1 R ε)⁻¹=6*(2*R^2+1)*ε⁻¹ ∧
    (MSConvexAnchorTangent.precision 1 R ε)⁻¹=36*(2*R^2+1)*(ε⁻¹)^2 := by
  simp only [MSConvexAnchorTangent.spacing,MSConvexAnchorTangent.precision,
    MSConvexAnchorTangent.curvature,div_one,inv_div,_root_.mul_inv_rev,div_eq_mul_inv,inv_inv]
  constructor <;> ring

theorem scalar_inverse_bounds {R ε B : ℝ} (hR : 0≤R) (hRB : R≤B)
    (hε : 0<ε) (hεi : ε⁻¹≤100) :
    (MSConvexAnchorTangent.spacing 1 R ε)⁻¹≤600*(2*B^2+1) ∧
    (MSConvexAnchorTangent.precision 1 R ε)⁻¹≤360000*(2*B^2+1) := by
  rw [(inverse_formulas R ε).1,(inverse_formulas R ε).2]
  have hs : R^2≤B^2 := (sq_le_sq₀ hR (hR.trans hRB)).mpr hRB
  have he : 0≤ε⁻¹ := (inv_pos.mpr hε).le
  have hsq : (ε⁻¹)^2≤10000 := by nlinarith
  constructor
  · have h := mul_le_mul (show 6*(2*R^2+1)≤6*(2*B^2+1) by linarith) hεi he (by positivity)
    nlinarith
  · have h := mul_le_mul (show 36*(2*R^2+1)≤36*(2*B^2+1) by linarith) hsq (sq_nonneg _) (by positivity)
    nlinarith

theorem actual_inverse_bounds {m N d : ℕ} (cfg : EpochConfig (Fin m) (Fin d))
    (hd : 0<d) (hm : m≤N) :
    (MSConvexAnchorTangent.spacing 1
      (MSManuscriptAcceptedEpoch.reportConfig cfg hd).radius
      (MSManuscriptNumericalAcceptance.tolerance (MSManuscriptAcceptedEpoch.reportConfig cfg hd)))⁻¹≤spacingInv N d ∧
    (MSConvexAnchorTangent.precision 1
      (MSManuscriptAcceptedEpoch.reportConfig cfg hd).radius
      (MSManuscriptNumericalAcceptance.tolerance (MSManuscriptAcceptedEpoch.reportConfig cfg hd)))⁻¹≤precisionInv N d := by
  have hr : 0≤(MSManuscriptAcceptedEpoch.reportConfig cfg hd).radius := by
    unfold MSManuscriptAcceptedEpoch.reportConfig MSManuscriptInputRadius.radius
    have he := cfg.epsilon_pos.le
    positivity
  have h := scalar_inverse_bounds hr (radius_le cfg hd hm)
    (MSManuscriptNumericalAcceptance.tolerance_pos _) (tolerance_inverse_le cfg hd)
  simpa only [spacingInv,precisionInv,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,
    Nat.cast_ofNat,Nat.cast_one] using h

end MatrixSpencer.MSConvexPolynomialTangentParameters
