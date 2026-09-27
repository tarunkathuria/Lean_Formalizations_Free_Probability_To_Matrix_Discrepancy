import MatrixSpencer.MSManuscriptNumericalAcceptance
import MatrixSpencer.MSConvexCertificateReport

/-! The original square walk with convex owner-value queries substituted.
The state, invariants, tuning constants and non-query primitives remain original. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexNumericalAcceptance
open MSManuscriptNumericalAcceptance MSManuscriptAdaptive KSOwnerInputBounds
attribute [local instance] Classical.propDecidable
variable [MSConvexOwnerValue.Oracle]
variable {N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
attribute [local irreducible] ownerPotential ownerCertificate
export MSManuscriptNumericalAcceptance (acceptReports acceptReports_iff reports_sound good_reports_accepted Config Endpoint scale tolerance scale_pos tolerance_pos psi tangent tangentReport Good roundingTangent potential initialPotential)

def psiReport (cfg : Config N d) (e : Endpoint N d) : ℝ :=
  MSConvexCertificateReport.report cfg.savedCenter e.center cfg.family e.covariance
    cfg.theta cfg.radius (tolerance cfg) cfg.dimension_pos

def accepts (cfg : Config N d) (e : Endpoint N d) : Bool :=
  acceptReports e.cleaningFailed (scale cfg) (psiReport cfg e) (tangentReport cfg e)

theorem reports_accuracy (cfg : Config N d) (e : Endpoint N d) (he : e.Valid cfg) :
    |psiReport cfg e-psi cfg e| ≤ scale cfg/100 ∧
      |tangentReport cfg e-tangent cfg e| ≤ scale cfg/100 := by
  letI : Nonempty (Fin d) := ⟨⟨0,cfg.dimension_pos⟩⟩
  have hp := MSConvexCertificateReport.report_accuracy cfg.savedCenter e.center
    cfg.savedCenter_hermitian he.1 cfg.family cfg.family_hermitian he.2.1
    cfg.theta_pos cfg.radius_nonneg (tolerance_pos cfg) cfg.dimension_pos he.2.2.2.1
  have ht := MSManuscriptCertificateReport.tangentReport_accuracy cfg.savedCenter e.movementSum
    cfg.savedCenter_hermitian he.2.2.1 cfg.theta_pos cfg.radius_nonneg
    (tolerance_pos cfg) cfg.dimension_pos he.2.2.2.2
  exact ⟨hp,ht.trans (show tolerance cfg / 3 ≤ scale cfg / 100 from by
    unfold tolerance; linarith [(scale_pos cfg).le])⟩



theorem accepts_sound (cfg : Config N d) (e : Endpoint N d) (he : e.Valid cfg)
    (ha : accepts cfg e = true) :
    e.cleaningFailed = false ∧ psi cfg e ≤ (1651/100:ℝ)*scale cfg ∧
      tangent cfg e ≤ (451/100:ℝ)*scale cfg :=
  reports_sound (reports_accuracy cfg e he).1 (reports_accuracy cfg e he).2 ha

theorem good_accepted (cfg : Config N d) (e : Endpoint N d) (he : e.Valid cfg)
    (hg : Good cfg e) : accepts cfg e = true :=
  good_reports_accepted (scale_pos cfg).le (reports_accuracy cfg e he).1
    (reports_accuracy cfg e he).2 hg.1 hg.2.1 hg.2.2

/-- The remaining center displacement after subtracting centered movements.
This term includes the numerical epoch's cleaning and snapping increments. -/

theorem accepted_potential_increment (cfg : Config N d) (e : Endpoint N d)
    (he : e.Valid cfg) (ha : accepts cfg e = true)
    (hround : roundingTangent cfg e ≤ scale cfg/100) :
    potential cfg e-initialPotential cfg < 25*scale cfg := by
  letI : Nonempty (Fin d) := ⟨⟨0,cfg.dimension_pos⟩⟩
  obtain ⟨_,hp,ht⟩ := accepts_sound cfg e he ha
  have hid := ownerCertificate_terminal_identity cfg.savedCenter e.center
    cfg.family cfg.theta 1 e.covariance
  have hzero := ownerCertificate_nonneg cfg.savedCenter cfg.savedCenter
    cfg.family cfg.family_hermitian (Matrix.PosSemidef.one :
      (1 : Matrix (Fin N) (Fin N) ℝ).PosSemidef) cfg.theta
  have hsplit : ownerCertificateTangent cfg.savedCenter cfg.theta e.center =
      tangent cfg e + roundingTangent cfg e := by
    simp only [ownerCertificateTangent, tangent, roundingTangent,
      Matrix.mul_sub, realTrace_sub]
    ring
  rw [hsplit] at hid
  change 0 ≤ psi cfg { e with center := cfg.savedCenter, covariance := 1 } at hzero
  change potential cfg e-initialPotential cfg = psi cfg e -
    psi cfg { e with center := cfg.savedCenter, covariance := 1 } +
      (tangent cfg e+roundingTangent cfg e) at hid
  linarith [scale_pos cfg]

/-- Literal first-accepted numerical endpoint. The input sampler is the
actual numerical epoch sampler supplied by the epoch construction. -/

def output (cfg : Config N d) (P : Sampler (Endpoint N d)) (r : ℕ) : Sampler (Option (Endpoint N d)) :=
  MSManuscriptAcceptanceRetry.output P (accepts cfg) r

theorem output_sound (cfg : Config N d) (P : Sampler (Endpoint N d))
    (hvalid : ∀ z : P.Draws, (P.value z).Valid cfg) (r : ℕ)
    (z : (output cfg P r).Draws) (e : Endpoint N d) (ho : (output cfg P r).value z = some e) :
    e.cleaningFailed = false ∧ psi cfg e ≤ (1651/100:ℝ)*scale cfg ∧
      tangent cfg e ≤ (451/100:ℝ)*scale cfg :=
  MSManuscriptAcceptanceRetry.output_sound P (accepts cfg)
    (fun e => e.cleaningFailed = false ∧ psi cfg e ≤ (1651/100:ℝ)*scale cfg ∧
      tangent cfg e ≤ (451/100:ℝ)*scale cfg)
    (fun z hz => accepts_sound cfg (P.value z) (hvalid z) hz) r z e ho

/-- The actual epoch good-event probability is the remaining explicit
premise; numerical report accuracy is already discharged. -/

theorem output_event_probability_ge (cfg : Config N d) (P : Sampler (Endpoint N d))
    (hvalid : ∀ z : P.Draws, (P.value z).Valid cfg) {p : ℝ}
    (hgood : p ≤ P.expectation (fun e => if Good cfg e then 1 else 0)) (r : ℕ) :
    1-(1-p)^r ≤ ∑ z : (output cfg P r).Draws, (output cfg P r).weight z *
      (if ((output cfg P r).value z).isSome then 1 else 0) := by
  apply MSManuscriptAcceptanceRetry.output_event_probability_ge
  exact MSManuscriptAcceptanceRetry.acceptance_probability_ge P (accepts cfg) (Good cfg)
    hgood (fun z hg => good_accepted cfg (P.value z) (hvalid z) hg)

end MatrixSpencer.MSConvexNumericalAcceptance
