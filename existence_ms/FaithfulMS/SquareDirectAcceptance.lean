import MatrixSpencer.MSManuscriptNumericalAcceptance
import FaithfulMS.SquareDirectOracle

/-! The direct-density square walk. Optimizing densities give the covariance
response and supporting plane; all walk invariants are proved for this concrete update. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
open MatrixSpencer
namespace FaithfulMS.SquareDirectAcceptance
open MSManuscriptNumericalAcceptance MSManuscriptAdaptive KSOwnerInputBounds
attribute [local instance] Classical.propDecidable
variable [SquareDirectOracle.Oracle]
variable {N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
attribute [local irreducible] ownerPotential ownerCertificate
export MSManuscriptNumericalAcceptance (acceptReports acceptReports_iff reports_sound good_reports_accepted Config Endpoint scale tolerance scale_pos tolerance_pos psi tangent Good roundingTangent potential initialPotential)

def savedSolution (cfg : Config N d) :
    DirectDensity.SquareSolution cfg.savedCenter
      (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ)) 0 cfg.theta :=
  SquareDirectOracle.Oracle.service.squareSolution cfg.savedCenter _
    (fun i => i.elim) 0 Matrix.PosSemidef.zero cfg.dimension_pos cfg.theta cfg.theta_pos

def savedDensity (cfg : Config N d) : Matrix (Fin d) (Fin d) ℂ :=
  (savedSolution cfg).density

def savedValue (cfg : Config N d) : ℝ :=
  ownerObjective cfg.savedCenter (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ))
    0 cfg.theta (savedDensity cfg)

def endpointValue (cfg : Config N d) (e : Endpoint N d) : ℝ :=
  if hC : e.covariance.PosSemidef then
    ownerObjective e.center cfg.family e.covariance cfg.theta
      (SquareDirectOracle.Oracle.service.squareSolution e.center cfg.family
        cfg.family_hermitian e.covariance hC cfg.dimension_pos cfg.theta cfg.theta_pos).density
  else 0

def psiReport (cfg : Config N d) (e : Endpoint N d) : ℝ :=
  endpointValue cfg e - savedValue cfg -
    realTrace (savedDensity cfg * (e.center-cfg.savedCenter))

def tangentReport (cfg : Config N d) (e : Endpoint N d) : ℝ :=
  realTrace (savedDensity cfg * e.movementSum)

def accepts (cfg : Config N d) (e : Endpoint N d) : Bool :=
  acceptReports e.cleaningFailed (scale cfg) (psiReport cfg e) (tangentReport cfg e)

theorem savedDensity_eq (cfg : Config N d) [Nonempty (Fin d)] :
    savedDensity cfg = ownerCertificateDensity cfg.savedCenter cfg.theta :=
  (savedSolution cfg).saved_density_eq cfg.theta_pos

theorem savedValue_eq (cfg : Config N d) [Nonempty (Fin d)] :
    savedValue cfg = baseDensityPotential cfg.savedCenter cfg.theta := by
  rw [savedValue, savedDensity,
    (savedSolution cfg).owner_value_eq (fun i => i.elim) Matrix.PosSemidef.zero]
  exact MSManuscriptCertificateReport.empty_owner_eq_base _ _

theorem endpointValue_eq (cfg : Config N d) (e : Endpoint N d)
    (he : e.Valid cfg) [Nonempty (Fin d)] :
    endpointValue cfg e = ownerPotential e.center cfg.family e.covariance cfg.theta := by
  rw [endpointValue, dif_pos he.2.1]
  exact DirectDensity.SquareSolution.owner_value_eq _ cfg.family_hermitian he.2.1

theorem reports_exact (cfg : Config N d) (e : Endpoint N d) (he : e.Valid cfg) :
    psiReport cfg e = psi cfg e ∧ tangentReport cfg e = tangent cfg e := by
  letI : Nonempty (Fin d) := ⟨⟨0,cfg.dimension_pos⟩⟩
  constructor
  · simp only [psiReport, endpointValue_eq cfg e he, savedValue_eq, savedDensity_eq,
      psi, ownerCertificate, ownerCertificateTangent]
  · simp only [tangentReport, savedDensity_eq, tangent]

theorem reports_accuracy (cfg : Config N d) (e : Endpoint N d) (he : e.Valid cfg) :
    |psiReport cfg e-psi cfg e| ≤ scale cfg/100 ∧
      |tangentReport cfg e-tangent cfg e| ≤ scale cfg/100 := by
  simp only [(reports_exact cfg e he).1, (reports_exact cfg e he).2, sub_self, abs_zero, and_self]
  exact div_nonneg (scale_pos cfg).le (by norm_num)



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

end FaithfulMS.SquareDirectAcceptance
