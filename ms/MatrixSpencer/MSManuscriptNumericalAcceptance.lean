import MatrixSpencer.MSManuscriptCertificateReport
import MatrixSpencer.MSManuscriptAcceptanceRetry



open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalAcceptance

open MSManuscriptAdaptive KSOwnerInputBounds
attribute [local instance] Classical.propDecidable
variable {N d : ℕ}


def acceptReports (cleaningFailed : Bool) (scale psiHat tangentHat : ℝ) : Bool :=
  !cleaningFailed && decide (psiHat ≤ (33/2:ℝ)*scale) && decide (tangentHat ≤ (9/2:ℝ)*scale)

theorem acceptReports_iff (failed : Bool) (scale psiHat tangentHat : ℝ) :
    acceptReports failed scale psiHat tangentHat = true ↔
      failed = false ∧ psiHat ≤ (33/2:ℝ)*scale ∧ tangentHat ≤ (9/2:ℝ)*scale := by
  simp [acceptReports, and_assoc]

theorem reports_sound {failed : Bool} {scale psi tangent psiHat tangentHat : ℝ}
    (hpsi : |psiHat-psi| ≤ scale/100) (htangent : |tangentHat-tangent| ≤ scale/100)
    (ha : acceptReports failed scale psiHat tangentHat = true) :
    failed = false ∧ psi ≤ (1651/100:ℝ)*scale ∧ tangent ≤ (451/100:ℝ)*scale := by
  obtain ⟨hf,hp,ht⟩ := (acceptReports_iff _ _ _ _).mp ha
  exact ⟨hf,by linarith [(abs_le.mp hpsi).1],by linarith [(abs_le.mp htangent).1]⟩

theorem good_reports_accepted {failed : Bool} {scale psi tangent psiHat tangentHat : ℝ}
    (hscale : 0 ≤ scale) (hpsi : |psiHat-psi| ≤ scale/100)
    (htangent : |tangentHat-tangent| ≤ scale/100)
    (hf : failed = false) (hp : psi ≤ 16*scale) (ht : tangent ≤ 4*scale) :
    acceptReports failed scale psiHat tangentHat = true := by
  apply (acceptReports_iff _ _ _ _).mpr
  exact ⟨hf,by linarith [(abs_le.mp hpsi).2],by linarith [(abs_le.mp htangent).2]⟩

/-- Fixed data for one saved epoch. The radius is fixed for all its trials,
so both reported certificates use the same computed anchor density. -/
structure Config (N d : ℕ) where
  savedCenter : Matrix (Fin d) (Fin d) ℂ
  family : Fin N → Matrix (Fin d) (Fin d) ℂ
  theta : ℝ
  radius : ℝ
  count : ℕ
  dimension_pos : 0 < d
  count_pos : 0 < count
  theta_pos : 0 < theta
  radius_nonneg : 0 ≤ radius
  savedCenter_hermitian : savedCenter.IsHermitian
  family_hermitian : ∀ i, (family i).IsHermitian

structure Endpoint (N d : ℕ) where
  center : Matrix (Fin d) (Fin d) ℂ
  covariance : Matrix (Fin N) (Fin N) ℝ
  movementSum : Matrix (Fin d) (Fin d) ℂ
  cleaningFailed : Bool

/-- `movementSum` is the physical sum of centered movements only. The
numerical epoch supplies the relation to its accumulated sampling history. -/
def Endpoint.Valid (cfg : Config N d) (e : Endpoint N d) : Prop :=
  e.center.IsHermitian ∧ e.covariance.PosSemidef ∧ e.movementSum.IsHermitian ∧
  Real.sqrt (matrixEnergy (e.center-cfg.savedCenter)) ≤ cfg.radius ∧
  Real.sqrt (matrixEnergy e.movementSum) ≤ cfg.radius

def scale (cfg : Config N d) : ℝ := Real.sqrt (cfg.count:ℝ)
def tolerance (cfg : Config N d) : ℝ := scale cfg / 100

theorem scale_pos (cfg : Config N d) : 0 < scale cfg := Real.sqrt_pos.mpr (Nat.cast_pos.mpr cfg.count_pos)
theorem tolerance_pos (cfg : Config N d) : 0 < tolerance cfg := div_pos (scale_pos cfg) (by norm_num)

def psi (cfg : Config N d) (e : Endpoint N d) : ℝ := by
  letI : Nonempty (Fin d) := ⟨⟨0,cfg.dimension_pos⟩⟩
  exact ownerCertificate cfg.savedCenter cfg.family cfg.theta e.center e.covariance

def tangent (cfg : Config N d) (e : Endpoint N d) : ℝ := by
  letI : Nonempty (Fin d) := ⟨⟨0,cfg.dimension_pos⟩⟩
  exact realTrace (ownerCertificateDensity cfg.savedCenter cfg.theta * e.movementSum)

/-- Finite optimized-value and saved-density reports, with the fixed radius. -/
def psiReport (cfg : Config N d) (e : Endpoint N d) : ℝ :=
  MSManuscriptCertificateReport.report cfg.savedCenter e.center cfg.family e.covariance
    cfg.theta cfg.radius (tolerance cfg) cfg.dimension_pos

def tangentReport (cfg : Config N d) (e : Endpoint N d) : ℝ :=
  MSManuscriptCertificateReport.tangentReport cfg.savedCenter e.movementSum
    cfg.theta cfg.radius (tolerance cfg) cfg.dimension_pos

def accepts (cfg : Config N d) (e : Endpoint N d) : Bool :=
  acceptReports e.cleaningFailed (scale cfg) (psiReport cfg e) (tangentReport cfg e)

theorem reports_accuracy (cfg : Config N d) (e : Endpoint N d) (he : e.Valid cfg) :
    |psiReport cfg e-psi cfg e| ≤ scale cfg/100 ∧
      |tangentReport cfg e-tangent cfg e| ≤ scale cfg/100 := by
  letI : Nonempty (Fin d) := ⟨⟨0,cfg.dimension_pos⟩⟩
  have hp := MSManuscriptCertificateReport.report_accuracy cfg.savedCenter e.center
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

def Good (cfg : Config N d) (e : Endpoint N d) : Prop :=
  e.cleaningFailed = false ∧ psi cfg e ≤ 16*scale cfg ∧ tangent cfg e ≤ 4*scale cfg

theorem good_accepted (cfg : Config N d) (e : Endpoint N d) (he : e.Valid cfg)
    (hg : Good cfg e) : accepts cfg e = true :=
  good_reports_accepted (scale_pos cfg).le (reports_accuracy cfg e he).1
    (reports_accuracy cfg e he).2 hg.1 hg.2.1 hg.2.2

/-- The remaining center displacement after subtracting centered movements.
This term includes the numerical epoch's cleaning and snapping increments. -/
def roundingTangent (cfg : Config N d) (e : Endpoint N d) : ℝ := by
  letI : Nonempty (Fin d) := ⟨⟨0,cfg.dimension_pos⟩⟩
  exact realTrace (ownerCertificateDensity cfg.savedCenter cfg.theta *
    (e.center-cfg.savedCenter-e.movementSum))

def potential (cfg : Config N d) (e : Endpoint N d) : ℝ := by
  letI : Nonempty (Fin d) := ⟨⟨0,cfg.dimension_pos⟩⟩
  exact ownerPotential e.center cfg.family e.covariance cfg.theta

def initialPotential (cfg : Config N d) : ℝ := by
  letI : Nonempty (Fin d) := ⟨⟨0,cfg.dimension_pos⟩⟩
  exact ownerPotential cfg.savedCenter cfg.family 1 cfg.theta


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

end MatrixSpencer.MSManuscriptNumericalAcceptance
