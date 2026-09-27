import MatrixSpencer.MSManuscriptAcceptedEpoch
import FaithfulMS.SquareDirectEpochSuccess
import FaithfulMS.SquareDirectAcceptance

/-! The direct-density square walk. Optimizing densities give the covariance
response and supporting plane; all walk invariants are proved for this concrete update. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
open MatrixSpencer
namespace FaithfulMS.SquareDirectAcceptedEpoch
open MSManuscriptAcceptedEpoch MSManuscriptAdaptive MSManuscriptNumericalConfig
attribute [local instance] Classical.propDecidable
variable [SquareDirectOracle.Oracle]
variable {N d : ℕ} [Nonempty (Fin d)]
variable (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d)
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
attribute [local irreducible] ownerPotential ownerCertificate
export MSManuscriptAcceptedEpoch (reportConfig endpoint rounding_le centered_le endpoint_valid psi_eq tangent_eq GoodEndpoint)

theorem good_probability :
    (499/800:ℝ)≤(SquareDirectEpochRun.output (ofEpochConfig cfg hd)).expectation
      (fun s=>if MSManuscriptNumericalAcceptance.Good (reportConfig cfg hd) (endpoint cfg hd s) then 1 else 0) := by
  have hm:=SquareDirectEpochSuccess.all_moments cfg hd
  have hh:=MSManuscriptAcceptanceMoments.good_probability_ge (SquareDirectEpochRun.output (ofEpochConfig cfg hd))
    (fun s=>(endpoint cfg hd s).cleaningFailed)
    (fun s=>MSManuscriptNumericalAcceptance.psi (reportConfig cfg hd) (endpoint cfg hd s))
    (fun s=>MSManuscriptNumericalAcceptance.tangent (reportConfig cfg hd) (endpoint cfg hd s))
    (s:=Real.sqrt (N:ℝ)) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (count_pos cfg)))
    (fun z=>by
      change 0≤MSManuscriptNumericalAcceptance.psi (reportConfig cfg hd)
        (endpoint cfg hd ((SquareDirectEpochRun.output (ofEpochConfig cfg hd)).value z))
      rw [psi_eq cfg hd]
      exact MSManuscriptNumericalEpochMoments.energy_nonneg _ _)
    (by simpa only [endpoint,decide_eq_true_eq] using hm.1)
    (by simpa only [psi_eq] using hm.2.1)
    (by simpa only [tangent_eq] using hm.2.2)
  convert hh using 1
  congr 1
  funext s
  simp only [MSManuscriptNumericalAcceptance.Good,MSManuscriptNumericalAcceptance.scale,reportConfig]
  split_ifs <;> rfl

def accepts (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) : Bool :=
  SquareDirectAcceptance.accepts (reportConfig cfg hd) (endpoint cfg hd s)

def output (r : ℕ) : Sampler (Option (MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd))) :=
  MSManuscriptAcceptanceRetry.output (SquareDirectEpochRun.output (ofEpochConfig cfg hd)) (accepts cfg hd) r

theorem acceptance_probability : (499/800:ℝ)≤MSManuscriptAcceptanceRetry.acceptanceProbability
    (SquareDirectEpochRun.output (ofEpochConfig cfg hd)) (accepts cfg hd) :=
  MSManuscriptAcceptanceRetry.acceptance_probability_ge _ _
    (fun s=>MSManuscriptNumericalAcceptance.Good (reportConfig cfg hd) (endpoint cfg hd s)) (good_probability cfg hd)
    (fun _ hz=>SquareDirectAcceptance.good_accepted _ _ (endpoint_valid cfg hd _) hz)

theorem output_failure_le (r : ℕ) : (output cfg hd r).expectation failure≤(301/800:ℝ)^r := by
  have hh:=MSManuscriptAcceptanceRetry.output_failure_le _ _ (acceptance_probability cfg hd) r
  norm_num only [show (1:ℝ)-499/800=301/800 by norm_num] at hh
  exact hh

theorem output_event_probability_ge (r : ℕ) :
    1-(301/800:ℝ)^r≤∑z:(output cfg hd r).Draws,(output cfg hd r).weight z*
      (if ((output cfg hd r).value z).isSome then 1 else 0) := by
  have hf:=output_failure_le cfg hd r
  have ht:=success_add_failure (output cfg hd r)
  change 1-(301/800:ℝ)^r≤(output cfg hd r).expectation success
  linarith

theorem accepted_draw (z : (SquareDirectEpochRun.output (ofEpochConfig cfg hd)).Draws)
    (ha : accepts cfg hd ((SquareDirectEpochRun.output (ofEpochConfig cfg hd)).value z)=true) :
    GoodEndpoint cfg hd ((SquareDirectEpochRun.output (ofEpochConfig cfg hd)).value z) := by
  let s:MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd):=(SquareDirectEpochRun.output (ofEpochConfig cfg hd)).value z
  have hav:=SquareDirectAcceptance.accepts_sound _ _ (endpoint_valid cfg hd s) ha
  have hp : s.val.paid+s.val.dust≤(N:ℝ)/64 := by
    have hh:=hav.1
    change decide ((N:ℝ)/64<s.val.paid+s.val.dust)=false at hh
    simpa only [decide_eq_false_iff_not,not_lt] using hh
  have hr:=MSManuscriptInputRadius.rounding_tangent_le (reportConfig cfg hd) (endpoint cfg hd s) cfg.offset
    (WithLp.ofLp s.val.point) (WithLp.ofLp cfg.start) (WithLp.ofLp s.val.centered)
    (centered_le cfg hd s) cfg.contractions
    (epochCenter_coe cfg.offset cfg.matrices cfg.hermitian cfg.start)
    (epochCenter_coe cfg.offset cfg.matrices cfg.hermitian s.val.point) rfl
  have hrb : MSManuscriptNumericalAcceptance.roundingTangent (reportConfig cfg hd) (endpoint cfg hd s)≤MSManuscriptNumericalAcceptance.scale (reportConfig cfg hd)/100 :=
    (le_abs_self _).trans (hr.trans (rounding_budget cfg hd))
  have hg:=SquareDirectAcceptance.accepted_potential_increment _ _ (endpoint_valid cfg hd s) ha hrb
  have hreset:=ownerPotential_le_base_add (cfg.center s.val.point) cfg.matrices cfg.hermitian
    cfg.contractions (Matrix.PosSemidef.one : (1:Matrix (Fin N) (Fin N) ℝ).PosSemidef) le_rfl (1:ℝ)
  have hbase:=baseDensityPotential_le_owner (cfg.center s.val.point) cfg.matrices cfg.hermitian
    (s.property.1.owner_valid.physical_posSemidef _ (ofEpochConfig cfg hd).floor_pos.le) (1:ℝ)
  refine ⟨SquareDirectEpochRun.output_time_or_freezing _ z hp,?_⟩
  change ownerPotential (cfg.center s.val.point) cfg.matrices s.val.owner.physical 1-
    ownerPotential cfg.anchor cfg.matrices 1 1<25*Real.sqrt (N:ℝ) at hg
  simp only [Fintype.card_fin] at hreset
  change ownerPotential (cfg.center s.val.point) cfg.matrices 1 1≤_
  linarith

theorem output_sound (r : ℕ) (z : (output cfg hd r).Draws)
    (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) (ho : (output cfg hd r).value z=some s) : GoodEndpoint cfg hd s :=
  MSManuscriptAcceptanceRetry.output_sound _ _ (GoodEndpoint cfg hd) (accepted_draw cfg hd) r z s ho

end FaithfulMS.SquareDirectAcceptedEpoch
