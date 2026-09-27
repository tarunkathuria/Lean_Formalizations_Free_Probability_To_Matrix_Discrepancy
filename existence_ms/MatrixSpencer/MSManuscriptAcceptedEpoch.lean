import MatrixSpencer.MSManuscriptNumericalEpochSuccess
import MatrixSpencer.MSManuscriptAcceptanceMoments
import MatrixSpencer.MSManuscriptInputRadius

/-! The literal numerical two-test filter and finite retries applied to the
proved numerical epoch. Returned states retain their actual coordinates and
ledgers; all accuracy, moment and success premises are discharged internally. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptAcceptedEpoch
open MSManuscriptAdaptive MSManuscriptNumericalConfig
variable {N d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1400000
attribute [local irreducible] ownerPotential ownerCertificate

variable (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d)

def reportConfig : MSManuscriptNumericalAcceptance.Config N d where
  savedCenter:=cfg.anchor
  family:=cfg.matrices
  theta:=1
  radius:=MSManuscriptInputRadius.radius N d (cfg.epsilon*N)
  count:=N
  dimension_pos:=hd
  count_pos:=count_pos cfg
  theta_pos:=by norm_num
  radius_nonneg:=MSManuscriptInputRadius.radius_nonneg (mul_nonneg cfg.epsilon_pos.le (Nat.cast_nonneg N))
  savedCenter_hermitian:=(cfg.center cfg.start).property
  family_hermitian:=cfg.hermitian

def endpoint (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) : MSManuscriptNumericalAcceptance.Endpoint N d where
  center:=cfg.center s.val.point
  covariance:=s.val.owner.physical
  movementSum:=MSManuscriptInputRadius.combination cfg.matrices (WithLp.ofLp s.val.centered)
  cleaningFailed:=decide ((N:ℝ)/64<s.val.paid+s.val.dust)

omit [Nonempty (Fin d)] in
theorem rounding_le (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) : s.val.rounding≤cfg.epsilon*N := by
  exact s.property.1.rounding_le.trans (mul_le_mul_of_nonneg_left
    (by simpa only [Fintype.card_fin] using (Nat.cast_le.mpr (Finset.card_le_univ (frozenCoordinates s.val.point)) :
      ((frozenCoordinates s.val.point).card:ℝ)≤Fintype.card (Fin N))) cfg.epsilon_pos.le)

theorem centered_le (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) :
    (∑i,|s.val.point i-cfg.start i-s.val.centered i|)≤cfg.epsilon*N :=
  s.property.2.1.trans (rounding_le cfg hd s)

theorem endpoint_valid (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) : (endpoint cfg hd s).Valid (reportConfig cfg hd) := by
  apply MSManuscriptInputRadius.endpoint_valid_of_rounding (reportConfig cfg hd) (endpoint cfg hd s) cfg.offset cfg.offset.property
    (WithLp.ofLp s.val.point) (WithLp.ofLp cfg.start) (WithLp.ofLp s.val.centered)
    s.property.1.regular.1 cfg.start_regular.1
    (mul_nonneg cfg.epsilon_pos.le (Nat.cast_nonneg N)) (centered_le cfg hd s) cfg.contractions
  · exact epochCenter_coe cfg.offset cfg.matrices cfg.hermitian cfg.start
  · exact epochCenter_coe cfg.offset cfg.matrices cfg.hermitian s.val.point
  · rfl
  · exact s.property.1.owner_valid.physical_posSemidef _ (ofEpochConfig cfg hd).floor_pos.le
  · exact le_rfl

theorem psi_eq (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) :
    MSManuscriptNumericalAcceptance.psi (reportConfig cfg hd) (endpoint cfg hd s)=MSManuscriptNumericalEpochMoments.energy (ofEpochConfig cfg hd) s.val := rfl

theorem tangent_eq (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) :
    MSManuscriptNumericalAcceptance.tangent (reportConfig cfg hd) (endpoint cfg hd s)=MSManuscriptNumericalEpochMoments.tangent (ofEpochConfig cfg hd) s.val := by
  simp only [MSManuscriptNumericalAcceptance.tangent,reportConfig,endpoint,MSManuscriptInputRadius.combination,Matrix.mul_sum,realTrace_sum,
    Matrix.mul_smul,realTrace_smul,MSManuscriptNumericalEpochMoments.tangent,MSManuscriptNumericalEpochMoments.gradient,ownerCertificateGradient,dotProduct,
    MSManuscriptNumericalEpochMoments.anchor,ofEpochConfig,EpochConfig.anchor,EpochConfig.center]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem good_probability :
    (499/800:ℝ)≤(MSManuscriptNumericalEpochRun.output (ofEpochConfig cfg hd)).expectation
      (fun s=>if MSManuscriptNumericalAcceptance.Good (reportConfig cfg hd) (endpoint cfg hd s) then 1 else 0) := by
  have hm:=MSManuscriptNumericalEpochSuccess.all_moments cfg hd
  have hh:=MSManuscriptAcceptanceMoments.good_probability_ge (MSManuscriptNumericalEpochRun.output (ofEpochConfig cfg hd))
    (fun s=>(endpoint cfg hd s).cleaningFailed)
    (fun s=>MSManuscriptNumericalAcceptance.psi (reportConfig cfg hd) (endpoint cfg hd s))
    (fun s=>MSManuscriptNumericalAcceptance.tangent (reportConfig cfg hd) (endpoint cfg hd s))
    (s:=Real.sqrt (N:ℝ)) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (count_pos cfg)))
    (fun z=>by
      change 0≤MSManuscriptNumericalAcceptance.psi (reportConfig cfg hd)
        (endpoint cfg hd ((MSManuscriptNumericalEpochRun.output (ofEpochConfig cfg hd)).value z))
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
  MSManuscriptNumericalAcceptance.accepts (reportConfig cfg hd) (endpoint cfg hd s)

def output (r : ℕ) : Sampler (Option (MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd))) :=
  MSManuscriptAcceptanceRetry.output (MSManuscriptNumericalEpochRun.output (ofEpochConfig cfg hd)) (accepts cfg hd) r

theorem acceptance_probability : (499/800:ℝ)≤MSManuscriptAcceptanceRetry.acceptanceProbability
    (MSManuscriptNumericalEpochRun.output (ofEpochConfig cfg hd)) (accepts cfg hd) :=
  MSManuscriptAcceptanceRetry.acceptance_probability_ge _ _
    (fun s=>MSManuscriptNumericalAcceptance.Good (reportConfig cfg hd) (endpoint cfg hd s)) (good_probability cfg hd)
    (fun _ hz=>MSManuscriptNumericalAcceptance.good_accepted _ _ (endpoint_valid cfg hd _) hz)

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

structure GoodEndpoint (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) : Prop where
  progress : (N:ℝ)/64≤(frozenCoordinates s.val.point).card ∨ MSManuscriptNumericalEpochLedger.timeLimit/2≤s.val.time
  reset_growth : ownerPotential (cfg.center s.val.point) cfg.matrices 1 1≤
    ownerPotential cfg.anchor cfg.matrices 1 1+27*Real.sqrt (N:ℝ)

theorem accepted_draw (z : (MSManuscriptNumericalEpochRun.output (ofEpochConfig cfg hd)).Draws)
    (ha : accepts cfg hd ((MSManuscriptNumericalEpochRun.output (ofEpochConfig cfg hd)).value z)=true) :
    GoodEndpoint cfg hd ((MSManuscriptNumericalEpochRun.output (ofEpochConfig cfg hd)).value z) := by
  let s:MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd):=(MSManuscriptNumericalEpochRun.output (ofEpochConfig cfg hd)).value z
  have hav:=MSManuscriptNumericalAcceptance.accepts_sound _ _ (endpoint_valid cfg hd s) ha
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
  have hg:=MSManuscriptNumericalAcceptance.accepted_potential_increment _ _ (endpoint_valid cfg hd s) ha hrb
  have hreset:=ownerPotential_le_base_add (cfg.center s.val.point) cfg.matrices cfg.hermitian
    cfg.contractions (Matrix.PosSemidef.one : (1:Matrix (Fin N) (Fin N) ℝ).PosSemidef) le_rfl (1:ℝ)
  have hbase:=baseDensityPotential_le_owner (cfg.center s.val.point) cfg.matrices cfg.hermitian
    (s.property.1.owner_valid.physical_posSemidef _ (ofEpochConfig cfg hd).floor_pos.le) (1:ℝ)
  refine ⟨MSManuscriptNumericalEpochRun.output_time_or_freezing _ z hp,?_⟩
  change ownerPotential (cfg.center s.val.point) cfg.matrices s.val.owner.physical 1-
    ownerPotential cfg.anchor cfg.matrices 1 1<25*Real.sqrt (N:ℝ) at hg
  simp only [Fintype.card_fin] at hreset
  change ownerPotential (cfg.center s.val.point) cfg.matrices 1 1≤_
  linarith

theorem output_sound (r : ℕ) (z : (output cfg hd r).Draws)
    (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) (ho : (output cfg hd r).value z=some s) : GoodEndpoint cfg hd s :=
  MSManuscriptAcceptanceRetry.output_sound _ _ (GoodEndpoint cfg hd) (accepted_draw cfg hd) r z s ho

end MatrixSpencer.MSManuscriptAcceptedEpoch
