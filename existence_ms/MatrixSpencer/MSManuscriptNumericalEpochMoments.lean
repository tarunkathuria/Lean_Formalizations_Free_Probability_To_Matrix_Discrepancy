import MatrixSpencer.MSManuscriptNumericalEpochRun
import SimpleMS.UniformCertificate

/-! Actual conditional moment accounts for the finite numerical epoch. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalEpochMoments
open MSManuscriptAdaptive MSManuscriptNumericalEpochLedger MSManuscriptNumericalEpochRun
open MSManuscriptSupportedPaid
variable {N d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
set_option maxHeartbeats 1600000
attribute [local irreducible] ownerPotential ownerCertificate

def anchor (c : Config N d) : Matrix (Fin d) (Fin d) ℂ := epochCenter c.offset c.atoms c.hermitian c.start

def center (c : Config N d) (s : State N) := epochCenter c.offset c.atoms c.hermitian s.point

def energy (c : Config N d) (s : State N) : ℝ :=
  ownerCertificate (anchor c) c.atoms c.regularizer (center c s) s.owner.physical

def gradient (c : Config N d) := ownerCertificateGradient (anchor c) c.atoms c.regularizer

def tangent (c : Config N d) (s : State N) : ℝ := gradient c⬝ᵥWithLp.ofLp s.centered

def response (c : Config N d) :=
  (2+12*Real.sqrt (c.threshold*Real.sqrt (N:ℝ))/c.regularizer)*Real.sqrt (N:ℝ)

def energyAccount (c : Config N d) (s : State N) : ℝ :=
  energy c s+(c.threshold/2)*s.paid-(response c+c.driftError)*s.time-2*s.rounding

def tangentAccount (c : Config N d) (s : State N) : ℝ := tangent c s^2-(N:ℝ)*s.time

theorem energy_nonneg (c : Config N d) (s : Certified c) : 0≤energy c s.val :=
  ownerCertificate_nonneg _ _ c.atoms c.hermitian
    (s.property.1.owner_valid.physical_posSemidef _ c.floor_pos.le) _

/-- Finite adaptive iteration of a true conditional account inequality. -/
theorem run_account_le (c : Config N d) (f : Certified c→ℝ)
    (hnext : ∀s,(next c s).expectation f≤f s) (k : ℕ) (s : Certified c) :
    (run c k s).expectation f≤f s := by
  induction k generalizing s with
  | zero => simp only [MSManuscriptNumericalEpochRun.run,Sampler.expectation_pure,le_refl]
  | succ k ih =>
    rw [MSManuscriptNumericalEpochRun.run,Sampler.expectation_bind]
    exact ((next c s).expectation_mono (fun q=>ih q)).trans (hnext s)

@[simp] theorem tangent_prepare (c : Config N d) (s : Certified c) :
    tangent c (prepare c s).val=tangent c s.val := rfl

@[simp] theorem tangentAccount_prepare (c : Config N d) (s : Certified c) :
    tangentAccount c (prepare c s).val=tangentAccount c s.val := rfl

theorem tangent_afterMove (c : Config N d) (s : State N) (h : ℝ) (z : Draws s) :
    tangent c (afterMove c.margin s h z)=tangent c s+
      h*(gradient c⬝ᵥWithLp.ofLp (MSManuscriptNumericalCoordinateStep.increment s.owner.physical s.point z)) := by
  simp only [tangent,afterMove,WithLp.ofLp_add,WithLp.ofLp_smul,dotProduct_add,dotProduct_smul,smul_eq_mul]

/-- No independence between stages is needed: each actual current covariance
is PSD and at most identity, so its saved tangent variance is at most N. -/
theorem movement_tangent_le (c : Config N d) (s : Certified c)
    (hf : s.val.owner.Valid (2*c.floor)) (hn : ¬Stopped c s.val) :
    (movement c s hf hn).expectation (fun q=>tangentAccount c q.val)≤tangentAccount c s.val := by
  have hQ := MSManuscriptNumericalCoordinateStep.covariance_posSemidef s.val.owner.physical
    (s.property.1.owner_valid.physical_posSemidef _ c.floor_pos.le) s.val.point
  have hQ1 := (MSManuscriptNumericalCoordinateStep.covariance_le s.val.owner.physical
    (s.property.1.owner_valid.physical_posSemidef _ c.floor_pos.le) s.val.point).trans s.property.1.owner_le_one
  have hq := (short_trace_lower c.floor_pos.le s.property.1 c.count_large (not_or.mp hn).1).2
  have hm := SimpleMS.UniformCertificate.tangent_square_le (anchor c) c.atoms c.hermitian c.contractions
    c.regularizer (samplingSpace s.val) hQ hQ1 hq (tangent c s.val) (mesh c)
  have he : (movement c s hf hn).expectation (fun q=>tangentAccount c q.val)=
      (∑z:Draws s.val,SimpleMS.UniformSampler.weight (samplingSpace s.val) z*
        (tangent c s.val+mesh c*(gradient c⬝ᵥWithLp.ofLp
          (MSManuscriptNumericalCoordinateStep.increment s.val.owner.physical s.val.point z)))^2)-
        (N:ℝ)*(s.val.time+(mesh c)^2) := by
    change (∑z:Draws s.val,SimpleMS.UniformSampler.weight (samplingSpace s.val) z*
      (tangent c (afterMove c.margin s.val (mesh c) z)^2-(N:ℝ)*(s.val.time+(mesh c)^2)))=_
    have hw : (∑z:Draws s.val,SimpleMS.UniformSampler.weight (samplingSpace s.val) z)=1 :=
      SimpleMS.UniformSampler.weights_sum (samplingSpace s.val) (SimpleMS.Movement.rank_positive _ _ _ hq)
    simp only [tangent_afterMove,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hw,one_mul]
  rw [he]
  change _≤tangent c s.val^2-(N:ℝ)*s.val.time
  change (∑z:Draws s.val,SimpleMS.UniformSampler.weight (samplingSpace s.val) z*
        (tangent c s.val+mesh c*(gradient c⬝ᵥWithLp.ofLp
          (MSManuscriptNumericalCoordinateStep.increment s.val.owner.physical s.val.point z)))^2)≤
    tangent c s.val^2+(mesh c)^2*N at hm
  nlinarith

theorem next_tangent_le (c : Config N d) (s : Certified c) :
    (next c s).expectation (fun q=>tangentAccount c q.val)≤tangentAccount c s.val := by
  classical
  unfold next
  split
  · simp only [Sampler.expectation_pure,le_refl]
  · dsimp only
    split
    · simp only [Sampler.expectation_pure,tangentAccount_prepare,le_refl]
    · exact (movement_tangent_le c (prepare c s) (prepare_floor c s) _).trans_eq (tangentAccount_prepare c s)

theorem output_tangent_moment (c : Config N d) :
    (output c).expectation (fun s=>tangent c s.val^2)≤(N:ℝ)*timeLimit := by
  have hm := run_account_le c (fun s=>tangentAccount c s.val) (next_tangent_le c) (count c) (initial c)
  have hi : tangentAccount c (initial c).val=0 := by simp [tangentAccount,tangent,MSManuscriptNumericalEpochRun.initial,MSManuscriptNumericalEpochLedger.initial]
  change (output c).expectation (fun s=>tangentAccount c s.val)≤_ at hm
  rw [hi] at hm
  have hp : (output c).expectation (fun s=>tangent c s.val^2-(N:ℝ)*timeLimit)≤
      (output c).expectation (fun s=>tangentAccount c s.val) :=
    (output c).expectation_mono (fun s=>sub_le_sub_left
      (mul_le_mul_of_nonneg_left s.property.2.2 (Nat.cast_nonneg N)) _)
  rw [Sampler.expectation_sub,Sampler.expectation_const] at hp
  linarith


/-- Paid preparation decreases the joint energy/paid account, while all
unpaid support deletions are already included in its actual potential bound. -/
theorem prepare_energy_le (c : Config N d) (s : Certified c) :
    energyAccount c (prepare c s).val≤energyAccount c s.val := by
  let P := params c s.val
  let y := preparationResult c s
  have hP := params_valid c s
  have hc := MSManuscriptSupportedPreparation.output_sound P hP s.val.owner
    ⟨s.property.1.owner_valid,s.property.1.owner_le_one,s.property.1.dim_le⟩ (preparationResult_eq c s)
  have ha : 0≤paidSize P*(y.2:ℝ) := mul_nonneg (paidSize_pos P hP).le (Nat.cast_nonneg _)
  have hp : ownerPotential (center c s.val) c.atoms y.1.physical c.regularizer+
      (c.threshold/2)*(paidSize P*(y.2:ℝ))≤
      ownerPotential (center c s.val) c.atoms s.val.owner.physical c.regularizer := by
    have ht := hc.potential_paid
    change ownerPotential (center c s.val) c.atoms y.1.physical c.regularizer+
      (5*c.threshold*paidSize P/8)*(y.2:ℝ)≤
      ownerPotential (center c s.val) c.atoms s.val.owner.physical c.regularizer at ht
    have hprice := mul_nonneg c.threshold_pos.le ha
    nlinarith
  have he := ownerCertificate_covariance_payment (anchor c) (center c s.val) c.atoms c.regularizer
    (c.threshold/2) (paidSize P*(y.2:ℝ)) s.val.owner.physical y.1.physical hp
  change energy c (prepare c s).val+(c.threshold/2)*(s.val.paid+paidSize P*(y.2:ℝ))-
    (response c+c.driftError)*s.val.time-2*s.val.rounding≤_
  change energy c (prepare c s).val+(c.threshold/2)*(paidSize P*(y.2:ℝ))≤energy c s.val at he
  unfold energyAccount
  linarith

/-- Pathwise center rounding has the exact accumulated L1 cost. -/
theorem move_energy_pointwise (c : Config N d) (s : Certified c)
    (hf : s.val.owner.Valid (2*c.floor)) (hn : ¬Stopped c s.val) (z : Draws s.val) :
    energyAccount c (moveValue c s hf hn z).val≤energyAccount c s.val+
      (ownerCertificate (anchor c) c.atoms c.regularizer
        (center c s.val+mesh c•ownerPhysicalIncrement c.atoms c.hermitian
          (MSManuscriptNumericalCoordinateStep.increment s.val.owner.physical s.val.point z))
        (s.val.owner.physical-(mesh c)^2•Q s.val)-energy c s.val)-
      (response c+c.driftError)*(mesh c)^2 := by
  let moved := MSManuscriptNumericalCoordinateStep.moved s.val.owner.physical s.val.point (mesh c) z
  let rounded := MSManuscriptNumericalCoordinateStep.rounded c.margin s.val.owner.physical s.val.point (mesh c) z
  let cost : ℝ := ∑i,|rounded i-moved i|
  let Hm := epochCenter c.offset c.atoms c.hermitian moved
  let Hr := epochCenter c.offset c.atoms c.hermitian rounded
  have hnrm : ‖(Hr : Matrix (Fin d) (Fin d) ℂ)-(Hm : Matrix (Fin d) (Fin d) ℂ)‖≤cost := by
    simpa only [Hr,Hm,epochCenter_coe,add_sub_add_left_eq_sub] using
      ThresholdRounding.combination_norm_sub_le_l1 c.atoms c.contractions (WithLp.ofLp moved) (WithLp.ofLp rounded)
  have hphys : (moveValue c s hf hn z).val.owner.physical=s.val.owner.physical-(mesh c)^2•Q s.val :=
    MSManuscriptOwnerAdvance.physical s.val.owner s.property.1.owner_valid (Q s.val)
      (MSManuscriptNumericalCoordinateStep.covariance_posSemidef _
        (s.property.1.owner_valid.physical_posSemidef _ c.floor_pos.le) _)
      (MSManuscriptNumericalCoordinateStep.covariance_le _
        (s.property.1.owner_valid.physical_posSemidef _ c.floor_pos.le) _) _
  have hC : (s.val.owner.physical-(mesh c)^2•Q s.val).PosSemidef := by
    rw [←hphys]
    exact (moveValue c s hf hn z).property.1.owner_valid.physical_posSemidef _ c.floor_pos.le
  have hr := abs_ownerCertificate_center_difference_le (anchor c) Hm.property Hr.property
    c.atoms c.hermitian hC c.regularizer
  have hb := (le_abs_self (ownerCertificate (anchor c) c.atoms c.regularizer Hr _-
    ownerCertificate (anchor c) c.atoms c.regularizer Hm _)).trans hr
  have hcenter : Hm=center c s.val+mesh c•ownerPhysicalIncrement c.atoms c.hermitian
      (MSManuscriptNumericalCoordinateStep.increment s.val.owner.physical s.val.point z) :=
    epochCenter_add_smul c.offset c.atoms c.hermitian s.val.point _ (mesh c)
  have he : energy c (moveValue c s hf hn z).val=
      ownerCertificate (anchor c) c.atoms c.regularizer Hr (s.val.owner.physical-(mesh c)^2•Q s.val) := by
    unfold energy
    rw [hphys]
    rfl
  change energy c (moveValue c s hf hn z).val+(c.threshold/2)*s.val.paid-
    (response c+c.driftError)*(s.val.time+(mesh c)^2)-2*(s.val.rounding+cost)≤_
  rw [he]
  have hb2 := hb.trans (mul_le_mul_of_nonneg_left hnrm (by norm_num : (0:ℝ)≤2))
  rw [hcenter] at hb2
  change ownerCertificate (anchor c) c.atoms c.regularizer Hr (s.val.owner.physical-(mesh c)^2•Q s.val)-
    ownerCertificate (anchor c) c.atoms c.regularizer
      ((center c s.val : Matrix (Fin d) (Fin d) ℂ)+mesh c•
        (ownerPhysicalIncrement c.atoms c.hermitian
          (MSManuscriptNumericalCoordinateStep.increment s.val.owner.physical s.val.point z) : Matrix (Fin d) (Fin d) ℂ))
      (s.val.owner.physical-(mesh c)^2•Q s.val)≤2*cost at hb2
  unfold energyAccount
  linarith

/-- Actual numerical preparation and the original fixed mesh discharge the
conditional anchored-certificate drift; no response or Taylor bound is assumed. -/
theorem prepared_movement_energy_le (c : Config N d) (s : Certified c)
    (hn : ¬Stopped c (prepare c s).val) :
    (movement c (prepare c s) (prepare_floor c s) hn).expectation (fun q=>energyAccount c q.val)≤
      energyAccount c (prepare c s).val := by
  let p := prepare c s
  let W := movement c p (prepare_floor c s) hn
  let inc : Certified c→ℝ := fun _=>0
  let D := response c+c.driftError
  let e : Draws p.val→ℝ := fun z=>ownerCertificate (anchor c) c.atoms c.regularizer
    (center c p.val+mesh c•ownerPhysicalIncrement c.atoms c.hermitian
      (MSManuscriptNumericalCoordinateStep.increment p.val.owner.physical p.val.point z))
    (p.val.owner.physical-(mesh c)^2•Q p.val)-energy c p.val
  have hb : W.expectation (fun q=>energyAccount c q.val)≤
      ∑z:Draws p.val,SimpleMS.UniformSampler.weight (samplingSpace p.val) z*
        (energyAccount c p.val+e z-D*(mesh c)^2) := by
    apply Finset.sum_le_sum
    intro z _
    exact mul_le_mul_of_nonneg_left (move_energy_pointwise c p (prepare_floor c s) hn z) (W.weight_nonneg z)
  have hq := (short_trace_lower c.floor_pos.le p.property.1 c.count_large (not_or.mp hn).1).2
  have hQ := MSManuscriptNumericalCoordinateStep.covariance_posSemidef _
    (p.property.1.owner_valid.physical_posSemidef _ c.floor_pos.le) p.val.point
  have hw : (∑z:Draws p.val,SimpleMS.UniformSampler.weight (samplingSpace p.val) z)=1 :=
    SimpleMS.UniformSampler.weights_sum (samplingSpace p.val) (SimpleMS.Movement.rank_positive _ _ _ hq)
  have he : (∑z:Draws p.val,SimpleMS.UniformSampler.weight (samplingSpace p.val) z*
        (energyAccount c p.val+e z-D*(mesh c)^2))=
      energyAccount c p.val+(∑z:Draws p.val,SimpleMS.UniformSampler.weight (samplingSpace p.val) z*e z)-D*(mesh c)^2 := by
    simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.sum_mul,hw,one_mul]
  rw [he] at hb
  have hmesh : mesh c≤MSManuscriptPreparedMovement.stepSize (params c s.val) c.driftError :=
    (mesh_le_base c).trans (MSManuscriptEpochInput.mesh_le_step c.offset c.atoms c.hermitian
      c.regularizer c.floor c.threshold c.dimension_pos c.margin c.driftError s.val.point)
  have hd := MSManuscriptPreparedMovement.output_drift_atStep (params c s.val) (params_valid c s)
    (by have h:=c.count_large; omega) s.val.owner
    ⟨s.property.1.owner_valid,s.property.1.owner_le_one,s.property.1.dim_le⟩ (preparationResult_eq c s)
    (frozenCoordinates p.val.point) p.val.point hq c.driftError_pos (mesh_pos c) hmesh
  have hi : (∑z:Draws p.val,SimpleMS.UniformSampler.weight (samplingSpace p.val) z*e z)≤(mesh c)^2*D := by
    change (∑z:SimpleMS.UniformSampler.Draws (samplingSpace p.val),SimpleMS.UniformSampler.weight (samplingSpace p.val) z*
      (ownerCertificate (anchor c) c.atoms c.regularizer
        (center c p.val+mesh c•ownerPhysicalIncrement c.atoms c.hermitian
          (SimpleMS.UniformSampler.increment (samplingSpace p.val) z))
        (p.val.owner.physical-(mesh c)^2•Q p.val)-
        ownerCertificate (anchor c) c.atoms c.regularizer (center c p.val) p.val.owner.physical))≤_
    have hcancel := SimpleMS.UniformCertificate.certificate_drift_eq (anchor c) c.atoms c.hermitian
      c.regularizer (center c p.val) p.val.owner.physical (samplingSpace p.val) (mesh c)
    change (∑z:Draws p.val, SimpleMS.UniformSampler.weight (samplingSpace p.val) z * e z) = _ at hcancel
    exact hcancel.le.trans hd
  change W.expectation (fun q=>energyAccount c q.val)≤_
  nlinarith

theorem next_energy_le (c : Config N d) (s : Certified c) :
    (next c s).expectation (fun q=>energyAccount c q.val)≤energyAccount c s.val := by
  classical
  unfold next
  split
  · simp only [Sampler.expectation_pure,le_refl]
  · dsimp only
    split
    · simpa only [Sampler.expectation_pure] using prepare_energy_le c s
    · exact (prepared_movement_energy_le c s _).trans (prepare_energy_le c s)

/-- Both moment accounts are consequences of the actual finite adaptive run. -/
theorem output_energy_account (c : Config N d) :
    (output c).expectation (fun s=>energyAccount c s.val)≤2*Real.sqrt (N:ℝ) := by
  have hm := run_account_le c (fun s=>energyAccount c s.val) (next_energy_le c) (count c) (initial c)
  have hi : energyAccount c (initial c).val≤2*Real.sqrt (N:ℝ) := by
    have he := ownerCertificate_initial_le (anchor c) c.atoms c.hermitian c.contractions
      Matrix.PosSemidef.one (le_refl (1 : Matrix (Fin N) (Fin N) ℝ)) c.regularizer
    simpa [energyAccount,energy,center,anchor,MSManuscriptNumericalEpochRun.initial,
      MSManuscriptNumericalEpochLedger.initial,MSManuscriptSupportedPreparation.initial,
      MSManuscriptSupportedOwner.Owner.physical] using he
  exact hm.trans hi


theorem response_nonneg (c : Config N d) : 0≤response c := by
  have ht:=c.regularizer_pos
  unfold response
  positivity

theorem rounding_le (c : Config N d) (s : Certified c) : s.val.rounding≤c.margin*N := by
  have hc : ((frozenCoordinates s.val.point).card:ℝ)≤N := by
    exact_mod_cast (show (frozenCoordinates s.val.point).card≤N by simpa using Finset.card_le_univ (frozenCoordinates s.val.point))
  exact s.property.1.rounding_le.trans (mul_le_mul_of_nonneg_left hc c.margin_pos.le)

/-- Actual numerical epoch joint moment, with all local drift and sampler
identities proved internally. Only primitive scalar Config fields remain. -/
theorem output_joint_moment (c : Config N d) :
    (output c).expectation (fun s=>energy c s.val+(c.threshold/2)*s.val.paid)≤
      2*Real.sqrt (N:ℝ)+(response c+c.driftError)*timeLimit+2*c.margin*N := by
  have hD : 0≤response c+c.driftError := add_nonneg (response_nonneg c) c.driftError_pos.le
  have hp (s : Certified c) : energy c s.val+(c.threshold/2)*s.val.paid≤
      energyAccount c s.val+((response c+c.driftError)*timeLimit+2*c.margin*N) := by
    have ht := mul_le_mul_of_nonneg_left s.property.2.2 hD
    have hr := rounding_le c s
    unfold energyAccount
    linarith
  have hm := (output c).expectation_mono hp
  have he : (output c).expectation (fun s=>energyAccount c s.val+
      ((response c+c.driftError)*timeLimit+2*c.margin*N))=
      (output c).expectation (fun s=>energyAccount c s.val)+
      ((response c+c.driftError)*timeLimit+2*c.margin*N) := by
    simp only [Sampler.expectation,mul_add,Finset.sum_add_distrib,←Finset.sum_mul,
      Sampler.weight_sum,one_mul]
  rw [he] at hm
  linarith [output_energy_account c]

end MatrixSpencer.MSManuscriptNumericalEpochMoments
