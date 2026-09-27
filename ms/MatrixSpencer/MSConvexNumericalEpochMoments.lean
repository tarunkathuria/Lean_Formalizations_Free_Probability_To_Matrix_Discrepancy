import MatrixSpencer.MSManuscriptNumericalEpochMoments
import MatrixSpencer.MSConvexNumericalEpochRun
import MatrixSpencer.MSConvexPreparedMovement

/-! The original square walk with convex owner-value queries substituted.
The state, invariants, tuning constants and non-query primitives remain original. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexNumericalEpochMoments
open MSManuscriptNumericalEpochMoments MSManuscriptAdaptive MSManuscriptNumericalEpochLedger MSConvexNumericalEpochRun MSManuscriptSupportedPaid
variable [MSConvexOwnerValue.Oracle]
variable {N d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
attribute [local irreducible] ownerPotential ownerCertificate
export MSManuscriptNumericalEpochMoments (anchor center energy gradient tangent response energyAccount tangentAccount energy_nonneg tangent_afterMove movement_tangent_le move_energy_pointwise response_nonneg rounding_le)

theorem run_account_le (c : Config N d) (f : Certified c→ℝ)
    (hnext : ∀s,(next c s).expectation f≤f s) (k : ℕ) (s : Certified c) :
    (run c k s).expectation f≤f s := by
  induction k generalizing s with
  | zero => simp only [MSConvexNumericalEpochRun.run,Sampler.expectation_pure,le_refl]
  | succ k ih =>
    rw [MSConvexNumericalEpochRun.run,Sampler.expectation_bind]
    exact ((next c s).expectation_mono (fun q=>ih q)).trans (hnext s)

@[simp] theorem tangent_prepare (c : Config N d) (s : Certified c) :
    tangent c (prepare c s).val=tangent c s.val := rfl

@[simp] theorem tangentAccount_prepare (c : Config N d) (s : Certified c) :
    tangentAccount c (prepare c s).val=tangentAccount c s.val := rfl

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
  have hi : tangentAccount c (initial c).val=0 := by simp [tangentAccount,tangent,MSConvexNumericalEpochRun.initial,MSManuscriptNumericalEpochLedger.initial]
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
  have hc := MSConvexSupportedPreparation.output_sound P hP s.val.owner
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
  have hd := MSConvexPreparedMovement.output_drift_atStep (params c s.val) (params_valid c s)
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
    simpa [energyAccount,energy,center,anchor,MSConvexNumericalEpochRun.initial,
      MSManuscriptNumericalEpochLedger.initial,MSManuscriptSupportedPreparation.initial,
      MSManuscriptSupportedOwner.Owner.physical] using he
  exact hm.trans hi

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

end MatrixSpencer.MSConvexNumericalEpochMoments
