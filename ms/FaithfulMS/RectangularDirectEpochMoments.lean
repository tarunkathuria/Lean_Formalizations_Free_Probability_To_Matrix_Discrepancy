import FaithfulMS.RectangularDirectEpochStateFacts
import MatrixSpencer.RectangularRidgeLiveSamplerMoments
import MatrixSpencer.RectangularRidgePreparedResponse

/-!
# Conditional moments of the actual finite rectangular ridge epoch

The saved density belongs to the actual mixed regularizer. Preparation,
shorting, sampling, matching and rounding are the constructed numerical run.
No favorable draw, response bound or successful preparation is an input.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularDirectEpochMoments
open RectangularRidgeEpochInput RectangularDirectEpochRun
open MSManuscriptAdaptive (Sampler)
open MSManuscriptNumericalEpochLedger (State Q Draws afterMove samplingSpace)
open RectangularRidgePreparationData (floor)
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgeEpochMomentsCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeEpochMomentsSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
set_option maxHeartbeats 1400000
attribute [local irreducible] prepare preparationResult run RectangularRidgePotential.optimizer
  RectangularRidgeCovarianceCalculus.ownerPotential regularizedOwnerPotential

def depth (c : Config N d) := RectangularRidgeTuning.depth N d c.count_pos
def theta (c : Config N d) := RectangularRidgePrimitiveParameters.weight N d c.count_pos
def ridge (_c : Config N d) : ℝ := 1 / (d : ℝ)
def anchor (c : Config N d) := center c c.start

def energy (c : Config N d) (s : State N) : ℝ :=
  RectangularRidgeCertificate.certificate (anchor c) c.atoms (depth c) (theta c) (ridge c)
    (center c s.point) s.owner.physical

def gradient (c : Config N d) :=
  RectangularRidgeCertificate.gradient (anchor c) c.atoms (depth c) (theta c) (ridge c)

def tangent (c : Config N d) (s : State N) : ℝ := gradient c ⬝ᵥ WithLp.ofLp s.centered

def response (c : Config N d) : ℝ :=
  RectangularRidgeUniformResponse.coefficient N d c.count_pos * Real.sqrt (live c : ℝ)
def driftError : ℝ := 1 / (2 : ℝ) ^ 40

def energyAccount (c : Config N d) (s : State N) : ℝ :=
  energy c s + (threshold c / 2) * s.paid - (response c + driftError) * s.time - 2 * s.rounding

def tangentAccount (c : Config N d) (s : State N) : ℝ := tangent c s ^ 2 - (live c : ℝ) * s.time

theorem energy_nonneg (c : Config N d) (s : Certified c) : 0 ≤ energy c s.val :=
  RectangularRidgeCertificate.certificate_nonneg _ _ c.atoms c.hermitian
    (s.property.1.owner_valid.physical_posSemidef _ (by norm_num [floor])) _ _ _

theorem run_account_le (solver : RectangularDirectSolver.Service) (a : Fin d)
    (c : Config N d) (f : Certified c → ℝ)
    (hnext : ∀ s, (next solver a c s).expectation f ≤ f s) (k : ℕ) (s : Certified c) :
    (run solver a c k s).expectation f ≤ f s := by
  induction k generalizing s with
  | zero => simp only [run, Sampler.expectation_pure, le_refl]
  | succ k ih =>
    rw [run, Sampler.expectation_bind]
    exact ((next solver a c s).expectation_mono (fun q => ih q)).trans (hnext s)

theorem tangent_afterMove (c : Config N d) (s : State N) (h : ℝ) (z : Draws s) :
    tangent c (afterMove (margin N) s h z) = tangent c s +
      h * (gradient c ⬝ᵥ WithLp.ofLp (MSManuscriptNumericalCoordinateStep.increment s.owner.physical s.point z)) := by
  simp only [tangent, afterMove, WithLp.ofLp_add, WithLp.ofLp_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]

/-- The actual tangent square is compensated by the live, not ambient, count. -/
theorem movement_tangent_le (c : Config N d) (s : Certified c)
    (hf : s.val.owner.Valid (2 * floor)) (hn : ¬Stopped c s.val) :
    (movement c s hf hn).expectation (fun q => tangentAccount c q.val) ≤ tangentAccount c s.val := by
  have hC := s.property.1.owner_valid.physical_posSemidef s.val.owner (by norm_num [floor])
  have hQ := MSManuscriptNumericalCoordinateStep.covariance_posSemidef s.val.owner.physical hC s.val.point
  have hQC := MSManuscriptNumericalCoordinateStep.covariance_le s.val.owner.physical hC s.val.point
  have hQ1 := hQC.trans s.property.1.owner_le_one
  have hF := RectangularRidgeLiveShort.annihilators_mono s.val.owner.physical (Q s.val) hQ hQC
    (oldFrozen c) s.property.1.annihilates
  have hq := (short_trace c s hn).2
  have hm := RectangularRidgeLiveSamplerMoments.tangent_square_le (anchor c) c.atoms c.hermitian c.contractions
    (depth c) (theta c) (ridge c) (oldFrozen c) (samplingSpace s.val) hQ hQ1 hF hq (tangent c s.val) (mesh c)
  have he : (movement c s hf hn).expectation (fun q => tangentAccount c q.val) =
      (∑ z : Draws s.val, SimpleMS.UniformSampler.weight (samplingSpace s.val) z *
        (tangent c s.val + mesh c * (gradient c ⬝ᵥ WithLp.ofLp
          (MSManuscriptNumericalCoordinateStep.increment s.val.owner.physical s.val.point z))) ^ 2) -
        (live c : ℝ) * (s.val.time + mesh c ^ 2) := by
    change (∑ z : Draws s.val, SimpleMS.UniformSampler.weight (samplingSpace s.val) z *
      (tangent c (afterMove (margin N) s.val (mesh c) z) ^ 2 -
        (live c : ℝ) * (s.val.time + mesh c ^ 2))) = _
    have hw : (∑ z : Draws s.val, SimpleMS.UniformSampler.weight (samplingSpace s.val) z) = 1 :=
      SimpleMS.UniformSampler.weights_sum (samplingSpace s.val) (SimpleMS.Movement.rank_positive _ _ _ hq)
    simp only [tangent_afterMove, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul]
  rw [he]
  change _ ≤ tangent c s.val ^ 2 - (live c : ℝ) * s.val.time
  change (∑ z : Draws s.val, SimpleMS.UniformSampler.weight (samplingSpace s.val) z *
      (tangent c s.val + mesh c * (gradient c ⬝ᵥ WithLp.ofLp
        (MSManuscriptNumericalCoordinateStep.increment s.val.owner.physical s.val.point z))) ^ 2) ≤
      tangent c s.val ^ 2 + mesh c ^ 2 * live c at hm
  nlinarith

@[simp] theorem tangentAccount_prepare (solver : RectangularDirectSolver.Service) (a : Fin d)
    (c : Config N d) (s : Certified c) : tangentAccount c (prepare solver a c s).val = tangentAccount c s.val := by
  simp only [tangentAccount, tangent, prepare_centered, prepare_time]

theorem next_tangent_le (solver : RectangularDirectSolver.Service) (a : Fin d)
    (c : Config N d) (s : Certified c) :
    (next solver a c s).expectation (fun q => tangentAccount c q.val) ≤ tangentAccount c s.val := by
  classical
  unfold next
  split
  · simp only [Sampler.expectation_pure, le_refl]
  · dsimp only
    split
    · simp only [Sampler.expectation_pure, tangentAccount_prepare, le_refl]
    · exact (movement_tangent_le c (prepare solver a c s) (prepare_floor solver a c s) _).trans_eq
        (tangentAccount_prepare solver a c s)

/-- The conditional finite tangent account yields the actual output moment. -/
theorem output_tangent_moment (solver : RectangularDirectSolver.Service) (a : Fin d)
    (c : Config N d) :
    (output solver a c).expectation (fun s => tangent c s.val ^ 2) ≤ (live c : ℝ) * duration c := by
  have hm := run_account_le solver a c (fun s => tangentAccount c s.val) (next_tangent_le solver a c)
    (count c) (initial c)
  have hi : tangentAccount c (initial c).val = 0 := by simp [tangentAccount, tangent, initial, RectangularRidgeLiveOwner.initial]
  change (output solver a c).expectation (fun s => tangentAccount c s.val) ≤ _ at hm
  rw [hi] at hm
  have hp : (output solver a c).expectation (fun s => tangent c s.val ^ 2 - (live c : ℝ) * duration c) ≤
      (output solver a c).expectation (fun s => tangentAccount c s.val) :=
    (output solver a c).expectation_mono (fun s => sub_le_sub_left
      (mul_le_mul_of_nonneg_left s.property.2.2 (Nat.cast_nonneg (live c))) _)
  rw [Sampler.expectation_sub, Sampler.expectation_const] at hp
  linarith

private theorem preparation_payment (c : Config N d) (s : Certified c)
    (y : MSManuscriptSupportedOwner.Owner N × ℕ)
    (hc : RectangularRidgePreparationRun.Certificate (params c s.val.point) s.val.owner
      (RectangularRidgePreparationRun.budget (params c s.val.point)) y) :
    RectangularRidgeCertificate.certificate (anchor c) c.atoms (depth c) (theta c) (ridge c)
      (center c s.val.point) y.1.physical + (threshold c / 2) *
        (RectangularRidgePreparationData.paidSize (params c s.val.point) * (y.2 : ℝ)) ≤ energy c s.val := by
  let P := params c s.val.point
  have hP := params_valid c s.val.point s.property.1.regular.1
  have hpaid : 0 ≤ RectangularRidgePreparationData.paidSize P * (y.2 : ℝ) :=
    mul_nonneg (RectangularRidgePreparationData.paidSize_pos P).le (Nat.cast_nonneg _)
  have ht : 0 ≤ threshold c := (RectangularRidgePreparationData.threshold_pos P hP).le
  have hpay : regularizedOwnerPotential (center c s.val.point) c.atoms y.1.physical
      (RectangularRidgeCovarianceCalculus.regularizer (depth c) (theta c) (ridge c)) +
      (threshold c / 2) * (RectangularRidgePreparationData.paidSize P * (y.2 : ℝ)) ≤
        regularizedOwnerPotential (center c s.val.point) c.atoms s.val.owner.physical
          (RectangularRidgeCovarianceCalculus.regularizer (depth c) (theta c) (ridge c)) := by
    have hh := hc.potential_paid
    change RectangularRidgePreparationData.potential P y.1 +
      RectangularRidgePreparationData.paidGain P * (y.2 : ℝ) ≤
        RectangularRidgePreparationData.potential P s.val.owner at hh
    dsimp only [RectangularRidgePreparationData.potential, RectangularRidgeCovarianceCalculus.ownerPotential,
      RectangularRidgePreparationData.paidGain, RectangularRidgePreparationData.depth,
      RectangularRidgePreparationData.theta, RectangularRidgePreparationData.ridge, P, params] at hh
    simp only [RectangularRidgeCovarianceCalculus.ownerPotential] at hh
    change regularizedOwnerPotential (center c s.val.point) c.atoms y.1.physical
      (RectangularRidgeCovarianceCalculus.regularizer (depth c) (theta c) (ridge c)) +
      (5 * threshold c * RectangularRidgePreparationData.paidSize P / 8) * (y.2 : ℝ) ≤
        regularizedOwnerPotential (center c s.val.point) c.atoms s.val.owner.physical
          (RectangularRidgeCovarianceCalculus.regularizer (depth c) (theta c) (ridge c)) at hh
    nlinarith [mul_nonneg ht hpaid]
  have he := RectangularRidgeCertificate.certificate_covariance_payment (anchor c) (center c s.val.point)
    c.atoms (depth c) (theta c) (ridge c) (threshold c / 2)
    (RectangularRidgePreparationData.paidSize P * (y.2 : ℝ)) s.val.owner.physical y.1.physical hpay
  exact he

/-- Actual numerical preparation pays for its full covariance trace loss.
No cap-report accuracy or preparation-success premise remains. -/
theorem prepare_energy_le (solver : RectangularDirectSolver.Service) (a : Fin d)
    (c : Config N d) (s : Certified c) :
    energyAccount c (prepare solver a c s).val ≤ energyAccount c s.val := by
  let P := params c s.val.point
  let y := preparationResult solver a c s
  have he := preparation_payment c s y (prepare_certificate solver a c s)
  have he' : energy c (prepare solver a c s).val + (threshold c / 2) *
      (RectangularRidgePreparationData.paidSize P * (y.2 : ℝ)) ≤ energy c s.val := by
    simpa only [energy, prepare_point, prepare_owner] using he
  unfold energyAccount
  rw [prepare_paid, prepare_time, prepare_rounding]
  change energy c (prepare solver a c s).val + (threshold c / 2) *
    (s.val.paid + RectangularRidgePreparationData.paidSize P * (y.2 : ℝ)) -
      (response c + driftError) * s.val.time - 2 * s.val.rounding ≤ _
  linarith

/-- Threshold snaps have their actual accumulated coordinate cost; the
matched covariance withdrawal is the computed physical owner update. -/
theorem move_energy_pointwise (c : Config N d) (s : Certified c)
    (hf : s.val.owner.Valid (2 * floor)) (hn : ¬Stopped c s.val) (z : Draws s.val) :
    energyAccount c (moveValue c s hf hn z).val ≤ energyAccount c s.val +
      (RectangularRidgeCertificate.certificate (anchor c) c.atoms (depth c) (theta c) (ridge c)
        (center c s.val.point + mesh c • ownerPhysicalIncrement c.atoms c.hermitian
          (MSManuscriptNumericalCoordinateStep.increment s.val.owner.physical s.val.point z))
        (s.val.owner.physical - mesh c ^ 2 • Q s.val) - energy c s.val) -
      (response c + driftError) * mesh c ^ 2 := by
  let moved := MSManuscriptNumericalCoordinateStep.moved s.val.owner.physical s.val.point (mesh c) z
  let rounded := MSManuscriptNumericalCoordinateStep.rounded (margin N) s.val.owner.physical s.val.point (mesh c) z
  let cost : ℝ := ∑ i, |rounded i - moved i|
  let Hm := center c moved
  let Hr := center c rounded
  have hnrm : ‖(Hr : Matrix (Fin d) (Fin d) ℂ) - (Hm : Matrix (Fin d) (Fin d) ℂ)‖ ≤ cost := by
    simpa only [Hr, Hm, center, epochCenter_coe, add_sub_add_left_eq_sub] using
      ThresholdRounding.combination_norm_sub_le_l1 c.atoms c.contractions (WithLp.ofLp moved) (WithLp.ofLp rounded)
  have hC := s.property.1.owner_valid.physical_posSemidef s.val.owner (by norm_num [floor])
  have hQ := MSManuscriptNumericalCoordinateStep.covariance_posSemidef _ hC s.val.point
  have hQC := MSManuscriptNumericalCoordinateStep.covariance_le _ hC s.val.point
  have hphys : (moveValue c s hf hn z).val.owner.physical = s.val.owner.physical - mesh c ^ 2 • Q s.val :=
    MSManuscriptOwnerAdvance.physical s.val.owner s.property.1.owner_valid (Q s.val) hQ hQC (mesh c)
  have hC' : (s.val.owner.physical - mesh c ^ 2 • Q s.val).PosSemidef := by
    rw [← hphys]
    exact (moveValue c s hf hn z).property.1.owner_valid.physical_posSemidef _ (by norm_num [floor])
  have hr := RectangularRidgeCertificate.abs_center_difference_le (anchor c) Hm.property Hr.property
    c.atoms c.hermitian hC' (depth c) (theta c) (ridge c)
  have hb := (le_abs_self (RectangularRidgeCertificate.certificate (anchor c) c.atoms (depth c) (theta c) (ridge c) Hr _ -
    RectangularRidgeCertificate.certificate (anchor c) c.atoms (depth c) (theta c) (ridge c) Hm _)).trans hr
  have hcenter : Hm = center c s.val.point + mesh c • ownerPhysicalIncrement c.atoms c.hermitian
      (MSManuscriptNumericalCoordinateStep.increment s.val.owner.physical s.val.point z) :=
    epochCenter_add_smul 0 c.atoms c.hermitian s.val.point _ (mesh c)
  have he : energy c (moveValue c s hf hn z).val =
      RectangularRidgeCertificate.certificate (anchor c) c.atoms (depth c) (theta c) (ridge c) Hr
        (s.val.owner.physical - mesh c ^ 2 • Q s.val) := by
    unfold energy
    rw [hphys]
    rfl
  change energy c (moveValue c s hf hn z).val + (threshold c / 2) * s.val.paid -
    (response c + driftError) * (s.val.time + mesh c ^ 2) - 2 * (s.val.rounding + cost) ≤ _
  rw [he]
  have hb2 := hb.trans (mul_le_mul_of_nonneg_left hnrm (by norm_num : (0 : ℝ) ≤ 2))
  rw [hcenter] at hb2
  change RectangularRidgeCertificate.certificate (anchor c) c.atoms (depth c) (theta c) (ridge c) Hr
      (s.val.owner.physical - mesh c ^ 2 • Q s.val) -
    RectangularRidgeCertificate.certificate (anchor c) c.atoms (depth c) (theta c) (ridge c)
      ((center c s.val.point : Matrix (Fin d) (Fin d) ℂ) + mesh c •
        (ownerPhysicalIncrement c.atoms c.hermitian
          (MSManuscriptNumericalCoordinateStep.increment s.val.owner.physical s.val.point z) : Matrix (Fin d) (Fin d) ℂ))
      (s.val.owner.physical - mesh c ^ 2 • Q s.val) ≤ 2 * cost at hb2
  unfold energyAccount
  linarith

private theorem capped_movement_energy_le (c : Config N d) (s : Certified c)
    (hf : s.val.owner.Valid (2 * floor)) (hn : ¬Stopped c s.val)
    (hcap : RectangularRidgePreparationData.Cap (params c s.val.point) s.val.owner) :
    (movement c s hf hn).expectation (fun q => energyAccount c q.val) ≤ energyAccount c s.val := by
  let P := params c s.val.point
  let W := movement c s hf hn
  let D := response c + driftError
  let e : Draws s.val → ℝ := fun z =>
    RectangularRidgeCertificate.certificate (anchor c) c.atoms (depth c) (theta c) (ridge c)
      (center c s.val.point + mesh c • ownerPhysicalIncrement c.atoms c.hermitian
        (MSManuscriptNumericalCoordinateStep.increment s.val.owner.physical s.val.point z))
      (s.val.owner.physical - mesh c ^ 2 • Q s.val) - energy c s.val
  have hb : W.expectation (fun q => energyAccount c q.val) ≤
      ∑ z : Draws s.val, SimpleMS.UniformSampler.weight (samplingSpace s.val) z *
        (energyAccount c s.val + e z - D * mesh c ^ 2) := by
    apply Finset.sum_le_sum
    intro z _
    exact mul_le_mul_of_nonneg_left (move_energy_pointwise c s hf hn z) (W.weight_nonneg z)
  have hC := s.property.1.owner_valid.physical_posSemidef _ (by norm_num [floor])
  have hQ := MSManuscriptNumericalCoordinateStep.covariance_posSemidef _ hC s.val.point
  have hq := (short_trace c s hn).2
  have hw : (∑ z : Draws s.val, SimpleMS.UniformSampler.weight (samplingSpace s.val) z) = 1 :=
    SimpleMS.UniformSampler.weights_sum (samplingSpace s.val) (SimpleMS.Movement.rank_positive _ _ _ hq)
  have he : (∑ z : Draws s.val, SimpleMS.UniformSampler.weight (samplingSpace s.val) z *
      (energyAccount c s.val + e z - D * mesh c ^ 2)) =
        energyAccount c s.val + (∑ z : Draws s.val, SimpleMS.UniformSampler.weight (samplingSpace s.val) z * e z) -
          D * mesh c ^ 2 := by
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]
  rw [he] at hb
  have hp := params_valid c s.val.point s.property.1.regular.1
  have hd := RectangularRidgePreparedResponse.prepared_actual_movement_of_frozen P hp s.val.owner
    ⟨s.property.1.owner_valid, s.property.1.owner_le_one, s.property.1.dim_le.trans (live_le c)⟩
    hcap (oldFrozen c) s.property.1.annihilates
    (by have := live_large c; change 0 < live c; omega) rfl
    (frozenCoordinates s.val.point) s.val.point hq
  have hi : (∑ z : Draws s.val, SimpleMS.UniformSampler.weight (samplingSpace s.val) z * e z) ≤ mesh c ^ 2 * D := by
    change (∑ z : SimpleMS.UniformSampler.Draws (samplingSpace s.val),
      SimpleMS.UniformSampler.weight (samplingSpace s.val) z *
        (RectangularRidgeCertificate.certificate (anchor c) c.atoms (depth c) (theta c) (ridge c)
          (center c s.val.point + mesh c • ownerPhysicalIncrement c.atoms c.hermitian
            (SimpleMS.UniformSampler.increment (samplingSpace s.val) z))
          (s.val.owner.physical - mesh c ^ 2 • Q s.val) -
            RectangularRidgeCertificate.certificate (anchor c) c.atoms (depth c) (theta c) (ridge c)
              (center c s.val.point) s.val.owner.physical)) ≤ _
    have hcancel := RectangularRidgeSamplerMoments.certificate_drift_eq (anchor c) c.atoms c.hermitian
      (depth c) (theta c) (ridge c) (center c s.val.point) s.val.owner.physical (samplingSpace s.val) (mesh c)
    change (∑z:Draws s.val, SimpleMS.UniformSampler.weight (samplingSpace s.val) z * e z) = _ at hcancel
    exact hcancel.le.trans hd
  change W.expectation (fun q => energyAccount c q.val) ≤ _
  nlinarith

/-- The cap premise is discharged by this run's concrete finite preparation. -/
theorem prepared_movement_energy_le (solver : RectangularDirectSolver.Service) (a : Fin d)
    (c : Config N d) (s : Certified c) (hn : ¬Stopped c (prepare solver a c s).val) :
    (movement c (prepare solver a c s) (prepare_floor solver a c s) hn).expectation
      (fun q => energyAccount c q.val) ≤ energyAccount c (prepare solver a c s).val := by
  have hc : RectangularRidgePreparationData.Cap (params c (prepare solver a c s).val.point)
      (prepare solver a c s).val.owner := by
    rw [prepare_point, prepare_owner]
    exact (prepare_certificate solver a c s).cap
  exact capped_movement_energy_le c (prepare solver a c s) (prepare_floor solver a c s) hn hc

theorem next_energy_le (solver : RectangularDirectSolver.Service) (a : Fin d)
    (c : Config N d) (s : Certified c) :
    (next solver a c s).expectation (fun q => energyAccount c q.val) ≤ energyAccount c s.val := by
  classical
  unfold next
  split
  · simp only [Sampler.expectation_pure, le_refl]
  · dsimp only
    split
    · simpa only [Sampler.expectation_pure] using prepare_energy_le solver a c s
    · exact (prepared_movement_energy_le solver a c s _).trans (prepare_energy_le solver a c s)

/-- The run begins with the actual live-projection certificate. -/
theorem output_energy_account (solver : RectangularDirectSolver.Service) (a : Fin d)
    (c : Config N d) :
    (output solver a c).expectation (fun s => energyAccount c s.val) ≤ 2 * Real.sqrt (live c : ℝ) := by
  have hm := run_account_le solver a c (fun s => energyAccount c s.val) (next_energy_le solver a c)
    (count c) (initial c)
  have hi : energyAccount c (initial c).val ≤ 2 * Real.sqrt (live c : ℝ) := by
    have hh := RectangularRidgeLiveOwnerBounds.certificate_initial_le (anchor c) c.atoms c.hermitian
      c.contractions (oldFrozen c) (depth c) (theta c) (ridge c)
    simpa only [energyAccount, energy, initial, RectangularRidgeLiveOwner.initial,
      anchor, mul_zero, add_zero, sub_zero] using hh
  exact hm.trans hi

theorem response_nonneg (c : Config N d) : 0 ≤ response c :=
  mul_nonneg (by linarith [RectangularRidgeUniformResponse.coefficient_two_le c.count_pos c.rectangular])
    (Real.sqrt_nonneg _)

theorem rounding_le (c : Config N d) (s : Certified c) : s.val.rounding ≤ margin N * live c := by
  have hc : (frozenCoordinates s.val.point \ oldFrozen c).card ≤ (Finset.univ \ oldFrozen c).card := by
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, (Finset.mem_sdiff.mp hi).2⟩
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin] at hc
  have hl : (frozenCoordinates s.val.point \ oldFrozen c).card ≤ live c := by
    simpa only [live, RectangularRidgeLiveOwner.count_eq] using hc
  exact s.property.1.rounding_le.trans
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hl) (margin_pos c).le)

theorem output_joint_moment (solver : RectangularDirectSolver.Service) (a : Fin d)
    (c : Config N d) :
    (output solver a c).expectation (fun s => energy c s.val + (threshold c / 2) * s.val.paid) ≤
      2 * Real.sqrt (live c : ℝ) + (response c + driftError) * duration c + 2 * margin N * live c := by
  have hD : 0 ≤ response c + driftError := add_nonneg (response_nonneg c) (by norm_num [driftError])
  have hp (s : Certified c) : energy c s.val + (threshold c / 2) * s.val.paid ≤
      energyAccount c s.val + ((response c + driftError) * duration c + 2 * margin N * live c) := by
    have ht := mul_le_mul_of_nonneg_left s.property.2.2 hD
    have hr := rounding_le c s
    unfold energyAccount
    linarith
  have hm := (output solver a c).expectation_mono hp
  have he : (output solver a c).expectation (fun s => energyAccount c s.val +
      ((response c + driftError) * duration c + 2 * margin N * live c)) =
        (output solver a c).expectation (fun s => energyAccount c s.val) +
          ((response c + driftError) * duration c + 2 * margin N * live c) := by
    simp only [Sampler.expectation, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      Sampler.weight_sum, one_mul]
  rw [he] at hm
  linarith [output_energy_account solver a c]

/-- The exact response duration retains an O(sqrt(live)) energy budget. -/
theorem duration_drift_le (c : Config N d) :
    (response c + driftError) * duration c ≤ Real.sqrt (live c : ℝ) := by
  have hr : 1 ≤ Real.sqrt (live c : ℝ) := Real.le_sqrt_of_sq_le (by
    have hl : (1 : ℝ) ≤ live c := by exact_mod_cast (by have := live_large c; omega : 1 ≤ live c)
    simpa using hl)
  have hB := RectangularRidgeUniformResponse.coefficient_two_le c.count_pos c.rectangular
  have he : driftError ≤ Real.sqrt (live c : ℝ) := (by norm_num [driftError] : driftError ≤ 1).trans hr
  unfold duration RectangularRidgeUniformResponse.duration response
  rw [mul_one_div]
  apply (div_le_iff₀ (by linarith : 0 < RectangularRidgeUniformResponse.coefficient N d c.count_pos + 1)).mpr
  nlinarith

theorem rounding_scale_le (c : Config N d) : 2 * margin N * live c ≤ Real.sqrt (live c : ℝ) / 50 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by have := c.count_pos; omega : 0 < N)
  have hl : (live c : ℝ) ≤ N := by exact_mod_cast live_le c
  have hr : 1 ≤ Real.sqrt (live c : ℝ) := Real.le_sqrt_of_sq_le (by
    have hℓ : (1 : ℝ) ≤ live c := by exact_mod_cast (by have := live_large c; omega : 1 ≤ live c)
    simpa using hℓ)
  have hh : 2 * margin N * live c ≤ 1 / 8192 := by
    calc
      2 * margin N * live c ≤ 2 * margin N * N := mul_le_mul_of_nonneg_left hl (by have := margin_pos c; positivity)
      _ = 1 / 8192 := by unfold margin; field_simp <;> norm_num
  linarith

theorem joint_moment (solver : RectangularDirectSolver.Service) (a : Fin d) (c : Config N d) :
    (output solver a c).expectation (fun s => energy c s.val +
      (2048 / Real.sqrt (live c : ℝ)) * s.val.paid) ≤ (151 / 50 : ℝ) * Real.sqrt (live c : ℝ) := by
  have hm := output_joint_moment solver a c
  have hp : threshold c / 2 = 2048 / Real.sqrt (live c : ℝ) := by unfold threshold; ring
  rw [hp] at hm
  linarith [duration_drift_le c, rounding_scale_le c]

end MatrixSpencer.RectangularDirectEpochMoments
