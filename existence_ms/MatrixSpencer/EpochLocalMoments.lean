import MatrixSpencer.EpochUpdate
import MatrixSpencer.EpochWalkMesh
import MatrixSpencer.OwnerSamplerCertificate
import MatrixSpencer.OwnerSamplerMoments

/-!
# The two actual conditional epoch inequalities

Every child is linked to the concrete update by its proved witness. The
analytic drift premise is supplied internally by the actual support mesh.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance epochLocalCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance epochLocalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def epochEnergyAccount (cfg : EpochConfig ι n) (s : EpochState ι) : ℝ :=
  ownerCertificate cfg.anchor cfg.matrices 1 (cfg.center s.point) s.covariance +
    (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * s.paid -
    (epochResponseConstant * Real.sqrt (Fintype.card ι : ℝ) + epochTaylorError ι) * s.time -
    2 * s.rounding

def epochTangentAccount (s : EpochState ι) : ℝ :=
  s.tangent ^ 2 - (Fintype.card ι : ℝ) * s.time

theorem epochMovedCovariance_pos {cfg : EpochConfig ι n} {s : EpochState ι}
    (hs : s.Invariant cfg) (hactive : ¬ s.Terminal) :
    (epochMovedCovariance s (cfg.step s)).PosSemidef := by
  have hpos := cfg.step_pos s hactive
  have hsmall := cfg.step_le_half s
  exact (covarianceMovement_posSemidef_range hs.covariance_pos
    (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point)
    (epochCovariance_le hs.covariance_pos _ _) (by nlinarith)).1

/-- Rounding and cleaning are charged pathwise before taking expectations. -/
theorem epochStep_energy_account_le {cfg : EpochConfig ι n} {s child : EpochState ι}
    (hs : s.Invariant cfg) (hactive : ¬ s.Terminal) (o : EpochOutcome s)
    (hw : EpochStepWitness cfg s (cfg.step s) o child) :
    epochEnergyAccount cfg child ≤ epochEnergyAccount cfg s +
      (ownerCertificate cfg.anchor cfg.matrices 1
        (cfg.center (epochMovedPoint s.covariance s.point (cfg.step s) o))
          (epochMovedCovariance s (cfg.step s)) -
        ownerCertificate cfg.anchor cfg.matrices 1 (cfg.center s.point) s.covariance) -
      (epochResponseConstant * Real.sqrt (Fintype.card ι : ℝ) + epochTaylorError ι) * cfg.step s ^ 2 := by
  have hn : ‖(cfg.center child.point : Matrix n n ℂ) -
      (cfg.center (epochMovedPoint s.covariance s.point (cfg.step s) o) : Matrix n n ℂ)‖ ≤
      epochRoundingCost cfg s (cfg.step s) o := by
    rw [hw.point_eq]
    exact epochCenter_norm_sub_le_l1 cfg _ _
  have hcert := ownerCertificate_rounding_preparation_le cfg.anchor
    (cfg.center (epochMovedPoint s.covariance s.point (cfg.step s) o)) (cfg.center child.point)
    (cfg.center (epochMovedPoint s.covariance s.point (cfg.step s) o)).property
    (cfg.center child.point).property cfg.matrices cfg.hermitian 1
    (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) (child.paid - s.paid)
    (epochRoundingCost cfg s (cfg.step s) o) (epochMovedCovariance_pos hs hactive) hw.payment hn
  unfold epochEnergyAccount
  rw [hw.time_eq, hw.rounding_eq]
  linarith

/-- The actual anchored energy, cleaning, time, and rounding account is a finite supermartingale. -/
theorem epochEnergyAccount_conditional_le {cfg : EpochConfig ι n} {s : EpochState ι}
    (hs : s.Invariant cfg) (hactive : ¬ s.Terminal)
    (child : EpochOutcome s → EpochState ι)
    (hw : ∀ o, EpochStepWitness cfg s (cfg.step s) o (child o)) :
    (∑ o : EpochOutcome s, covarianceSampleWeight
      (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point) o *
        epochEnergyAccount cfg (child o)) ≤ epochEnergyAccount cfg s := by
  let hQ := epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point
  let w := fun o : EpochOutcome s => covarianceSampleWeight hQ o
  let D := epochResponseConstant * Real.sqrt (Fintype.card ι : ℝ) + epochTaylorError ι
  let inc := fun o : EpochOutcome s =>
    ownerCertificate cfg.anchor cfg.matrices 1
      (cfg.center (epochMovedPoint s.covariance s.point (cfg.step s) o))
        (epochMovedCovariance s (cfg.step s)) -
      ownerCertificate cfg.anchor cfg.matrices 1 (cfg.center s.point) s.covariance
  have htrace := (hs.sample_trace_positive hactive).2
  have hone : (∑ o : EpochOutcome s, w o) = 1 := positive_covarianceSample_weight_sum hQ htrace
  have hbound : (∑ o : EpochOutcome s, w o * epochEnergyAccount cfg (child o)) ≤
      ∑ o : EpochOutcome s, w o * (epochEnergyAccount cfg s + inc o - D * cfg.step s ^ 2) := by
    apply Finset.sum_le_sum
    intro o _
    exact mul_le_mul_of_nonneg_left (epochStep_energy_account_le hs hactive o (hw o)) o.property.le
  have he : (∑ o : EpochOutcome s, w o *
      (epochEnergyAccount cfg s + inc o - D * cfg.step s ^ 2)) =
      epochEnergyAccount cfg s + (∑ o : EpochOutcome s, w o * inc o) - D * cfg.step s ^ 2 := by
    calc
      _ = (∑ o : EpochOutcome s, w o) * (epochEnergyAccount cfg s - D * cfg.step s ^ 2) +
          ∑ o : EpochOutcome s, w o * inc o := by
        simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro o _
        ring
      _ = _ := by rw [hone]; ring
  have hinc : (∑ o : EpochOutcome s, w o * inc o) =
      ownerSamplerDrift cfg.matrices cfg.hermitian 1 (cfg.center s.point) s.covariance hQ (cfg.step s) := by
    have hh := positive_covarianceSample_certificate_drift_eq cfg.anchor cfg.matrices cfg.hermitian
      1 (cfg.center s.point) s.covariance hQ htrace (cfg.step s)
    simpa only [w, inc, EpochConfig.center, epochMovedPoint, epochCenter_add_smul,
      epochCoordinateIncrement, ownerPhysicalIncrement, epochMovedCovariance] using hh
  rw [he, hinc] at hbound
  have hd := hs.step_drift_capped hactive
  change (∑ o : EpochOutcome s, w o * epochEnergyAccount cfg (child o)) ≤ _
  dsimp only [D] at hbound
  linarith

/-- The actual centered tangent second moment is paid by operational time. -/
theorem epochTangentAccount_conditional_le {cfg : EpochConfig ι n} {s : EpochState ι}
    (hs : s.Invariant cfg) (hactive : ¬ s.Terminal)
    (child : EpochOutcome s → EpochState ι)
    (hw : ∀ o, EpochStepWitness cfg s (cfg.step s) o (child o)) :
    (∑ o : EpochOutcome s, covarianceSampleWeight
      (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point) o *
        epochTangentAccount (child o)) ≤ epochTangentAccount s := by
  let hQ := epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point
  let w := fun o : EpochOutcome s => covarianceSampleWeight hQ o
  have htrace := (hs.sample_trace_positive hactive).2
  have hone : (∑ o : EpochOutcome s, w o) = 1 := positive_covarianceSample_weight_sum hQ htrace
  have hsq := positive_ownerCertificate_second_moment_le cfg.anchor cfg.matrices cfg.hermitian
    cfg.contractions 1 s.tangent (cfg.step s) hQ
    ((epochCovariance_le hs.covariance_pos _ _).trans hs.covariance_le_one) htrace
  have hvariance : (∑ o : EpochOutcome s, w o * (child o).tangent ^ 2) ≤
      s.tangent ^ 2 + cfg.step s ^ 2 * (Fintype.card ι : ℝ) := by
    convert hsq using 1
    apply Finset.sum_congr rfl
    intro o _
    rw [(hw o).tangent_eq]
    simp only [epochTangentIncrement, dotProduct, epochCoordinateIncrement, mul_comm]
    rfl
  have he : (∑ o : EpochOutcome s, w o * epochTangentAccount (child o)) =
      (∑ o : EpochOutcome s, w o * (child o).tangent ^ 2) -
        (Fintype.card ι : ℝ) * (s.time + cfg.step s ^ 2) := by
    simp only [epochTangentAccount, mul_sub, Finset.sum_sub_distrib]
    congr 1
    calc
      _ = (∑ o : EpochOutcome s, w o) * ((Fintype.card ι : ℝ) * (s.time + cfg.step s ^ 2)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro o _
        rw [(hw o).time_eq]
      _ = _ := by rw [hone, one_mul]
  change (∑ o : EpochOutcome s, w o * epochTangentAccount (child o)) ≤ _
  rw [he]
  unfold epochTangentAccount
  nlinarith

end MatrixSpencer
