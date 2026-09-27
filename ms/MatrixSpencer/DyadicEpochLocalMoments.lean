import MatrixSpencer.DyadicEpochUpdate
import MatrixSpencer.OwnerSamplerMoments

/-!
# Conditional dyadic epoch moments from the actual finite sampler

Every child is linked to the concrete update by its proved witness. The
actual potential drift bound is an explicit hypothesis; its analytic
existence remains separate. The tangent moment is discharged internally.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance dyadicEpochLocalCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicEpochLocalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def dyadicEpochEnergyAccount (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι) : ℝ :=
  dyadicOwnerCertificate cfg.anchor cfg.matrices cfg.depth cfg.weight (cfg.center s.point) s.covariance +
    (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * s.paid -
    cfg.energyRate * s.time -
    2 * s.rounding

def dyadicEpochTangentAccount (s : DyadicEpochState ι) : ℝ :=
  s.tangent ^ 2 - (Fintype.card ι : ℝ) * s.time

def dyadicEpochPotentialDrift (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι) (h : ℝ) : ℝ :=
  ∑ o : DyadicEpochOutcome s, covarianceSampleWeight
    (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point) o *
      (cfg.potential (cfg.center (epochMovedPoint s.covariance s.point h o))
        (dyadicEpochMovedCovariance s h) - cfg.potential (cfg.center s.point) s.covariance)

theorem positive_dyadicOwnerCertificate_second_moment_le
    (Hstar : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, ‖A i‖ ≤ 1) (m : ℕ) (θ M h : ℝ)
    {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef) (hQ1 : Q ≤ 1) (htrace : 0 < realTrace Q) :
    (∑ o : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ o *
      (M + h * (dyadicOwnerCertificateGradient Hstar A m θ ⬝ᵥ
        WithLp.ofLp (covarianceSampleIncrement hQ o))) ^ 2) ≤
      M ^ 2 + h ^ 2 * (Fintype.card ι : ℝ) := by
  rw [positive_covarianceSample_shifted_square hQ htrace]
  exact add_le_add_left (mul_le_mul_of_nonneg_left
    (dyadicOwnerCertificateGradient_covariance_bound Hstar A hA hN m θ hQ hQ1).2
      (sq_nonneg h)) _

theorem dyadicEpochTangentIncrement_mean_zero (cfg : DyadicEpochConfig ι n)
    (s : DyadicEpochState ι) (h : ℝ)
    (htrace : 0 < realTrace (epochCovariance s.covariance (frozenCoordinates s.point) s.point)) :
    (∑ o : DyadicEpochOutcome s, covarianceSampleWeight
      (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point) o *
        dyadicEpochTangentIncrement cfg s h o) = 0 := by
  have hh := positive_covarianceSample_linear_mean
    (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point) htrace
    (dyadicOwnerCertificateGradient cfg.anchor cfg.matrices cfg.depth cfg.weight)
  have hm := congrArg (fun x : ℝ => h * x) hh
  simpa only [Finset.mul_sum, dyadicEpochTangentIncrement, dotProduct,
    epochCoordinateIncrement, mul_zero, mul_left_comm, mul_comm, mul_assoc] using hm

theorem dyadicEpoch_certificate_drift_eq (cfg : DyadicEpochConfig ι n)
    (s : DyadicEpochState ι) (h : ℝ)
    (htrace : 0 < realTrace (epochCovariance s.covariance (frozenCoordinates s.point) s.point)) :
    (∑ o : DyadicEpochOutcome s, covarianceSampleWeight
      (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point) o *
        (dyadicOwnerCertificate cfg.anchor cfg.matrices cfg.depth cfg.weight
          (cfg.center (epochMovedPoint s.covariance s.point h o)) (dyadicEpochMovedCovariance s h) -
        dyadicOwnerCertificate cfg.anchor cfg.matrices cfg.depth cfg.weight
          (cfg.center s.point) s.covariance)) = dyadicEpochPotentialDrift cfg s h := by
  have he : ∀ o : DyadicEpochOutcome s,
      dyadicOwnerCertificate cfg.anchor cfg.matrices cfg.depth cfg.weight
          (cfg.center (epochMovedPoint s.covariance s.point h o)) (dyadicEpochMovedCovariance s h) -
        dyadicOwnerCertificate cfg.anchor cfg.matrices cfg.depth cfg.weight
          (cfg.center s.point) s.covariance =
      (cfg.potential (cfg.center (epochMovedPoint s.covariance s.point h o))
        (dyadicEpochMovedCovariance s h) - cfg.potential (cfg.center s.point) s.covariance) -
          dyadicEpochTangentIncrement cfg s h o := by
    intro o
    have ht := dyadicEpochTangent_moved_difference cfg s h o
    unfold dyadicOwnerCertificate DyadicEpochConfig.potential
    linarith
  simp_rw [he, mul_sub]
  rw [Finset.sum_sub_distrib, dyadicEpochTangentIncrement_mean_zero cfg s h htrace, sub_zero]
  simp only [dyadicEpochPotentialDrift, mul_sub]

/-- Rounding and cleaning are charged pathwise before taking expectations. -/
theorem dyadicEpochStep_energy_account_le {cfg : DyadicEpochConfig ι n} {s child : DyadicEpochState ι}
    (hs : s.Invariant cfg) {h : ℝ} (hh : 0 ≤ h) (hhalf : h ≤ 1 / 2) (o : DyadicEpochOutcome s)
    (hw : DyadicEpochStepWitness cfg s (h) o child) :
    dyadicEpochEnergyAccount cfg child ≤ dyadicEpochEnergyAccount cfg s +
      (dyadicOwnerCertificate cfg.anchor cfg.matrices cfg.depth cfg.weight
        (cfg.center (epochMovedPoint s.covariance s.point (h) o))
          (dyadicEpochMovedCovariance s (h)) -
        dyadicOwnerCertificate cfg.anchor cfg.matrices cfg.depth cfg.weight (cfg.center s.point) s.covariance) -
      cfg.energyRate * h ^ 2 := by
  have hn : ‖(cfg.center child.point : Matrix n n ℂ) -
      (cfg.center (epochMovedPoint s.covariance s.point (h) o) : Matrix n n ℂ)‖ ≤
      dyadicEpochRoundingCost cfg s (h) o := by
    rw [hw.point_eq]
    exact dyadicEpochCenter_norm_sub_le_l1 cfg _ _
  have hcert := dyadicOwnerCertificate_rounding_preparation_le cfg.anchor
    (cfg.center (epochMovedPoint s.covariance s.point (h) o)) (cfg.center child.point)
    (cfg.center (epochMovedPoint s.covariance s.point (h) o)).property
    (cfg.center child.point).property cfg.matrices cfg.hermitian cfg.depth cfg.weight
    (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) (child.paid - s.paid)
    (dyadicEpochRoundingCost cfg s (h) o) (dyadicEpochMovedCovariance_properties hs hh hhalf).1 hw.payment hn
  unfold dyadicEpochEnergyAccount
  rw [hw.time_eq, hw.rounding_eq]
  linarith

/-- The actual anchored energy, cleaning, time, and rounding account is a finite supermartingale. -/
theorem dyadicEpochEnergyAccount_conditional_le {cfg : DyadicEpochConfig ι n} {s : DyadicEpochState ι}
    (hs : s.Invariant cfg) (hactive : ¬ s.Terminal cfg) (h : ℝ) (hh : 0 ≤ h) (hhalf : h ≤ 1 / 2)
    (child : DyadicEpochOutcome s → DyadicEpochState ι)
    (hw : ∀ o, DyadicEpochStepWitness cfg s (h) o (child o))
    (hdrift : dyadicEpochPotentialDrift cfg s h ≤ cfg.energyRate * h ^ 2) :
    (∑ o : DyadicEpochOutcome s, covarianceSampleWeight
      (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point) o *
        dyadicEpochEnergyAccount cfg (child o)) ≤ dyadicEpochEnergyAccount cfg s := by
  let hQ := epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point
  let w := fun o : DyadicEpochOutcome s => covarianceSampleWeight hQ o
  let D := cfg.energyRate
  let inc := fun o : DyadicEpochOutcome s =>
    dyadicOwnerCertificate cfg.anchor cfg.matrices cfg.depth cfg.weight
      (cfg.center (epochMovedPoint s.covariance s.point (h) o))
        (dyadicEpochMovedCovariance s (h)) -
      dyadicOwnerCertificate cfg.anchor cfg.matrices cfg.depth cfg.weight (cfg.center s.point) s.covariance
  have htrace := (hs.sample_trace_positive hactive).2
  have hone : (∑ o : DyadicEpochOutcome s, w o) = 1 := positive_covarianceSample_weight_sum hQ htrace
  have hbound : (∑ o : DyadicEpochOutcome s, w o * dyadicEpochEnergyAccount cfg (child o)) ≤
      ∑ o : DyadicEpochOutcome s, w o * (dyadicEpochEnergyAccount cfg s + inc o - D * h ^ 2) := by
    apply Finset.sum_le_sum
    intro o _
    exact mul_le_mul_of_nonneg_left (dyadicEpochStep_energy_account_le hs hh hhalf o (hw o)) o.property.le
  have he : (∑ o : DyadicEpochOutcome s, w o *
      (dyadicEpochEnergyAccount cfg s + inc o - D * h ^ 2)) =
      dyadicEpochEnergyAccount cfg s + (∑ o : DyadicEpochOutcome s, w o * inc o) - D * h ^ 2 := by
    calc
      _ = (∑ o : DyadicEpochOutcome s, w o) * (dyadicEpochEnergyAccount cfg s - D * h ^ 2) +
          ∑ o : DyadicEpochOutcome s, w o * inc o := by
        simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro o _
        ring
      _ = _ := by rw [hone]; ring
  have hinc : (∑ o : DyadicEpochOutcome s, w o * inc o) =
      dyadicEpochPotentialDrift cfg s h := dyadicEpoch_certificate_drift_eq cfg s h htrace
  rw [he, hinc] at hbound
  change (∑ o : DyadicEpochOutcome s, w o * dyadicEpochEnergyAccount cfg (child o)) ≤ _
  dsimp only [D] at hbound
  linarith

/-- The actual centered tangent second moment is paid by operational time. -/
theorem dyadicEpochTangentAccount_conditional_le {cfg : DyadicEpochConfig ι n} {s : DyadicEpochState ι}
    (hs : s.Invariant cfg) (hactive : ¬ s.Terminal cfg) (h : ℝ)
    (child : DyadicEpochOutcome s → DyadicEpochState ι)
    (hw : ∀ o, DyadicEpochStepWitness cfg s (h) o (child o)) :
    (∑ o : DyadicEpochOutcome s, covarianceSampleWeight
      (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point) o *
        dyadicEpochTangentAccount (child o)) ≤ dyadicEpochTangentAccount s := by
  let hQ := epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point
  let w := fun o : DyadicEpochOutcome s => covarianceSampleWeight hQ o
  have htrace := (hs.sample_trace_positive hactive).2
  have hone : (∑ o : DyadicEpochOutcome s, w o) = 1 := positive_covarianceSample_weight_sum hQ htrace
  have hsq := positive_dyadicOwnerCertificate_second_moment_le cfg.anchor cfg.matrices cfg.hermitian
    cfg.contractions cfg.depth cfg.weight s.tangent (h) hQ
    ((epochCovariance_le hs.covariance_pos _ _).trans hs.covariance_le_one) htrace
  have hvariance : (∑ o : DyadicEpochOutcome s, w o * (child o).tangent ^ 2) ≤
      s.tangent ^ 2 + h ^ 2 * (Fintype.card ι : ℝ) := by
    convert hsq using 1
    apply Finset.sum_congr rfl
    intro o _
    rw [(hw o).tangent_eq]
    simp only [dyadicEpochTangentIncrement, dotProduct, epochCoordinateIncrement, mul_comm]
    rfl
  have he : (∑ o : DyadicEpochOutcome s, w o * dyadicEpochTangentAccount (child o)) =
      (∑ o : DyadicEpochOutcome s, w o * (child o).tangent ^ 2) -
        (Fintype.card ι : ℝ) * (s.time + h ^ 2) := by
    simp only [dyadicEpochTangentAccount, mul_sub, Finset.sum_sub_distrib]
    congr 1
    calc
      _ = (∑ o : DyadicEpochOutcome s, w o) * ((Fintype.card ι : ℝ) * (s.time + h ^ 2)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro o _
        rw [(hw o).time_eq]
      _ = _ := by rw [hone, one_mul]
  change (∑ o : DyadicEpochOutcome s, w o * dyadicEpochTangentAccount (child o)) ≤ _
  rw [he]
  unfold dyadicEpochTangentAccount
  nlinarith

end MatrixSpencer
