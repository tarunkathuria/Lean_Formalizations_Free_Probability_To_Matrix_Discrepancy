import MatrixSpencer.DyadicEpochState
import MatrixSpencer.PositiveCovarianceSampler

/-!
# Exact sampled and rounded dyadic epoch bookkeeping

The state update uses the concrete covariance sampler and threshold rule.
The preparation and response facts remain explicit assumptions of the
invariant-preservation theorem; no analytic step is assumed to exist.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Set
noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance dyadicEpochUpdateCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicEpochUpdateSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

abbrev DyadicEpochOutcome (s : DyadicEpochState ι) :=
  PositiveCovarianceOutcome (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point)

def dyadicEpochMovedCovariance (s : DyadicEpochState ι) (h : ℝ) : Matrix ι ι ℝ :=
  s.covariance - h ^ 2 • epochCovariance s.covariance (frozenCoordinates s.point) s.point

def dyadicEpochRoundingCost (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι) (h : ℝ) (o : DyadicEpochOutcome s) : ℝ :=
  ∑ i, |epochRoundedPoint cfg.epsilon s.covariance s.point h o i -
    epochMovedPoint s.covariance s.point h o i|

def dyadicEpochTangentIncrement (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι) (h : ℝ)
    (o : DyadicEpochOutcome s) : ℝ :=
  h * ∑ i, epochCoordinateIncrement s.covariance s.point o i *
    dyadicOwnerCertificateGradient cfg.anchor cfg.matrices cfg.depth cfg.weight i

def dyadicEpochUpdatedState (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι) (h : ℝ) (o : DyadicEpochOutcome s)
    (C : Matrix ι ι ℝ) (paid dust : ℝ) : DyadicEpochState ι where
  point := epochRoundedPoint cfg.epsilon s.covariance s.point h o
  covariance := C
  time := s.time + h ^ 2
  paid := s.paid + paid
  dust := s.dust + dust
  tangent := s.tangent + dyadicEpochTangentIncrement cfg s h o
  rounding := s.rounding + dyadicEpochRoundingCost cfg s h o

def DyadicEpochMovementStops (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι) (h : ℝ) (o : DyadicEpochOutcome s) : Prop :=
  (Fintype.card ι : ℝ) / 64 ≤
      (frozenCoordinates (epochRoundedPoint cfg.epsilon s.covariance s.point h o)).card ∨
    cfg.duration ≤ s.time + h ^ 2

lemma dyadicEpochUpdatedState_terminal_of_movement_stop (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι)
    (h : ℝ) (o : DyadicEpochOutcome s) (C : Matrix ι ι ℝ) (paid dust : ℝ)
    (hstop : DyadicEpochMovementStops cfg s h o) :
    (dyadicEpochUpdatedState cfg s h o C paid dust).Terminal cfg := Or.inr hstop

omit [Nonempty n] in
lemma dyadicEpochRoundingCost_nonneg (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι) (h : ℝ)
    (o : DyadicEpochOutcome s) : 0 ≤ dyadicEpochRoundingCost cfg s h o :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma dyadicEpochCenter_sub (cfg : DyadicEpochConfig ι n) (x y : EuclideanSpace ℝ ι) :
    (cfg.center y : Matrix n n ℂ) - (cfg.center x : Matrix n n ℂ) =
      ∑ i, (y i - x i) • cfg.matrices i := by
  simp only [DyadicEpochConfig.center, EpochConfig.center, epochCenter_coe, add_sub_add_left_eq_sub,
    ← Finset.sum_sub_distrib, sub_smul]

lemma dyadicEpochCenter_norm_sub_le_l1 (cfg : DyadicEpochConfig ι n) (x y : EuclideanSpace ℝ ι) :
    ‖(cfg.center y : Matrix n n ℂ) - (cfg.center x : Matrix n n ℂ)‖ ≤ ∑ i, |y i - x i| := by
  simpa only [DyadicEpochConfig.center, EpochConfig.center, epochCenter_coe, add_sub_add_left_eq_sub] using
    ThresholdRounding.combination_norm_sub_le_l1 cfg.matrices cfg.contractions
      (WithLp.ofLp x) (WithLp.ofLp y)

lemma dyadicEpochTangent_difference (cfg : DyadicEpochConfig ι n) (x y : EuclideanSpace ℝ ι) :
    dyadicOwnerCertificateTangent cfg.anchor cfg.depth cfg.weight (cfg.center y) -
      dyadicOwnerCertificateTangent cfg.anchor cfg.depth cfg.weight (cfg.center x) =
      ∑ i, (y i - x i) * dyadicOwnerCertificateGradient cfg.anchor cfg.matrices cfg.depth cfg.weight i := by
  rw [dyadicOwnerCertificateTangent_difference, dyadicEpochCenter_sub]
  simp only [Matrix.mul_sum, realTrace_sum, Matrix.mul_smul, realTrace_smul, dyadicOwnerCertificateGradient]

lemma dyadicEpochTangent_moved_difference (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι) (h : ℝ)
    (o : DyadicEpochOutcome s) :
    dyadicOwnerCertificateTangent cfg.anchor cfg.depth cfg.weight (cfg.center (epochMovedPoint s.covariance s.point h o)) -
      dyadicOwnerCertificateTangent cfg.anchor cfg.depth cfg.weight (cfg.center s.point) = dyadicEpochTangentIncrement cfg s h o := by
  rw [dyadicEpochTangent_difference]
  simp only [epochMovedPoint, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    add_sub_cancel_left, mul_assoc, ← Finset.mul_sum, dyadicEpochTangentIncrement]

lemma dyadicEpochTangent_rounding_error (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι) (h : ℝ)
    (o : DyadicEpochOutcome s) :
    |dyadicOwnerCertificateTangent cfg.anchor cfg.depth cfg.weight
        (cfg.center (epochRoundedPoint cfg.epsilon s.covariance s.point h o)) -
      dyadicOwnerCertificateTangent cfg.anchor cfg.depth cfg.weight (cfg.center (epochMovedPoint s.covariance s.point h o))| ≤
      dyadicEpochRoundingCost cfg s h o := by
  exact (abs_dyadicOwnerCertificateTangent_difference_le cfg.anchor
    (cfg.center (epochMovedPoint s.covariance s.point h o)).property
    (cfg.center (epochRoundedPoint cfg.epsilon s.covariance s.point h o)).property cfg.depth cfg.weight).trans
      (dyadicEpochCenter_norm_sub_le_l1 cfg _ _)

/-- Exact witness of the actual movement, rounding, and optional preparation. -/
structure DyadicEpochStepWitness (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι) (h : ℝ)
    (outcome : DyadicEpochOutcome s) (child : DyadicEpochState ι) : Prop where
  invariant : child.Invariant cfg
  point_eq : child.point = epochRoundedPoint cfg.epsilon s.covariance s.point h outcome
  time_eq : child.time = s.time + h ^ 2
  tangent_eq : child.tangent = s.tangent + dyadicEpochTangentIncrement cfg s h outcome
  rounding_eq : child.rounding = s.rounding + dyadicEpochRoundingCost cfg s h outcome
  covariance_le_moved : child.covariance ≤ dyadicEpochMovedCovariance s h
  paid_mono : s.paid ≤ child.paid
  dust_mono : s.dust ≤ child.dust
  trace_loss_eq : realTrace (dyadicEpochMovedCovariance s h - child.covariance) =
    (child.paid - s.paid) + (child.dust - s.dust)
  payment : cfg.potential (cfg.center child.point) child.covariance +
    (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * (child.paid - s.paid) ≤
    cfg.potential (cfg.center child.point) (dyadicEpochMovedCovariance s h)
  dust_increment_le : child.dust - s.dust ≤ epochDustThreshold *
    (((dyadicEpochMovedCovariance s h).rank : ℝ) - child.covariance.rank)
  stop_before_preparation : DyadicEpochMovementStops cfg s h outcome →
    child.covariance = dyadicEpochMovedCovariance s h ∧ child.paid = s.paid ∧ child.dust = s.dust

lemma dyadicEpochMovedCovariance_properties {cfg : DyadicEpochConfig ι n} {s : DyadicEpochState ι}
    (hs : s.Invariant cfg) {h : ℝ} (hh : 0 ≤ h) (hhalf : h ≤ 1 / 2) :
    (dyadicEpochMovedCovariance s h).PosSemidef ∧ dyadicEpochMovedCovariance s h ≤ s.covariance ∧
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (dyadicEpochMovedCovariance s h)).toLinearMap =
        LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) s.covariance).toLinearMap := by
  have hsq : h ^ 2 < 1 := by
    have hb := mul_nonneg hh (sub_nonneg.mpr hhalf)
    nlinarith

  exact covarianceMovement_posSemidef_range hs.covariance_pos
    (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point)
    (epochCovariance_le hs.covariance_pos (frozenCoordinates s.point) s.point) hsq

/-- Arithmetic and coordinate invariants after any actually certified owner decrease. -/
lemma dyadicEpochUpdatedState_invariant {cfg : DyadicEpochConfig ι n} {s : DyadicEpochState ι}
    (hs : s.Invariant cfg) (hactive : ¬ s.Terminal cfg) {h : ℝ} (hh : 0 ≤ h)
    (hhalf : h ≤ 1 / 2) (hsmall : h * Real.sqrt (Fintype.card ι : ℝ) ≤ cfg.epsilon)
    (htime : s.time + h ^ 2 ≤ cfg.duration) (o : DyadicEpochOutcome s)
    {C : Matrix ι ι ℝ} {paid dust : ℝ}
    (hC : C.PosSemidef) (hCM : C ≤ dyadicEpochMovedCovariance s h)
    (hpaid : 0 ≤ paid) (hdust : 0 ≤ dust)
    (htrace : realTrace (dyadicEpochMovedCovariance s h - C) = paid + dust)
    (hdbudget : dust ≤ epochDustThreshold * (((dyadicEpochMovedCovariance s h).rank : ℝ) - C.rank))
    (hready : ¬ (dyadicEpochUpdatedState cfg s h o C paid dust).Terminal cfg →
      (∀ u : EuclideanSpace ℝ ι,
        u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap →
        epochDustThreshold * ‖u‖ ^ 2 ≤ inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) C u)) ∧
      realTrace (C * dyadicOwnerCoefficientResponse cfg.matrices cfg.hermitian C cfg.depth cfg.weight
        (cfg.center (epochRoundedPoint cfg.epsilon s.covariance s.point h o))) ≤
        cfg.responseCoefficient * Real.sqrt (Fintype.card ι : ℝ)) :
    (dyadicEpochUpdatedState cfg s h o C paid dust).Invariant cfg := by
  have hmove := dyadicEpochMovedCovariance_properties hs hh hhalf
  have hQle := epochCovariance_le hs.covariance_pos (frozenCoordinates s.point) s.point
  have hQtrace := realTrace_le_card_of_le_one (hQle.trans hs.covariance_le_one)
  have hregular := epochRoundedPoint_regular hs.covariance_pos hs.covariance_le_one
    hs.regular hh hsmall o.property
  have hroundnonneg := dyadicEpochRoundingCost_nonneg cfg s h o
  refine {
    regular := hregular
    covariance_pos := hC
    covariance_le_one := hCM.trans (hmove.2.1.trans hs.covariance_le_one)
    time_nonneg := add_nonneg hs.time_nonneg (sq_nonneg h)
    time_le := htime
    paid_nonneg := add_nonneg hs.paid_nonneg hpaid
    dust_nonneg := add_nonneg hs.dust_nonneg hdust
    rounding_nonneg := add_nonneg hs.rounding_nonneg hroundnonneg
    trace_ledger := ?_
    dust_budget := ?_
    rounding_budget := ?_
    tangent_error := ?_
    norm_progress := ?_
    ready := hready }
  · have hledger := hs.trace_ledger
    have hcost := htrace
    rw [realTrace_sub] at hcost
    change realTrace (s.covariance - h ^ 2 •
      epochCovariance s.covariance (frozenCoordinates s.point) s.point) - realTrace C = paid + dust at hcost
    rw [covarianceMovement_trace] at hcost
    have hdecrement := mul_le_mul_of_nonneg_left hQtrace (sq_nonneg h)
    change (Fintype.card ι : ℝ) * (1 - (s.time + h ^ 2)) -
      (s.paid + paid) - (s.dust + dust) ≤ realTrace C
    nlinarith
  · have hbudget := hs.dust_budget
    have hr : ((dyadicEpochMovedCovariance s h).rank : ℝ) ≤ s.covariance.rank :=
      Nat.cast_le.mpr (CovarianceDust.rank_le_of_posSemidef_le hmove.1 hmove.2.1)
    have hδ : 0 ≤ epochDustThreshold := by norm_num [epochDustThreshold]
    change s.dust + dust ≤ epochDustThreshold * ((Fintype.card ι : ℝ) - C.rank)
    nlinarith
  · have hsub := epochRoundedPoint_frozen_subset cfg.epsilon s.covariance s.point h o.property
    have hcost := epochRoundedPoint_cost_le_new_frozen hs.covariance_pos hs.covariance_le_one
      cfg.epsilon_pos.le hs.regular hh hsmall o.property
    change dyadicEpochRoundingCost cfg s h o ≤ cfg.epsilon *
      ((frozenCoordinates (epochRoundedPoint cfg.epsilon s.covariance s.point h o)).card -
        (frozenCoordinates s.point).card : ℕ) at hcost
    rw [Nat.cast_sub (Finset.card_le_card hsub)] at hcost
    have hbudget := hs.rounding_budget
    change s.rounding + dyadicEpochRoundingCost cfg s h o ≤ cfg.epsilon *
      (frozenCoordinates (epochRoundedPoint cfg.epsilon s.covariance s.point h o)).card
    nlinarith
  · let oldT := dyadicOwnerCertificateTangent cfg.anchor cfg.depth cfg.weight (cfg.center s.point)
    let movedT := dyadicOwnerCertificateTangent cfg.anchor cfg.depth cfg.weight
      (cfg.center (epochMovedPoint s.covariance s.point h o))
    let newT := dyadicOwnerCertificateTangent cfg.anchor cfg.depth cfg.weight
      (cfg.center (epochRoundedPoint cfg.epsilon s.covariance s.point h o))
    have hinc : movedT - oldT = dyadicEpochTangentIncrement cfg s h o := dyadicEpochTangent_moved_difference cfg s h o
    have hround : |newT - movedT| ≤ dyadicEpochRoundingCost cfg s h o := dyadicEpochTangent_rounding_error cfg s h o
    have hold : |oldT - s.tangent| ≤ s.rounding := hs.tangent_error
    change |newT - (s.tangent + dyadicEpochTangentIncrement cfg s h o)| ≤
      s.rounding + dyadicEpochRoundingCost cfg s h o
    have he : newT - (s.tangent + dyadicEpochTangentIncrement cfg s h o) =
        (newT - movedT) + (oldT - s.tangent) := by linarith
    rw [he]
    exact (abs_add_le _ _).trans (by linarith)
  · have hnorm := epochRoundedPoint_norm_gain hs.covariance_pos hs.covariance_le_one
      hs.regular hh hsmall o.property
    have htraceQ := (hs.sample_trace_positive hactive).1
    have hgain := mul_le_mul_of_nonneg_left htraceQ (sq_nonneg h)
    have hprogress := hs.norm_progress
    change ‖cfg.start‖ ^ 2 + (Fintype.card ι : ℝ) / 16 * (s.time + h ^ 2) ≤
      ‖epochRoundedPoint cfg.epsilon s.covariance s.point h o‖ ^ 2
    nlinarith


/-- Given concrete preparation for a continuing branch, the actual child exists. -/
theorem exists_dyadic_epoch_step_of_preparation {cfg : DyadicEpochConfig ι n} {s : DyadicEpochState ι}
    (hs : s.Invariant cfg) (hactive : ¬ s.Terminal cfg) {h : ℝ} (hh : 0 < h)
    (hhalf : h ≤ 1 / 2) (hsmall : h * Real.sqrt (Fintype.card ι : ℝ) ≤ cfg.epsilon)
    (htime : s.time + h ^ 2 ≤ cfg.duration) (o : DyadicEpochOutcome s)
    (hprepare : ¬ DyadicEpochMovementStops cfg s h o →
      ∃ C paid dust, DyadicPreparedCovariance cfg
        (cfg.center (epochRoundedPoint cfg.epsilon s.covariance s.point h o))
        (dyadicEpochMovedCovariance s h) C paid dust) :
    ∃ child : DyadicEpochState ι, DyadicEpochStepWitness cfg s h o child := by
  have hmove := dyadicEpochMovedCovariance_properties hs hh.le hhalf
  by_cases hstop : DyadicEpochMovementStops cfg s h o
  · let child := dyadicEpochUpdatedState cfg s h o (dyadicEpochMovedCovariance s h) 0 0
    have hinv : child.Invariant cfg := dyadicEpochUpdatedState_invariant hs hactive hh.le hhalf hsmall htime o
      hmove.1 le_rfl le_rfl le_rfl (by simp) (by simp) (fun hn =>
        False.elim (hn (dyadicEpochUpdatedState_terminal_of_movement_stop cfg s h o _ 0 0 hstop)))
    refine ⟨child, ?_⟩
    refine {
      invariant := hinv
      point_eq := rfl
      time_eq := rfl
      tangent_eq := rfl
      rounding_eq := rfl
      covariance_le_moved := le_rfl
      paid_mono := by simp [child, dyadicEpochUpdatedState]
      dust_mono := by simp [child, dyadicEpochUpdatedState]
      trace_loss_eq := by simp [child, dyadicEpochUpdatedState]
      payment := by simp [child, dyadicEpochUpdatedState]
      dust_increment_le := by simp [child, dyadicEpochUpdatedState]
      stop_before_preparation := fun _ => by simp [child, dyadicEpochUpdatedState] }
  · obtain ⟨C, paid, dust, hprep⟩ := hprepare hstop
    let child := dyadicEpochUpdatedState cfg s h o C paid dust
    have hinv : child.Invariant cfg := dyadicEpochUpdatedState_invariant hs hactive hh.le hhalf hsmall htime o
      hprep.covariance.1.posSemidef hprep.covariance.2 hprep.paid_nonneg hprep.dust_nonneg
      hprep.trace_account hprep.dust_budget (fun _ => ⟨hprep.floor, hprep.response⟩)
    refine ⟨child, ?_⟩
    refine {
      invariant := hinv
      point_eq := rfl
      time_eq := rfl
      tangent_eq := rfl
      rounding_eq := rfl
      covariance_le_moved := hprep.covariance.2
      paid_mono := le_add_of_nonneg_right hprep.paid_nonneg
      dust_mono := le_add_of_nonneg_right hprep.dust_nonneg
      trace_loss_eq := ?_
      payment := ?_
      dust_increment_le := ?_
      stop_before_preparation := fun h => False.elim (hstop h) }
    · simpa only [child, dyadicEpochUpdatedState, add_sub_cancel_left] using hprep.trace_account
    · simpa only [child, dyadicEpochUpdatedState, add_sub_cancel_left] using hprep.payment
    · simpa only [child, dyadicEpochUpdatedState, add_sub_cancel_left] using hprep.dust_budget

namespace DyadicEpochStepWitness

variable {cfg : DyadicEpochConfig ι n} {s child : DyadicEpochState ι} {h : ℝ} {o : DyadicEpochOutcome s}

lemma covariance_le (hw : DyadicEpochStepWitness cfg s h o child) : child.covariance ≤ s.covariance := by
  apply hw.covariance_le_moved.trans
  exact sub_le_self _ ((epochCovariance_posSemidef s.covariance
    (frozenCoordinates s.point) s.point).smul (sq_nonneg h)).nonneg

lemma frozen_preserved (hw : DyadicEpochStepWitness cfg s h o child) (i : ι)
    (hi : i ∈ frozenCoordinates s.point) : child.point i = s.point i := by
  rw [hw.point_eq]
  exact epochRoundedPoint_preserves_frozen cfg.epsilon s.covariance s.point h o.property hi

lemma frozen_subset (hw : DyadicEpochStepWitness cfg s h o child) :
    frozenCoordinates s.point ⊆ frozenCoordinates child.point := by
  rw [hw.point_eq]
  exact epochRoundedPoint_frozen_subset cfg.epsilon s.covariance s.point h o.property

lemma time_mono (hw : DyadicEpochStepWitness cfg s h o child) : s.time ≤ child.time := by
  rw [hw.time_eq]
  exact le_add_of_nonneg_right (sq_nonneg h)

lemma rounding_mono (hw : DyadicEpochStepWitness cfg s h o child) : s.rounding ≤ child.rounding := by
  rw [hw.rounding_eq]
  exact le_add_of_nonneg_right (dyadicEpochRoundingCost_nonneg cfg s h o)

lemma rank_le (hw : DyadicEpochStepWitness cfg s h o child) : child.covariance.rank ≤ s.covariance.rank :=
  CovarianceDust.rank_le_of_posSemidef_le hw.invariant.covariance_pos hw.covariance_le

end DyadicEpochStepWitness

end MatrixSpencer
