import MatrixSpencer.EpochWalkMesh

/-!
# An actual sampled, rounded, and prepared epoch update

The state update uses the concrete covariance sampler and threshold rule.
Success from time or frozen coordinates is checked before another owner
preparation. Otherwise the actual finite dust-preparation theorem is used.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Set
noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance epochUpdateCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance epochUpdateSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

abbrev EpochOutcome (s : EpochState ι) :=
  PositiveCovarianceOutcome (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point)

def epochMovedCovariance (s : EpochState ι) (h : ℝ) : Matrix ι ι ℝ :=
  s.covariance - h ^ 2 • epochCovariance s.covariance (frozenCoordinates s.point) s.point

def epochRoundingCost (cfg : EpochConfig ι n) (s : EpochState ι) (h : ℝ) (o : EpochOutcome s) : ℝ :=
  ∑ i, |epochRoundedPoint cfg.epsilon s.covariance s.point h o i -
    epochMovedPoint s.covariance s.point h o i|

def epochTangentIncrement (cfg : EpochConfig ι n) (s : EpochState ι) (h : ℝ)
    (o : EpochOutcome s) : ℝ :=
  h * ∑ i, epochCoordinateIncrement s.covariance s.point o i *
    ownerCertificateGradient cfg.anchor cfg.matrices 1 i

def epochUpdatedState (cfg : EpochConfig ι n) (s : EpochState ι) (h : ℝ) (o : EpochOutcome s)
    (C : Matrix ι ι ℝ) (paid dust : ℝ) : EpochState ι where
  point := epochRoundedPoint cfg.epsilon s.covariance s.point h o
  covariance := C
  time := s.time + h ^ 2
  paid := s.paid + paid
  dust := s.dust + dust
  tangent := s.tangent + epochTangentIncrement cfg s h o
  rounding := s.rounding + epochRoundingCost cfg s h o

def EpochMovementStops (cfg : EpochConfig ι n) (s : EpochState ι) (h : ℝ) (o : EpochOutcome s) : Prop :=
  (Fintype.card ι : ℝ) / 64 ≤
      (frozenCoordinates (epochRoundedPoint cfg.epsilon s.covariance s.point h o)).card ∨
    epochTimeLimit ≤ s.time + h ^ 2

lemma epochUpdatedState_terminal_of_movement_stop (cfg : EpochConfig ι n) (s : EpochState ι)
    (h : ℝ) (o : EpochOutcome s) (C : Matrix ι ι ℝ) (paid dust : ℝ)
    (hstop : EpochMovementStops cfg s h o) :
    (epochUpdatedState cfg s h o C paid dust).Terminal := Or.inr hstop

omit [Nonempty n] in
lemma epochRoundingCost_nonneg (cfg : EpochConfig ι n) (s : EpochState ι) (h : ℝ)
    (o : EpochOutcome s) : 0 ≤ epochRoundingCost cfg s h o :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma epochCenter_sub (cfg : EpochConfig ι n) (x y : EuclideanSpace ℝ ι) :
    (cfg.center y : Matrix n n ℂ) - (cfg.center x : Matrix n n ℂ) =
      ∑ i, (y i - x i) • cfg.matrices i := by
  simp only [EpochConfig.center, epochCenter_coe, add_sub_add_left_eq_sub,
    ← Finset.sum_sub_distrib, sub_smul]

lemma epochCenter_norm_sub_le_l1 (cfg : EpochConfig ι n) (x y : EuclideanSpace ℝ ι) :
    ‖(cfg.center y : Matrix n n ℂ) - (cfg.center x : Matrix n n ℂ)‖ ≤ ∑ i, |y i - x i| := by
  simpa only [EpochConfig.center, epochCenter_coe, add_sub_add_left_eq_sub] using
    ThresholdRounding.combination_norm_sub_le_l1 cfg.matrices cfg.contractions
      (WithLp.ofLp x) (WithLp.ofLp y)

lemma epochTangent_difference (cfg : EpochConfig ι n) (x y : EuclideanSpace ℝ ι) :
    ownerCertificateTangent cfg.anchor 1 (cfg.center y) -
      ownerCertificateTangent cfg.anchor 1 (cfg.center x) =
      ∑ i, (y i - x i) * ownerCertificateGradient cfg.anchor cfg.matrices 1 i := by
  rw [ownerCertificateTangent_difference, epochCenter_sub]
  simp only [Matrix.mul_sum, realTrace_sum, Matrix.mul_smul, realTrace_smul, ownerCertificateGradient]

lemma epochTangent_moved_difference (cfg : EpochConfig ι n) (s : EpochState ι) (h : ℝ)
    (o : EpochOutcome s) :
    ownerCertificateTangent cfg.anchor 1 (cfg.center (epochMovedPoint s.covariance s.point h o)) -
      ownerCertificateTangent cfg.anchor 1 (cfg.center s.point) = epochTangentIncrement cfg s h o := by
  rw [epochTangent_difference]
  simp only [epochMovedPoint, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    add_sub_cancel_left, mul_assoc, ← Finset.mul_sum, epochTangentIncrement]

lemma epochTangent_rounding_error (cfg : EpochConfig ι n) (s : EpochState ι) (h : ℝ)
    (o : EpochOutcome s) :
    |ownerCertificateTangent cfg.anchor 1
        (cfg.center (epochRoundedPoint cfg.epsilon s.covariance s.point h o)) -
      ownerCertificateTangent cfg.anchor 1 (cfg.center (epochMovedPoint s.covariance s.point h o))| ≤
      epochRoundingCost cfg s h o := by
  exact (abs_ownerCertificateTangent_difference_le cfg.anchor
    (cfg.center (epochMovedPoint s.covariance s.point h o)).property
    (cfg.center (epochRoundedPoint cfg.epsilon s.covariance s.point h o)).property 1).trans
      (epochCenter_norm_sub_le_l1 cfg _ _)

/-- Exact witness of the actual movement, rounding, and optional preparation. -/
structure EpochStepWitness (cfg : EpochConfig ι n) (s : EpochState ι) (h : ℝ)
    (outcome : EpochOutcome s) (child : EpochState ι) : Prop where
  invariant : child.Invariant cfg
  point_eq : child.point = epochRoundedPoint cfg.epsilon s.covariance s.point h outcome
  time_eq : child.time = s.time + h ^ 2
  tangent_eq : child.tangent = s.tangent + epochTangentIncrement cfg s h outcome
  rounding_eq : child.rounding = s.rounding + epochRoundingCost cfg s h outcome
  covariance_le_moved : child.covariance ≤ epochMovedCovariance s h
  paid_mono : s.paid ≤ child.paid
  dust_mono : s.dust ≤ child.dust
  trace_loss_eq : realTrace (epochMovedCovariance s h - child.covariance) =
    (child.paid - s.paid) + (child.dust - s.dust)
  payment : ownerPotential (cfg.center child.point) cfg.matrices child.covariance 1 +
    (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * (child.paid - s.paid) ≤
    ownerPotential (cfg.center child.point) cfg.matrices (epochMovedCovariance s h) 1
  dust_increment_le : child.dust - s.dust ≤ epochDustThreshold *
    (((epochMovedCovariance s h).rank : ℝ) - child.covariance.rank)
  stop_before_preparation : EpochMovementStops cfg s h outcome →
    child.covariance = epochMovedCovariance s h ∧ child.paid = s.paid ∧ child.dust = s.dust

lemma epochMovedCovariance_properties {cfg : EpochConfig ι n} {s : EpochState ι}
    (hs : s.Invariant cfg) {h : ℝ} (hh : 0 ≤ h) (hhalf : h ≤ 1 / 2) :
    (epochMovedCovariance s h).PosSemidef ∧ epochMovedCovariance s h ≤ s.covariance ∧
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (epochMovedCovariance s h)).toLinearMap =
        LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) s.covariance).toLinearMap := by
  have hsq : h ^ 2 < 1 := by
    have hb := mul_nonneg hh (sub_nonneg.mpr hhalf)
    nlinarith

  exact covarianceMovement_posSemidef_range hs.covariance_pos
    (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point)
    (epochCovariance_le hs.covariance_pos (frozenCoordinates s.point) s.point) hsq

/-- Arithmetic and coordinate invariants after any actually certified owner decrease. -/
lemma epochUpdatedState_invariant {cfg : EpochConfig ι n} {s : EpochState ι}
    (hs : s.Invariant cfg) (hactive : ¬ s.Terminal) {h : ℝ} (hh : 0 ≤ h)
    (hhalf : h ≤ 1 / 2) (hsmall : h * Real.sqrt (Fintype.card ι : ℝ) ≤ cfg.epsilon)
    (htime : s.time + h ^ 2 ≤ epochTimeLimit) (o : EpochOutcome s)
    {C : Matrix ι ι ℝ} {paid dust : ℝ}
    (hC : C.PosSemidef) (hCM : C ≤ epochMovedCovariance s h)
    (hpaid : 0 ≤ paid) (hdust : 0 ≤ dust)
    (htrace : realTrace (epochMovedCovariance s h - C) = paid + dust)
    (hdbudget : dust ≤ epochDustThreshold * (((epochMovedCovariance s h).rank : ℝ) - C.rank))
    (hready : ¬ (epochUpdatedState cfg s h o C paid dust).Terminal →
      (∀ u : EuclideanSpace ℝ ι,
        u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap →
        epochDustThreshold * ‖u‖ ^ 2 ≤ inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) C u)) ∧
      realTrace (C * ownerCoefficientResponse cfg.matrices cfg.hermitian C 1
        (cfg.center (epochRoundedPoint cfg.epsilon s.covariance s.point h o))) ≤
        epochResponseConstant * Real.sqrt (Fintype.card ι : ℝ)) :
    (epochUpdatedState cfg s h o C paid dust).Invariant cfg := by
  have hmove := epochMovedCovariance_properties hs hh hhalf
  have hQle := epochCovariance_le hs.covariance_pos (frozenCoordinates s.point) s.point
  have hQtrace := realTrace_le_card_of_le_one (hQle.trans hs.covariance_le_one)
  have hregular := epochRoundedPoint_regular hs.covariance_pos hs.covariance_le_one
    hs.regular hh hsmall o.property
  have hroundnonneg := epochRoundingCost_nonneg cfg s h o
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
    have hr : ((epochMovedCovariance s h).rank : ℝ) ≤ s.covariance.rank :=
      Nat.cast_le.mpr (CovarianceDust.rank_le_of_posSemidef_le hmove.1 hmove.2.1)
    have hδ : 0 ≤ epochDustThreshold := by norm_num [epochDustThreshold]
    change s.dust + dust ≤ epochDustThreshold * ((Fintype.card ι : ℝ) - C.rank)
    nlinarith
  · have hsub := epochRoundedPoint_frozen_subset cfg.epsilon s.covariance s.point h o.property
    have hcost := epochRoundedPoint_cost_le_new_frozen hs.covariance_pos hs.covariance_le_one
      cfg.epsilon_pos.le hs.regular hh hsmall o.property
    change epochRoundingCost cfg s h o ≤ cfg.epsilon *
      ((frozenCoordinates (epochRoundedPoint cfg.epsilon s.covariance s.point h o)).card -
        (frozenCoordinates s.point).card : ℕ) at hcost
    rw [Nat.cast_sub (Finset.card_le_card hsub)] at hcost
    have hbudget := hs.rounding_budget
    change s.rounding + epochRoundingCost cfg s h o ≤ cfg.epsilon *
      (frozenCoordinates (epochRoundedPoint cfg.epsilon s.covariance s.point h o)).card
    nlinarith
  · let oldT := ownerCertificateTangent cfg.anchor 1 (cfg.center s.point)
    let movedT := ownerCertificateTangent cfg.anchor 1
      (cfg.center (epochMovedPoint s.covariance s.point h o))
    let newT := ownerCertificateTangent cfg.anchor 1
      (cfg.center (epochRoundedPoint cfg.epsilon s.covariance s.point h o))
    have hinc : movedT - oldT = epochTangentIncrement cfg s h o := epochTangent_moved_difference cfg s h o
    have hround : |newT - movedT| ≤ epochRoundingCost cfg s h o := epochTangent_rounding_error cfg s h o
    have hold : |oldT - s.tangent| ≤ s.rounding := hs.tangent_error
    change |newT - (s.tangent + epochTangentIncrement cfg s h o)| ≤
      s.rounding + epochRoundingCost cfg s h o
    have he : newT - (s.tangent + epochTangentIncrement cfg s h o) =
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

/-- Every positive sampler outcome admits an actual rounded child with certified preparation. -/
theorem exists_epoch_step {cfg : EpochConfig ι n} {s : EpochState ι}
    (hs : s.Invariant cfg) (hactive : ¬ s.Terminal) {h : ℝ} (hh : 0 < h)
    (hhalf : h ≤ 1 / 2) (hsmall : h * Real.sqrt (Fintype.card ι : ℝ) ≤ cfg.epsilon)
    (htime : s.time + h ^ 2 ≤ epochTimeLimit) (o : EpochOutcome s) :
    ∃ child : EpochState ι, EpochStepWitness cfg s h o child := by
  have hmove := epochMovedCovariance_properties hs hh.le hhalf
  by_cases hstop : EpochMovementStops cfg s h o
  · let child := epochUpdatedState cfg s h o (epochMovedCovariance s h) 0 0
    have hinv : child.Invariant cfg := epochUpdatedState_invariant hs hactive hh.le hhalf hsmall htime o
      hmove.1 le_rfl le_rfl le_rfl (by simp) (by simp) (fun hn =>
        False.elim (hn (epochUpdatedState_terminal_of_movement_stop cfg s h o _ 0 0 hstop)))
    refine ⟨child, ?_⟩
    refine {
      invariant := hinv
      point_eq := rfl
      time_eq := rfl
      tangent_eq := rfl
      rounding_eq := rfl
      covariance_le_moved := le_rfl
      paid_mono := by simp [child, epochUpdatedState]
      dust_mono := by simp [child, epochUpdatedState]
      trace_loss_eq := by simp [child, epochUpdatedState]
      payment := by simp [child, epochUpdatedState]
      dust_increment_le := by simp [child, epochUpdatedState]
      stop_before_preparation := fun _ => by simp [child, epochUpdatedState] }
  · have hk : 0 < Fintype.card ι := lt_of_lt_of_le (by norm_num : 0 < 32) cfg.count_large
    obtain ⟨C, paid, dust, hprep⟩ := exists_dust_prepared_owner
      (cfg.center (epochRoundedPoint cfg.epsilon s.covariance s.point h o))
      cfg.matrices cfg.hermitian cfg.contractions hmove.1
      (hmove.2.1.trans hs.covariance_le_one) (by norm_num : (0 : ℝ) < 1)
      (by norm_num [epochTracePriceScale] : 0 < epochTracePriceScale)
      (by norm_num [epochDustThreshold] : 0 < epochDustThreshold) hk
    let child := epochUpdatedState cfg s h o C paid dust
    have hresponse : realTrace (C * ownerCoefficientResponse cfg.matrices cfg.hermitian C 1
        (cfg.center (epochRoundedPoint cfg.epsilon s.covariance s.point h o))) ≤
        epochResponseConstant * Real.sqrt (Fintype.card ι : ℝ) := by
      apply hprep.response.trans
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      norm_num [epochTracePriceScale, epochResponseConstant]
    have hinv : child.Invariant cfg := epochUpdatedState_invariant hs hactive hh.le hhalf hsmall htime o
      hprep.covariance.1.posSemidef hprep.covariance.2 hprep.paid_nonneg hprep.dust_nonneg
      hprep.trace_account hprep.dust_budget (fun _ => ⟨hprep.floor, hresponse⟩)
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
    · simpa only [child, epochUpdatedState, add_sub_cancel_left] using hprep.trace_account
    · simpa only [child, epochUpdatedState, add_sub_cancel_left] using hprep.payment
    · simpa only [child, epochUpdatedState, add_sub_cancel_left] using hprep.dust_budget

/-- The fixed-support mesh supplies every numerical hypothesis of the actual update. -/
theorem exists_epoch_step_at_mesh {cfg : EpochConfig ι n} {s : EpochState ι}
    (hs : s.Invariant cfg) (hactive : ¬ s.Terminal) (o : EpochOutcome s) :
    ∃ child : EpochState ι, EpochStepWitness cfg s (cfg.step s) o child :=
  exists_epoch_step hs hactive (cfg.step_pos s hactive) (cfg.step_le_half s)
    (cfg.step_rounding s) (cfg.step_time_le s hactive) o

namespace EpochStepWitness

variable {cfg : EpochConfig ι n} {s child : EpochState ι} {h : ℝ} {o : EpochOutcome s}

lemma covariance_le (hw : EpochStepWitness cfg s h o child) : child.covariance ≤ s.covariance := by
  apply hw.covariance_le_moved.trans
  exact sub_le_self _ ((epochCovariance_posSemidef s.covariance
    (frozenCoordinates s.point) s.point).smul (sq_nonneg h)).nonneg

lemma frozen_preserved (hw : EpochStepWitness cfg s h o child) (i : ι)
    (hi : i ∈ frozenCoordinates s.point) : child.point i = s.point i := by
  rw [hw.point_eq]
  exact epochRoundedPoint_preserves_frozen cfg.epsilon s.covariance s.point h o.property hi

lemma frozen_subset (hw : EpochStepWitness cfg s h o child) :
    frozenCoordinates s.point ⊆ frozenCoordinates child.point := by
  rw [hw.point_eq]
  exact epochRoundedPoint_frozen_subset cfg.epsilon s.covariance s.point h o.property

lemma time_mono (hw : EpochStepWitness cfg s h o child) : s.time ≤ child.time := by
  rw [hw.time_eq]
  exact le_add_of_nonneg_right (sq_nonneg h)

lemma rounding_mono (hw : EpochStepWitness cfg s h o child) : s.rounding ≤ child.rounding := by
  rw [hw.rounding_eq]
  exact le_add_of_nonneg_right (epochRoundingCost_nonneg cfg s h o)

lemma rank_le (hw : EpochStepWitness cfg s h o child) : child.covariance.rank ≤ s.covariance.rank :=
  CovarianceDust.rank_le_of_posSemidef_le hw.invariant.covariance_pos hw.covariance_le

end EpochStepWitness

end MatrixSpencer
