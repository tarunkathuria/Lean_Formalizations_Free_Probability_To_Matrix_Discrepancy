import MatrixSpencer.DyadicOwnerCertificate
import MatrixSpencer.DyadicCoefficientResponse
import MatrixSpencer.EpochState
import MatrixSpencer.RectangularEpochParameters

/-!
# Concrete finite epoch data with a fixed dyadic regularizer and duration

The response budget is part of the explicit state invariant. This module
constructs no analytic preparation and asserts no existence of an epoch.
-/
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Set
noncomputable section
namespace MatrixSpencer
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance dyadicEpochStateCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicEpochStateSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

structure DyadicEpochConfig (ι n : Type*) [Fintype ι] [Fintype n] [DecidableEq n]
    extends EpochConfig ι n where
  depth : ℕ
  depth_positive : 1 ≤ depth
  weight : ℝ
  weight_positive : 0 < weight
  responseCoefficient : ℝ
  response_large : 2 ≤ responseCoefficient

def DyadicEpochConfig.center (cfg : DyadicEpochConfig ι n) (x : EuclideanSpace ℝ ι) :
    selfAdjoint (Matrix n n ℂ) := cfg.toEpochConfig.center x

def DyadicEpochConfig.anchor (cfg : DyadicEpochConfig ι n) : Matrix n n ℂ := cfg.center cfg.start

def DyadicEpochConfig.duration (cfg : DyadicEpochConfig ι n) : ℝ :=
  RectangularEpochParameters.duration cfg.responseCoefficient

def DyadicEpochConfig.potential (cfg : DyadicEpochConfig ι n) (H : Matrix n n ℂ)
    (C : Matrix ι ι ℝ) : ℝ :=
  regularizedOwnerPotential H cfg.matrices C (dyadicTsallisRegularizer cfg.depth cfg.weight)

def DyadicEpochConfig.energyRate (cfg : DyadicEpochConfig ι n) : ℝ :=
  RectangularEpochParameters.energyRate cfg.responseCoefficient (Fintype.card ι : ℝ)

omit [DecidableEq ι] [Nonempty n] in
theorem DyadicEpochConfig.duration_pos (cfg : DyadicEpochConfig ι n) : 0 < cfg.duration :=
  RectangularEpochParameters.duration_pos cfg.response_large

omit [DecidableEq ι] [Nonempty n] in
theorem DyadicEpochConfig.duration_le_half (cfg : DyadicEpochConfig ι n) : cfg.duration ≤ 1 / 2 :=
  (RectangularEpochParameters.duration_le_third cfg.response_large).trans (by norm_num)

/-- Concrete preparation data; its analytic existence remains a separate theorem. -/
structure DyadicPreparedCovariance (cfg : DyadicEpochConfig ι n)
    (H : selfAdjoint (Matrix n n ℂ)) (upper C : Matrix ι ι ℝ) (paid dust : ℝ) : Prop where
  covariance : C ∈ Icc 0 upper
  paid_nonneg : 0 ≤ paid
  dust_nonneg : 0 ≤ dust
  trace_account : realTrace (upper - C) = paid + dust
  dust_budget : dust ≤ epochDustThreshold * ((upper.rank : ℝ) - C.rank)
  payment : cfg.potential H C +
    (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * paid ≤ cfg.potential H upper
  floor : ∀ u : EuclideanSpace ℝ ι,
    u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap →
    epochDustThreshold * ‖u‖ ^ 2 ≤ inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) C u)
  response : realTrace (C * dyadicOwnerCoefficientResponse cfg.matrices cfg.hermitian C
    cfg.depth cfg.weight H) ≤ cfg.responseCoefficient * Real.sqrt (Fintype.card ι : ℝ)

structure DyadicEpochState (ι : Type*) [Fintype ι] where
  point : EuclideanSpace ℝ ι
  covariance : Matrix ι ι ℝ
  time : ℝ
  paid : ℝ
  dust : ℝ
  tangent : ℝ
  rounding : ℝ

def DyadicEpochState.Terminal (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι) : Prop :=
  (Fintype.card ι : ℝ) / 64 < s.paid + s.dust ∨
    (Fintype.card ι : ℝ) / 64 ≤ (frozenCoordinates s.point).card ∨ cfg.duration ≤ s.time

structure DyadicEpochState.Invariant (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι) : Prop where
  regular : CubeRegular cfg.epsilon s.point
  covariance_pos : s.covariance.PosSemidef
  covariance_le_one : s.covariance ≤ 1
  time_nonneg : 0 ≤ s.time
  time_le : s.time ≤ cfg.duration
  paid_nonneg : 0 ≤ s.paid
  dust_nonneg : 0 ≤ s.dust
  rounding_nonneg : 0 ≤ s.rounding
  trace_ledger : (Fintype.card ι : ℝ) * (1 - s.time) - s.paid - s.dust ≤ realTrace s.covariance
  dust_budget : s.dust ≤ epochDustThreshold *
    ((Fintype.card ι : ℝ) - (s.covariance.rank : ℝ))
  rounding_budget : s.rounding ≤ cfg.epsilon * (frozenCoordinates s.point).card
  tangent_error : |dyadicOwnerCertificateTangent cfg.anchor cfg.depth cfg.weight (cfg.center s.point) - s.tangent| ≤ s.rounding
  norm_progress : ‖cfg.start‖ ^ 2 + (Fintype.card ι : ℝ) / 16 * s.time ≤ ‖s.point‖ ^ 2
  ready : ¬ s.Terminal cfg →
    (∀ u : EuclideanSpace ℝ ι,
      u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) s.covariance).toLinearMap →
      epochDustThreshold * ‖u‖ ^ 2 ≤ inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) s.covariance u)) ∧
    realTrace (s.covariance * dyadicOwnerCoefficientResponse cfg.matrices cfg.hermitian s.covariance cfg.depth cfg.weight
      (cfg.center s.point)) ≤ cfg.responseCoefficient * Real.sqrt (Fintype.card ι : ℝ)

theorem DyadicEpochState.Invariant.sample_trace_positive {cfg : DyadicEpochConfig ι n}
    {s : DyadicEpochState ι} (hs : s.Invariant cfg) (hactive : ¬ s.Terminal cfg) :
    (Fintype.card ι : ℝ) / 16 ≤
      realTrace (epochCovariance s.covariance (frozenCoordinates s.point) s.point) ∧
      0 < realTrace (epochCovariance s.covariance (frozenCoordinates s.point) s.point) := by
  have hpaid : s.paid + s.dust ≤ (Fintype.card ι : ℝ) / 64 := by
    exact le_of_not_gt (fun h => hactive (Or.inl h))
  have hfrozen : (frozenCoordinates s.point).card < (Fintype.card ι : ℝ) / 64 := by
    exact lt_of_not_ge (fun h => hactive (Or.inr (Or.inl h)))
  apply epochCovariance_trace_positive hs.covariance_pos hs.covariance_le_one
    (frozenCoordinates s.point) s.point cfg.count_large ?_ hpaid hfrozen.le
  have ht : s.time ≤ (1 / 2 : ℝ) := hs.time_le.trans ((RectangularEpochParameters.duration_le_third cfg.response_large).trans (by norm_num))
  have hk : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left ht hk
  have hledger := hs.trace_ledger
  nlinarith


end MatrixSpencer
