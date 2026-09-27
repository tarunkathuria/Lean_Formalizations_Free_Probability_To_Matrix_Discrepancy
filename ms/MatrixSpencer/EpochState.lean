import MatrixSpencer.OwnerDustPreparation
import MatrixSpencer.OwnerCertificate
import MatrixSpencer.EpochCoordinateStep
import MatrixSpencer.EpochMesh

/-!
# Concrete data and invariants of a p=2 finite epoch

The center retains a fixed Hermitian offset and all original coefficient
labels of this epoch. The coefficient covariance is never reset inside it.
This file does not assume that an epoch or a full signing already exists.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Set
noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance epochStateCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance epochStateSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def epochTimeLimit : ℝ := 1 / 1539
def epochTracePriceScale : ℝ := 4096
def epochDustThreshold : ℝ := 1 / 8192
def epochResponseConstant : ℝ := 1538

def epochCenter (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    selfAdjoint (Matrix n n ℂ) :=
  offset + ∑ i, x i • hermitianMatrixFamily A hA i

theorem epochCenter_norm_le (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, ‖A i‖ ≤ 1) (x : EuclideanSpace ℝ ι) (hx : ∀ i, |x i| ≤ 1) :
    ‖epochCenter offset A hA x‖ ≤ ‖offset‖ + (Fintype.card ι : ℝ) := by
  apply (norm_add_le _ _).trans
  apply add_le_add_left
  calc
    _ ≤ ∑ i, ‖x i • hermitianMatrixFamily A hA i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hN i)).trans (hx i)
    _ = (Fintype.card ι : ℝ) := by simp

theorem epochCenter_coe (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    (epochCenter offset A hA x : Matrix n n ℂ) = (offset : Matrix n n ℂ) + ∑ i, x i • A i := by
  change (selfAdjoint (Matrix n n ℂ)).subtype
    (offset + ∑ i, x i • hermitianMatrixFamily A hA i) = _
  rw [map_add, map_sum]
  rfl

theorem epochCenter_add_smul (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (x v : EuclideanSpace ℝ ι) (h : ℝ) :
    epochCenter offset A hA (x + h • v) = epochCenter offset A hA x +
      h • (∑ i, v i • hermitianMatrixFamily A hA i) := by
  simp only [epochCenter, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    add_smul, MulAction.mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  module

structure EpochConfig (ι n : Type*) [Fintype ι] [Fintype n] [DecidableEq n] where
  matrices : ι → Matrix n n ℂ
  hermitian : ∀ i, (matrices i).IsHermitian
  contractions : ∀ i, ‖matrices i‖ ≤ 1
  offset : selfAdjoint (Matrix n n ℂ)
  start : EuclideanSpace ℝ ι
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_small : (Fintype.card ι : ℝ) * epsilon ≤ 1 / 1000
  start_regular : CubeRegular epsilon start
  start_unfrozen : ∀ i, ¬ IsSign (start i)
  count_large : 32 ≤ Fintype.card ι

def EpochConfig.center (cfg : EpochConfig ι n) (x : EuclideanSpace ℝ ι) :
    selfAdjoint (Matrix n n ℂ) := epochCenter cfg.offset cfg.matrices cfg.hermitian x

def EpochConfig.anchor (cfg : EpochConfig ι n) : Matrix n n ℂ := cfg.center cfg.start

structure EpochState (ι : Type*) [Fintype ι] where
  point : EuclideanSpace ℝ ι
  covariance : Matrix ι ι ℝ
  time : ℝ
  paid : ℝ
  dust : ℝ
  tangent : ℝ
  rounding : ℝ

def EpochState.Terminal (s : EpochState ι) : Prop :=
  (Fintype.card ι : ℝ) / 64 < s.paid + s.dust ∨
    (Fintype.card ι : ℝ) / 64 ≤ (frozenCoordinates s.point).card ∨ epochTimeLimit ≤ s.time

structure EpochState.Invariant (cfg : EpochConfig ι n) (s : EpochState ι) : Prop where
  regular : CubeRegular cfg.epsilon s.point
  covariance_pos : s.covariance.PosSemidef
  covariance_le_one : s.covariance ≤ 1
  time_nonneg : 0 ≤ s.time
  time_le : s.time ≤ epochTimeLimit
  paid_nonneg : 0 ≤ s.paid
  dust_nonneg : 0 ≤ s.dust
  rounding_nonneg : 0 ≤ s.rounding
  trace_ledger : (Fintype.card ι : ℝ) * (1 - s.time) - s.paid - s.dust ≤ realTrace s.covariance
  dust_budget : s.dust ≤ epochDustThreshold *
    ((Fintype.card ι : ℝ) - (s.covariance.rank : ℝ))
  rounding_budget : s.rounding ≤ cfg.epsilon * (frozenCoordinates s.point).card
  tangent_error : |ownerCertificateTangent cfg.anchor 1 (cfg.center s.point) - s.tangent| ≤ s.rounding
  norm_progress : ‖cfg.start‖ ^ 2 + (Fintype.card ι : ℝ) / 16 * s.time ≤ ‖s.point‖ ^ 2
  ready : ¬ s.Terminal →
    (∀ u : EuclideanSpace ℝ ι,
      u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) s.covariance).toLinearMap →
      epochDustThreshold * ‖u‖ ^ 2 ≤ inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) s.covariance u)) ∧
    realTrace (s.covariance * ownerCoefficientResponse cfg.matrices cfg.hermitian s.covariance 1
      (cfg.center s.point)) ≤ epochResponseConstant * Real.sqrt (Fintype.card ι : ℝ)

theorem EpochState.Invariant.sample_trace_positive {cfg : EpochConfig ι n}
    {s : EpochState ι} (hs : s.Invariant cfg) (hactive : ¬ s.Terminal) :
    (Fintype.card ι : ℝ) / 16 ≤
      realTrace (epochCovariance s.covariance (frozenCoordinates s.point) s.point) ∧
      0 < realTrace (epochCovariance s.covariance (frozenCoordinates s.point) s.point) := by
  have hpaid : s.paid + s.dust ≤ (Fintype.card ι : ℝ) / 64 := by
    exact le_of_not_gt (fun h => hactive (Or.inl h))
  have hfrozen : (frozenCoordinates s.point).card < (Fintype.card ι : ℝ) / 64 := by
    exact lt_of_not_ge (fun h => hactive (Or.inr (Or.inl h)))
  apply epochCovariance_trace_positive hs.covariance_pos hs.covariance_le_one
    (frozenCoordinates s.point) s.point cfg.count_large ?_ hpaid hfrozen.le
  have ht : s.time ≤ (1 / 2 : ℝ) := hs.time_le.trans (by norm_num [epochTimeLimit])
  have hk : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left ht hk
  have hledger := hs.trace_ledger
  nlinarith

end MatrixSpencer
