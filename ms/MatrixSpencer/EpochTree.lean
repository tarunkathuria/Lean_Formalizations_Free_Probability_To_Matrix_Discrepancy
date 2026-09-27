import MatrixSpencer.EpochLocalMoments
import MatrixSpencer.EpochInitial
import MatrixSpencer.EpochSelection

/-!
# An actual finite epoch and its successful endpoint

The states carry the proved invariant. Every branch is a concrete positive
covariance sample followed by the proved rounding and preparation update.
The actual support mesh supplies the well-founded rank/fuel clock and both
conditional moment bounds, so no transition or moment oracle is assumed.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer
open FiniteBranchingTermination

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance epochTreeCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance epochTreeSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

abbrev ValidEpochState (cfg : EpochConfig ι n) := {s : EpochState ι // s.Invariant cfg}

/-- Legal branches record their actual sample witnesses and the proved local accounts. -/
structure EpochLegal (cfg : EpochConfig ι n) (s : ValidEpochState cfg)
    (b : Transition (ValidEpochState cfg)) : Prop where
  active : ¬ s.val.Terminal
  actual : ∀ i, ∃ o : EpochOutcome s.val, EpochStepWitness cfg s.val (cfg.step s.val) o (b.child i).val
  energy : (∑ i, b.weight i * epochEnergyAccount cfg (b.child i).val) ≤ epochEnergyAccount cfg s.val
  tangent : (∑ i, b.weight i * epochTangentAccount (b.child i).val) ≤ epochTangentAccount s.val

/-- The concrete sampler and actual child construction give finite legal branching. -/
theorem exists_epoch_transition (cfg : EpochConfig ι n) (s : ValidEpochState cfg)
    (hactive : ¬ s.val.Terminal) :
    ∃ b : Transition (ValidEpochState cfg), EpochLegal cfg s b ∧
      ∀ i, (b.child i).val.covariance.rank < s.val.covariance.rank ∨
        (b.child i).val.covariance.rank = s.val.covariance.rank ∧
          cfg.fuel (b.child i).val < cfg.fuel s.val := by
  classical
  have hex : ∀ o : EpochOutcome s.val, ∃ child : EpochState ι,
      EpochStepWitness cfg s.val (cfg.step s.val) o child :=
    fun o => exists_epoch_step s.property hactive (cfg.step_pos s.val hactive)
      (cfg.step_le_half s.val) (cfg.step_rounding s.val) (cfg.step_time_le s.val hactive) o
  let child : EpochOutcome s.val → EpochState ι := fun o => Classical.choose (hex o)
  have hw : ∀ o, EpochStepWitness cfg s.val (cfg.step s.val) o (child o) :=
    fun o => Classical.choose_spec (hex o)
  let validChild : EpochOutcome s.val → ValidEpochState cfg := fun o => ⟨child o, (hw o).invariant⟩
  let hQ := epochCovariance_posSemidef s.val.covariance (frozenCoordinates s.val.point) s.val.point
  let weight := fun o : EpochOutcome s.val => covarianceSampleWeight hQ o
  have hpos : ∀ o : EpochOutcome s.val, 0 < weight o := fun o => o.property
  have hsum : (∑ o : EpochOutcome s.val, weight o) = 1 :=
    positive_covarianceSample_weight_sum hQ (s.property.sample_trace_positive hactive).2
  let b := Transition.ofFintype validChild weight hpos hsum
  have hb : EpochLegal cfg s b := by
    refine ⟨hactive, ?_, ?_, ?_⟩
    · intro i
      exact ⟨(Fintype.equivFin (EpochOutcome s.val)).symm i, hw _⟩
    · exact (Transition.ofFintype_expectation validChild weight hpos hsum
        (fun t => epochEnergyAccount cfg t.val)).le.trans
          (epochEnergyAccount_conditional_le s.property hactive child hw)
    · exact (Transition.ofFintype_expectation validChild weight hpos hsum
        (fun t => epochTangentAccount t.val)).le.trans
          (epochTangentAccount_conditional_le s.property hactive child hw)
  refine ⟨b, hb, ?_⟩
  intro i
  obtain ⟨o, ho⟩ := hb.actual i
  have hcov : (b.child i).val.covariance ≤ s.val.covariance := by
    exact ho.covariance_le_moved.trans
      (covarianceMovement_posSemidef_range s.property.covariance_pos hQ
        (epochCovariance_le s.property.covariance_pos _ _) (by
          have hp := cfg.step_pos s.val hactive
          have hh := cfg.step_le_half s.val
          nlinarith)).2.1
  exact cfg.rank_fuel_decrease s.property.covariance_pos (b.child i).property.covariance_pos
    hactive hcov ho.time_eq

/-- An epoch has an actual finite tree, with no depth or lower-mesh assumption. -/
theorem exists_finite_epoch_tree (cfg : EpochConfig ι n) (start : ValidEpochState cfg) :
    Nonempty (Tree (fun s : ValidEpochState cfg => s.val.Terminal) (EpochLegal cfg) start) :=
  exists_tree_of_rank_fuel (fun s : ValidEpochState cfg => s.val.covariance.rank)
    (fun s => cfg.fuel s.val) (exists_epoch_transition cfg) start

theorem finite_epoch_energy_le (cfg : EpochConfig ι n) {start : ValidEpochState cfg}
    (t : Tree (fun s : ValidEpochState cfg => s.val.Terminal) (EpochLegal cfg) start) :
    t.expectation (fun s => epochEnergyAccount cfg s.val) ≤ epochEnergyAccount cfg start.val :=
  t.expectation_le_of_local _ (fun _ _ hb => hb.energy)

theorem finite_epoch_tangent_le (cfg : EpochConfig ι n) {start : ValidEpochState cfg}
    (t : Tree (fun s : ValidEpochState cfg => s.val.Terminal) (EpochLegal cfg) start) :
    t.expectation (fun s => epochTangentAccount s.val) ≤ epochTangentAccount start.val :=
  t.expectation_le_of_local _ (fun _ _ hb => hb.tangent)

/-- The actual finite tree has a selected successful endpoint. All initialization,
transition, termination, and moment hypotheses are discharged internally. -/
theorem exists_good_epoch_endpoint (cfg : EpochConfig ι n) :
    ∃ s : EpochState ι, EpochGoodEndpoint cfg s := by
  classical
  obtain ⟨start, hstart, hpoint, htime, htangent, hround, henergy⟩ := exists_initial_epoch cfg
  let validStart : ValidEpochState cfg := ⟨start, hstart⟩
  let t := Classical.choice (exists_finite_epoch_tree cfg validStart)
  have he : (∑ l : t.Leaves, t.leafWeight l * epochEnergySuper cfg (t.leafState l).val) ≤
      2 * Real.sqrt (Fintype.card ι : ℝ) := by
    have he0 : epochEnergyAccount cfg start ≤ 2 * Real.sqrt (Fintype.card ι : ℝ) := by
      simpa only [epochEnergyAccount, htime, hround, mul_zero, sub_zero] using henergy
    exact (finite_epoch_energy_le cfg t).trans he0
  have hm : (∑ l : t.Leaves, t.leafWeight l * epochTangentAdjusted (t.leafState l).val) ≤ 0 := by
    have hm0 : epochTangentAccount start = 0 := by simp [epochTangentAccount, htangent, htime]
    exact (finite_epoch_tangent_le cfg t).trans hm0.le
  obtain ⟨l, _, hl⟩ := exists_good_epoch_endpoint_of_supermartingale cfg
    (fun l : t.Leaves => (t.leafState l).val) t.leafWeight (fun l => (t.leafWeight_pos l).le)
    t.leafWeight_sum (fun l => (t.leafState l).property) (fun l => t.leaf_terminal l) he hm
  exact ⟨(t.leafState l).val, hl⟩

/-- A public epoch statement: an actual regular point makes time or freezing
progress and pays at most 22 sqrt(k) in the identity-covariance potential. -/
theorem exists_successful_epoch (cfg : EpochConfig ι n) :
    ∃ (y : EuclideanSpace ℝ ι) (time : ℝ), CubeRegular cfg.epsilon y ∧
      0 ≤ time ∧ time ≤ epochTimeLimit ∧
      ‖cfg.start‖ ^ 2 + (Fintype.card ι : ℝ) / 16 * time ≤ ‖y‖ ^ 2 ∧
      (time = epochTimeLimit ∨ (Fintype.card ι : ℝ) / 64 ≤ (frozenCoordinates y).card) ∧
      ownerPotential (cfg.center y) cfg.matrices 1 1 -
        ownerPotential cfg.anchor cfg.matrices 1 1 ≤ 22 * Real.sqrt (Fintype.card ι : ℝ) := by
  obtain ⟨s, hs⟩ := exists_good_epoch_endpoint cfg
  exact ⟨s.point, s.time, hs.invariant.regular, hs.invariant.time_nonneg,
    hs.invariant.time_le, hs.invariant.norm_progress, hs.successful, hs.reset_growth⟩

end MatrixSpencer
