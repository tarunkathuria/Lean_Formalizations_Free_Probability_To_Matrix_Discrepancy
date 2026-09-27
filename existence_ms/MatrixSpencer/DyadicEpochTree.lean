import MatrixSpencer.DyadicEpochAnalyticInputs
import MatrixSpencer.DyadicEpochSelection

/-!
# A finite dyadic epoch conditional on explicit analytic inputs

The states carry the proved invariant. Every branch is a concrete positive
covariance sample followed by the proved rounding and preparation update.
The explicit analytic inputs supply preparation and actual potential drift.
From these inputs the rank/fuel clock, finite tree, and both conditional
moment bounds are proved internally. Analytic existence remains separate.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer
open FiniteBranchingTermination

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance dyadicEpochTreeCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicEpochTreeSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

abbrev ValidDyadicEpochState (cfg : DyadicEpochConfig ι n) := {s : DyadicEpochState ι // s.Invariant cfg}

/-- Legal branches record their actual sample witnesses and the proved local accounts. -/
structure DyadicEpochLegal (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (s : ValidDyadicEpochState cfg)
    (b : Transition (ValidDyadicEpochState cfg)) : Prop where
  active : ¬ s.val.Terminal cfg
  actual : ∀ i, ∃ o : DyadicEpochOutcome s.val, DyadicEpochStepWitness cfg s.val (inputs.step s.val) o (b.child i).val
  energy : (∑ i, b.weight i * dyadicEpochEnergyAccount cfg (b.child i).val) ≤ dyadicEpochEnergyAccount cfg s.val
  tangent : (∑ i, b.weight i * dyadicEpochTangentAccount (b.child i).val) ≤ dyadicEpochTangentAccount s.val

/-- The concrete sampler and actual child construction give finite legal branching. -/
theorem exists_dyadic_epoch_transition (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (s : ValidDyadicEpochState cfg)
    (hactive : ¬ s.val.Terminal cfg) :
    ∃ b : Transition (ValidDyadicEpochState cfg), DyadicEpochLegal cfg inputs s b ∧
      ∀ i, (b.child i).val.covariance.rank < s.val.covariance.rank ∨
        (b.child i).val.covariance.rank = s.val.covariance.rank ∧
          inputs.fuel (b.child i).val < inputs.fuel s.val := by
  classical
  have hex : ∀ o : DyadicEpochOutcome s.val, ∃ child : DyadicEpochState ι,
      DyadicEpochStepWitness cfg s.val (inputs.step s.val) o child :=
    fun o => inputs.exists_step s.property hactive o
  let child : DyadicEpochOutcome s.val → DyadicEpochState ι := fun o => Classical.choose (hex o)
  have hw : ∀ o, DyadicEpochStepWitness cfg s.val (inputs.step s.val) o (child o) :=
    fun o => Classical.choose_spec (hex o)
  let validChild : DyadicEpochOutcome s.val → ValidDyadicEpochState cfg := fun o => ⟨child o, (hw o).invariant⟩
  let hQ := epochCovariance_posSemidef s.val.covariance (frozenCoordinates s.val.point) s.val.point
  let weight := fun o : DyadicEpochOutcome s.val => covarianceSampleWeight hQ o
  have hpos : ∀ o : DyadicEpochOutcome s.val, 0 < weight o := fun o => o.property
  have hsum : (∑ o : DyadicEpochOutcome s.val, weight o) = 1 :=
    positive_covarianceSample_weight_sum hQ (s.property.sample_trace_positive hactive).2
  let b := Transition.ofFintype validChild weight hpos hsum
  have hb : DyadicEpochLegal cfg inputs s b := by
    refine ⟨hactive, ?_, ?_, ?_⟩
    · intro i
      exact ⟨(Fintype.equivFin (DyadicEpochOutcome s.val)).symm i, hw _⟩
    · exact (Transition.ofFintype_expectation validChild weight hpos hsum
        (fun t => dyadicEpochEnergyAccount cfg t.val)).le.trans
          (dyadicEpochEnergyAccount_conditional_le s.property hactive (inputs.step s.val)
            (inputs.step_pos s.val hactive).le (inputs.step_le_half s.val) child hw
            (inputs.step_drift s.property hactive))
    · exact (Transition.ofFintype_expectation validChild weight hpos hsum
        (fun t => dyadicEpochTangentAccount t.val)).le.trans
          (dyadicEpochTangentAccount_conditional_le s.property hactive (inputs.step s.val) child hw)
  refine ⟨b, hb, ?_⟩
  intro i
  obtain ⟨o, ho⟩ := hb.actual i
  have hcov : (b.child i).val.covariance ≤ s.val.covariance := by
    exact ho.covariance_le_moved.trans
      (covarianceMovement_posSemidef_range s.property.covariance_pos hQ
        (epochCovariance_le s.property.covariance_pos _ _) (by
          have hp := inputs.step_pos s.val hactive
          have hh := inputs.step_le_half s.val
          nlinarith)).2.1
  exact inputs.rank_fuel_decrease s.property.covariance_pos (b.child i).property.covariance_pos
    hactive hcov ho.time_eq

/-- An epoch has an actual finite tree, with no depth or lower-mesh assumption. -/
theorem exists_finite_dyadic_epoch_tree (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (start : ValidDyadicEpochState cfg) :
    Nonempty (Tree (fun s : ValidDyadicEpochState cfg => s.val.Terminal cfg) (DyadicEpochLegal cfg inputs) start) :=
  exists_tree_of_rank_fuel (fun s : ValidDyadicEpochState cfg => s.val.covariance.rank)
    (fun s => inputs.fuel s.val) (exists_dyadic_epoch_transition cfg inputs) start

theorem finite_dyadic_epoch_energy_le (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) {start : ValidDyadicEpochState cfg}
    (t : Tree (fun s : ValidDyadicEpochState cfg => s.val.Terminal cfg) (DyadicEpochLegal cfg inputs) start) :
    t.expectation (fun s => dyadicEpochEnergyAccount cfg s.val) ≤ dyadicEpochEnergyAccount cfg start.val :=
  t.expectation_le_of_local _ (fun _ _ hb => hb.energy)

theorem finite_dyadic_epoch_tangent_le (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) {start : ValidDyadicEpochState cfg}
    (t : Tree (fun s : ValidDyadicEpochState cfg => s.val.Terminal cfg) (DyadicEpochLegal cfg inputs) start) :
    t.expectation (fun s => dyadicEpochTangentAccount s.val) ≤ dyadicEpochTangentAccount start.val :=
  t.expectation_le_of_local _ (fun _ _ hb => hb.tangent)

/-- The actual finite tree has a selected successful endpoint. Given the explicit analytic inputs, initialization,
transition, termination, and moment hypotheses are discharged internally. -/
theorem exists_good_dyadic_epoch_endpoint (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) :
    ∃ s : DyadicEpochState ι, DyadicEpochGoodEndpoint cfg s := by
  classical
  obtain ⟨start, hstart, hpoint, htime, htangent, hround, henergy⟩ := inputs.exists_initial
  let validStart : ValidDyadicEpochState cfg := ⟨start, hstart⟩
  let t := Classical.choice (exists_finite_dyadic_epoch_tree cfg inputs validStart)
  have he : (∑ l : t.Leaves, t.leafWeight l * dyadicEpochEnergySuper cfg (t.leafState l).val) ≤
      2 * Real.sqrt (Fintype.card ι : ℝ) := by
    have he0 : dyadicEpochEnergyAccount cfg start ≤ 2 * Real.sqrt (Fintype.card ι : ℝ) := by
      simpa only [dyadicEpochEnergyAccount, htime, hround, mul_zero, sub_zero] using henergy
    exact (finite_dyadic_epoch_energy_le cfg inputs t).trans he0
  have hm : (∑ l : t.Leaves, t.leafWeight l * dyadicEpochTangentAdjusted (t.leafState l).val) ≤ 0 := by
    have hm0 : dyadicEpochTangentAccount start = 0 := by simp [dyadicEpochTangentAccount, htangent, htime]
    exact (finite_dyadic_epoch_tangent_le cfg inputs t).trans hm0.le
  obtain ⟨l, _, hl⟩ := exists_good_dyadic_epoch_endpoint_of_supermartingale cfg
    (fun l : t.Leaves => (t.leafState l).val) t.leafWeight (fun l => (t.leafWeight_pos l).le)
    t.leafWeight_sum (fun l => (t.leafState l).property) (fun l => t.leaf_terminal l) he hm
  exact ⟨(t.leafState l).val, hl⟩

/-- A public epoch statement: an actual regular point makes time or freezing
progress and pays at most 22 sqrt(k) in the identity-covariance potential. -/
theorem exists_successful_dyadic_epoch (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) :
    ∃ (y : EuclideanSpace ℝ ι) (time : ℝ), CubeRegular cfg.epsilon y ∧
      0 ≤ time ∧ time ≤ cfg.duration ∧
      ‖cfg.start‖ ^ 2 + (Fintype.card ι : ℝ) / 16 * time ≤ ‖y‖ ^ 2 ∧
      (time = cfg.duration ∨ (Fintype.card ι : ℝ) / 64 ≤ (frozenCoordinates y).card) ∧
      cfg.potential (cfg.center y) 1 -
        cfg.potential cfg.anchor 1 ≤ 22 * Real.sqrt (Fintype.card ι : ℝ) := by
  obtain ⟨s, hs⟩ := exists_good_dyadic_epoch_endpoint cfg inputs
  exact ⟨s.point, s.time, hs.invariant.regular, hs.invariant.time_nonneg,
    hs.invariant.time_le, hs.invariant.norm_progress, hs.successful, hs.reset_growth⟩

end MatrixSpencer
