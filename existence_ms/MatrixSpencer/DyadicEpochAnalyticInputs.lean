import MatrixSpencer.DyadicEpochLocalMoments
import MatrixSpencer.DyadicEpochInitial
import MatrixSpencer.EpochWalkMesh

/-!
# Explicit analytic inputs and the finite dyadic epoch clock

The analytic inputs below are concrete statements about the actual owner
potential and the actual sampled update. Their existence is not asserted
here. The mesh is indexed by the covariance subspace, never by an eigenbasis.
-/
open Set Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance dyadicEpochInputsCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicEpochInputsSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def DyadicEpochState.support (s : DyadicEpochState ι) : Submodule ℝ (EuclideanSpace ℝ ι) :=
  LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) s.covariance).toLinearMap

structure DyadicEpochAnalyticInputs (cfg : DyadicEpochConfig ι n) where
  prepare : ∀ (H : selfAdjoint (Matrix n n ℂ)) (upper : Matrix ι ι ℝ),
    upper.PosSemidef → upper ≤ 1 →
    ∃ C paid dust, DyadicPreparedCovariance cfg H upper C paid dust
  mesh : Submodule ℝ (EuclideanSpace ℝ ι) → ℝ
  mesh_pos : ∀ K, 0 < mesh K
  mesh_le_half : ∀ K, mesh K ≤ 1 / 2
  mesh_rounding : ∀ K, mesh K * Real.sqrt (Fintype.card ι : ℝ) ≤ cfg.epsilon
  drift : ∀ (s : DyadicEpochState ι), s.Invariant cfg → ¬ s.Terminal cfg →
    ∀ h : ℝ, 0 ≤ h → h ≤ mesh s.support →
      dyadicEpochPotentialDrift cfg s h ≤ cfg.energyRate * h ^ 2

namespace DyadicEpochAnalyticInputs
variable {cfg : DyadicEpochConfig ι n}

def step (inputs : DyadicEpochAnalyticInputs cfg) (s : DyadicEpochState ι) : ℝ :=
  epochMeshStep (inputs.mesh s.support) cfg.duration s.time

def fuel (inputs : DyadicEpochAnalyticInputs cfg) (s : DyadicEpochState ι) : ℕ :=
  epochMeshFuel (inputs.mesh s.support) cfg.duration s.time

theorem time_lt_of_active (s : DyadicEpochState ι) (hactive : ¬ s.Terminal cfg) :
    s.time < cfg.duration := lt_of_not_ge (fun ht => hactive (Or.inr (Or.inr ht)))

theorem step_pos (inputs : DyadicEpochAnalyticInputs cfg) (s : DyadicEpochState ι)
    (hactive : ¬ s.Terminal cfg) : 0 < inputs.step s :=
  epochMeshStep_pos (inputs.mesh_pos _) (time_lt_of_active s hactive)

theorem step_le_mesh (inputs : DyadicEpochAnalyticInputs cfg) (s : DyadicEpochState ι) :
    inputs.step s ≤ inputs.mesh s.support := epochMeshStep_le _ _ _

theorem step_le_half (inputs : DyadicEpochAnalyticInputs cfg) (s : DyadicEpochState ι) :
    inputs.step s ≤ (1 / 2 : ℝ) := (inputs.step_le_mesh s).trans (inputs.mesh_le_half _)

theorem step_rounding (inputs : DyadicEpochAnalyticInputs cfg) (s : DyadicEpochState ι) :
    inputs.step s * Real.sqrt (Fintype.card ι : ℝ) ≤ cfg.epsilon :=
  (mul_le_mul_of_nonneg_right (inputs.step_le_mesh s) (Real.sqrt_nonneg _)).trans (inputs.mesh_rounding _)

theorem step_time_le (inputs : DyadicEpochAnalyticInputs cfg) (s : DyadicEpochState ι)
    (hactive : ¬ s.Terminal cfg) : s.time + inputs.step s ^ 2 ≤ cfg.duration :=
  epochMeshStep_time_le (inputs.mesh_pos _) (time_lt_of_active s hactive)

theorem step_drift (inputs : DyadicEpochAnalyticInputs cfg) {s : DyadicEpochState ι}
    (hs : s.Invariant cfg) (hactive : ¬ s.Terminal cfg) :
    dyadicEpochPotentialDrift cfg s (inputs.step s) ≤ cfg.energyRate * inputs.step s ^ 2 :=
  inputs.drift s hs hactive _ (inputs.step_pos s hactive).le (inputs.step_le_mesh s)

theorem fuel_pos (inputs : DyadicEpochAnalyticInputs cfg) (s : DyadicEpochState ι)
    (hactive : ¬ s.Terminal cfg) : 0 < inputs.fuel s :=
  epochMeshFuel_pos (inputs.mesh_pos _) (time_lt_of_active s hactive)

theorem mesh_eq_of_rank_eq (inputs : DyadicEpochAnalyticInputs cfg) {s t : DyadicEpochState ι}
    (hs : s.covariance.PosSemidef) (ht : t.covariance.PosSemidef)
    (hcov : t.covariance ≤ s.covariance) (hrank : t.covariance.rank = s.covariance.rank) :
    inputs.mesh t.support = inputs.mesh s.support :=
  congrArg inputs.mesh (posSemidef_range_eq_of_le_of_rank_eq hs ht hcov hrank)

theorem fuel_decreases_of_rank_eq (inputs : DyadicEpochAnalyticInputs cfg) {s t : DyadicEpochState ι}
    (hs : s.covariance.PosSemidef) (ht : t.covariance.PosSemidef)
    (hactive : ¬ s.Terminal cfg) (hcov : t.covariance ≤ s.covariance)
    (hrank : t.covariance.rank = s.covariance.rank)
    (htime : t.time = s.time + inputs.step s ^ 2) : inputs.fuel t < inputs.fuel s := by
  have hm := inputs.mesh_eq_of_rank_eq hs ht hcov hrank
  unfold fuel
  rw [hm, htime]
  exact epochMeshFuel_decreases (inputs.mesh_pos _) (time_lt_of_active s hactive)

theorem rank_fuel_decrease (inputs : DyadicEpochAnalyticInputs cfg) {s t : DyadicEpochState ι}
    (hs : s.covariance.PosSemidef) (ht : t.covariance.PosSemidef)
    (hactive : ¬ s.Terminal cfg) (hcov : t.covariance ≤ s.covariance)
    (htime : t.time = s.time + inputs.step s ^ 2) :
    FiniteBranchingTermination.RankFuelDecrease (fun v : DyadicEpochState ι => v.covariance.rank)
      inputs.fuel t s := by
  have hrank := CovarianceDust.rank_le_of_posSemidef_le ht hcov
  rcases lt_or_eq_of_le hrank with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, inputs.fuel_decreases_of_rank_eq hs ht hactive hcov heq htime⟩

/-- The explicit preparation data and fixed-subspace mesh give every actual child. -/
theorem exists_step (inputs : DyadicEpochAnalyticInputs cfg) {s : DyadicEpochState ι}
    (hs : s.Invariant cfg) (hactive : ¬ s.Terminal cfg) (o : DyadicEpochOutcome s) :
    ∃ child : DyadicEpochState ι, DyadicEpochStepWitness cfg s (inputs.step s) o child := by
  have hmove := dyadicEpochMovedCovariance_properties hs (inputs.step_pos s hactive).le
    (inputs.step_le_half s)
  apply exists_dyadic_epoch_step_of_preparation hs hactive (inputs.step_pos s hactive)
    (inputs.step_le_half s) (inputs.step_rounding s) (inputs.step_time_le s hactive) o
  intro _
  exact inputs.prepare _ _ hmove.1 (hmove.2.1.trans hs.covariance_le_one)

/-- The prepared identity gives the actual initialized state and its paid certificate budget. -/
theorem exists_initial (inputs : DyadicEpochAnalyticInputs cfg) :
    ∃ s : DyadicEpochState ι, s.Invariant cfg ∧ s.point = cfg.start ∧ s.time = 0 ∧
      s.tangent = 0 ∧ s.rounding = 0 ∧
      dyadicOwnerCertificate cfg.anchor cfg.matrices cfg.depth cfg.weight
        (cfg.center s.point) s.covariance +
        (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * s.paid ≤
          2 * Real.sqrt (Fintype.card ι : ℝ) := by
  obtain ⟨C, p, d, hp⟩ := inputs.prepare (cfg.center cfg.start) 1 Matrix.PosSemidef.one le_rfl
  exact ⟨initialDyadicEpochState cfg C p d, initialDyadicEpochState_invariant cfg hp,
    rfl, rfl, rfl, rfl, initialDyadicEpochState_energy_le cfg hp⟩

end DyadicEpochAnalyticInputs
end
end MatrixSpencer
