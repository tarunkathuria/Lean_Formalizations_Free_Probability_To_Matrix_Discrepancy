import MatrixSpencer.RectangularRidgeEpochEndpointBounds
import MatrixSpencer.RectangularRidgePhaseAssembly
import MatrixSpencer.MSManuscriptAcceptanceRetry

/-! Actual finite ridge acceptance, retries and accepted epoch progress. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeEpochAcceptance
open RectangularRidgeEpochInput RectangularRidgeEpochRun RectangularRidgeEpochMoments
open RectangularRidgeEpochAcceptanceData RectangularRidgeEpochEndpointBounds
open MSManuscriptAdaptive (Sampler failure)
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgeEpochAcceptanceCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeEpochAcceptanceSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
attribute [local instance] Classical.propDecidable
attribute [local irreducible] run RectangularRidgePotential.optimizer RectangularRidgeCertificate.density
  RectangularRidgeCovarianceCalculus.ownerPotential regularizedOwnerPotential
set_option maxHeartbeats 1000000

theorem good_accepted (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (s : Certified c) (hg : RectangularRidgeEpochSuccess.Good c s.val) :
    accepts solver a c s = true := by
  apply RectangularRidgeSolverAcceptance.good_accepted solver (acceptanceConfig a c) (endpoint c s) (endpoint_valid a c s)
  obtain ⟨he,ht,hclean⟩ := hg
  refine ⟨?_,he,?_⟩
  · change decide ((live c : ℝ)/64<s.val.paid+s.val.dust)=false
    exact decide_eq_false (not_lt.mpr hclean)
  · rw [tangent_eq]
    exact ht

theorem acceptance_probability (solver : RectangularRidgeConvexValue.Solver) (a : Fin d) (c : Config N d) :
    (31/50 : ℝ) ≤ MSManuscriptAcceptanceRetry.acceptanceProbability (RectangularRidgeEpochRun.output solver a c) (accepts solver a c) :=
by
  apply (RectangularRidgeEpochSuccess.good_probability_ge solver a c).trans
  change (RectangularRidgeEpochRun.output solver a c).expectation _ ≤
    (RectangularRidgeEpochRun.output solver a c).expectation _
  apply Sampler.expectation_mono
  intro s
  by_cases hg : RectangularRidgeEpochSuccess.Good c s.val
  · simp only [if_pos hg, good_accepted solver a c s hg, Bool.true_eq, ↓reduceIte, le_refl]
  · simp only [if_neg hg]
    cases accepts solver a c s <;> norm_num

def accepted (solver : RectangularRidgeConvexValue.Solver) (a : Fin d) (c : Config N d) (r : ℕ) : Sampler (Option (Certified c)) :=
  MSManuscriptAcceptanceRetry.output (RectangularRidgeEpochRun.output solver a c) (accepts solver a c) r

theorem accepted_failure_le (solver : RectangularRidgeConvexValue.Solver) (a : Fin d) (c : Config N d) (r : ℕ) :
    (accepted solver a c r).expectation failure ≤ (19/50 : ℝ)^r := by
  have h := MSManuscriptAcceptanceRetry.output_failure_le _ _ (acceptance_probability solver a c) r
  norm_num only [show (1:ℝ)-31/50=19/50 by norm_num] at h
  exact h

def potential (c : Config N d) : EuclideanSpace ℝ (Fin N) → ℝ :=
  RectangularRidgeRemainingPotential.potential (depth c) (theta c) (ridge c) 0 c.atoms c.hermitian

def GoodEndpoint (c : Config N d) (s : Certified c) : Prop :=
  FiniteHalfPhase.EpochAdvance (potential c) (duration c/2) 27 c.start s.val.point s.val.time

theorem liveCount_eq (c : Config N d) : FiniteHalfPhase.liveCount c.start = live c := by
  simp only [FiniteHalfPhase.liveCount, live, oldFrozen, RectangularRidgeLiveOwner.count_eq, Fintype.card_fin]

theorem accepted_draw (solver : RectangularRidgeConvexValue.Solver) (a : Fin d) (c : Config N d)
    (z : (RectangularRidgeEpochRun.output solver a c).Draws)
    (ha : accepts solver a c ((RectangularRidgeEpochRun.output solver a c).value z)=true) :
    GoodEndpoint c ((RectangularRidgeEpochRun.output solver a c).value z) := by
  let s := (RectangularRidgeEpochRun.output solver a c).value z
  have hav := RectangularRidgeSolverAcceptance.accepts_sound solver (acceptanceConfig a c) (endpoint c s) (endpoint_valid a c s) ha
  have hc : s.val.paid+s.val.dust ≤ (live c : ℝ)/64 := by
    have h := hav.1
    change decide ((live c : ℝ)/64<s.val.paid+s.val.dust)=false at h
    simpa only [decide_eq_false_iff_not, not_lt] using h
  have hstop := output_stopped solver a c z
  have hs : duration c/2 ≤ s.val.time ∨ (live c : ℝ)/64 ≤
      ((frozenCoordinates s.val.point).card : ℝ)-(frozenCoordinates c.start).card := by
    have hcard := Finset.card_sdiff_of_subset s.property.1.frozen_subset
    have hcard' : ((frozenCoordinates s.val.point \ oldFrozen c).card : ℝ) =
        ((frozenCoordinates s.val.point).card : ℝ)-(oldFrozen c).card := by
      rw [hcard, Nat.cast_sub (Finset.card_le_card s.property.1.frozen_subset)]
    rcases hstop with (ht|hf|hp)|ht
    · exact Or.inl (by change duration c ≤ s.val.time at ht; linarith [duration_pos c])
    · exact Or.inr (by rw [hcard'] at hf; exact hf)
    · exact False.elim (not_lt.mpr hc hp)
    · exact Or.inl (by change duration c < s.val.time+mesh c^2 at ht; linarith [mesh_time c])
  have hC := (endpoint c s).covariance_psd
  have hstart := RectangularRidgeRemainingPotential.projection_posSemidef (oldFrozen c)
  have hp := RectangularRidgeSolverAcceptance.accepted_potential_increment solver
    (acceptanceConfig a c) (endpoint c s) (endpoint_valid a c s) ha
    (RectangularRidgeLiveOwner.owner (oldFrozen c)).physical hstart (rounding_budget a c s)
  have hr := RectangularRidgeRemainingPotential.reinstall_le (depth c) (theta c) (ridge c)
    0 c.atoms c.hermitian c.contractions s.val.point hC
  have hl := Real.sqrt_le_sqrt (Nat.cast_le.mpr
    (RectangularRidgeRemainingPotential.liveCount_antitone s.property.1.frozen_subset))
  refine ⟨s.property.1.regular.1,s.property.1.frozen_subset,s.property.1.time_nonneg,?_,?_,?_⟩
  · rw [liveCount_eq]
    exact RectangularRidgeEpochStateFacts.output_norm_progress solver a c z
  · rw [liveCount_eq]
    exact hs
  · rw [liveCount_eq]
    change potential c s.val.point ≤ potential c c.start+27*Real.sqrt (live c : ℝ)
    change RectangularRidgeCovarianceCalculus.ownerPotential (depth c) (center c s.val.point) c.atoms
      s.val.owner.physical (theta c) (ridge c)-potential c c.start < 25*Real.sqrt (live c : ℝ) at hp
    change potential c s.val.point-RectangularRidgeCovarianceCalculus.ownerPotential (depth c) (center c s.val.point)
      c.atoms s.val.owner.physical (theta c) (ridge c) ≤ 2*Real.sqrt (RectangularRidgeRemainingPotential.liveCount s.val.point : ℝ) at hr
    change Real.sqrt (RectangularRidgeRemainingPotential.liveCount s.val.point : ℝ) ≤ Real.sqrt (live c : ℝ) at hl
    linarith

theorem accepted_sound (solver : RectangularRidgeConvexValue.Solver) (a : Fin d) (c : Config N d)
    (r : ℕ) (z : (accepted solver a c r).Draws) (s : Certified c)
    (ho : (accepted solver a c r).value z=some s) : GoodEndpoint c s :=
  MSManuscriptAcceptanceRetry.output_sound _ _ (GoodEndpoint c) (accepted_draw solver a c) r z s ho

end MatrixSpencer.RectangularRidgeEpochAcceptance
