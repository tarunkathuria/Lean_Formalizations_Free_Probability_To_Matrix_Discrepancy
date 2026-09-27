import MatrixSpencer.MSManuscriptLiftedEpoch
import MatrixSpencer.ActualHalfPhase


open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
namespace MatrixSpencer.MSManuscriptHalfPhase
open PhaseRestriction MSManuscriptAdaptive MSManuscriptPhase
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
variable (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
  (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
  (ε : ℝ) (hε : 0 < ε) (hsmall : (Fintype.card ι : ℝ)*ε ≤ 1/1000)

structure Reports where
  value : ∀ (x : Point (ι := ι) ε) (_hl : 32 ≤ Fintype.card (Live x.val)), EpochState (Live x.val) → ℝ
  accuracy : ∀ x hl, MSManuscriptEpoch.ReportAccuracy
    (MSManuscriptLiftedEpoch.cfg offset A hA hN ε hε hsmall x hl) (value x hl)

def analyticReports : Reports offset A hA hN ε hε hsmall where
  value x hl := MSManuscriptEpoch.score (MSManuscriptLiftedEpoch.cfg offset A hA hN ε hε hsmall x hl)
  accuracy _ _ _ := by simp

private theorem large {x : Point (ι := ι) ε} (hx : ¬FiniteHalfPhase.Terminal x.val) :
    32 ≤ Fintype.card (Live x.val) := by
  simpa only [live_card, FiniteHalfPhase.liveCount] using FiniteHalfPhase.liveCount_large_of_nonterminal hx

def factory (reports : Reports offset A hA hN ε hε hsmall) (r : ℕ) :
    Factory (remainingPotential offset A hA) ε epochTimeLimit 22 (((1:ℝ)/2)^r) where
  sample x hx := MSManuscriptLiftedEpoch.sample offset A hA hN ε hε hsmall x (large ε hx)
    (reports.value x (large ε hx)) (reports.accuracy x (large ε hx)) r
  sound x hx := MSManuscriptLiftedEpoch.sample_sound offset A hA hN ε hε hsmall x (large ε hx)
    (reports.value x (large ε hx)) (reports.accuracy x (large ε hx)) r
  failure_le x hx := MSManuscriptLiftedEpoch.sample_failure offset A hA hN ε hε hsmall x (large ε hx)
    (reports.value x (large ε hx)) (reports.accuracy x (large ε hx)) r

/-- The only rounding branch is an explicit sign comparison at each live label. -/
def finish (x : Point (ι := ι) ε) : Point (ι := ι) ε := by
  classical
  exact if Fintype.card (Live x.val) < 32 then
    ⟨SmallLiveRounding.complete x.val, cubeRegular_of_full_signs ε _ (SmallLiveRounding.complete_isSign _)⟩
    else x

include hN in
theorem finish_sound (x : Point (ι := ι) ε) (ht : FiniteHalfPhase.Terminal x.val) :
    2*Fintype.card (Live (finish ε x).val) ≤ Fintype.card ι ∧
      remainingPotential offset A hA (finish ε x).val ≤ remainingPotential offset A hA x.val +
        64*Real.sqrt (Fintype.card ι : ℝ) := by
  classical
  unfold finish
  split_ifs with hl
  · refine ⟨?_, ?_⟩
    · change 2*Fintype.card (Live (SmallLiveRounding.complete x.val)) ≤ _
      rw [SmallLiveRounding.complete_live_card]
      omega
    · have hb := SmallLiveRounding.complete_remainingPotential_le_small_sqrt offset A hA hN x.property.1 hl
      have hc : (Fintype.card (Live x.val):ℝ) ≤ Fintype.card ι := by
        exact_mod_cast Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x.val)
      have hs := Real.sqrt_le_sqrt hc
      dsimp
      linarith
  · refine ⟨?_, ?_⟩
    · rcases ht with hf | hs
      · rw [live_card]
        have hc := frozenCoordinates_card_le x.val
        omega
      · exact False.elim (hl (by simpa only [live_card, FiniteHalfPhase.liveCount] using hs))
    · exact le_add_of_nonneg_right (by positivity)

def terminalSample (reports : Reports offset A hA hN ε hε hsmall) (r : ℕ)
    (hk : 0 < Fintype.card ι) (start : Point (ι := ι) ε) : Sampler (Option (Point (ι := ι) ε)) :=
  MSManuscriptPhase.output (factory offset A hA hN ε hε hsmall reports r)
    (by norm_num [epochTimeLimit]) hk (by norm_num) (by positivity) start 49377

def output (reports : Reports offset A hA hN ε hε hsmall) (r : ℕ)
    (hk : 0 < Fintype.card ι) (start : Point (ι := ι) ε) : Sampler (Option (Point (ι := ι) ε)) :=
  (terminalSample offset A hA hN ε hε hsmall reports r hk start).map (Option.map (finish ε))

theorem output_sound (reports : Reports offset A hA hN ε hε hsmall) (r : ℕ)
    (hk : 0 < Fintype.card ι) (start : Point (ι := ι) ε)
    (z : (output offset A hA hN ε hε hsmall reports r hk start).Draws)
    (y : Point (ι := ι) ε) (ho : (output offset A hA hN ε hε hsmall reports r hk start).value z = some y) :
    2*Fintype.card (Live y.val) ≤ Fintype.card ι ∧
      remainingPotential offset A hA y.val ≤ remainingPotential offset A hA start.val +
        squarePhaseCost*Real.sqrt (Fintype.card ι : ℝ) := by
  change ((terminalSample offset A hA hN ε hε hsmall reports r hk start).value z).map (finish ε) = some y at ho
  obtain ⟨w, hw, hwy⟩ := Option.map_eq_some_iff.mp ho
  subst y
  have ht := MSManuscriptPhase.output_sound (factory offset A hA hN ε hε hsmall reports r)
    (by norm_num [epochTimeLimit]) hk (by norm_num) (by positivity) start 49377
    (by norm_num [epochTimeLimit]) z w hw
  have hf := finish_sound offset A hA hN ε w ht.1
  refine ⟨hf.1, ?_⟩
  dsimp only [squarePhaseCost]
  norm_num only [Nat.cast_ofNat] at ht
  linarith [hf.2, ht.2]

theorem output_event_probability (reports : Reports offset A hA hN ε hε hsmall) (r : ℕ)
    (hk : 0 < Fintype.card ι) (start : Point (ι := ι) ε) :
    1-49377*((1:ℝ)/2)^r ≤ ∑ z, (output offset A hA hN ε hε hsmall reports r hk start).weight z *
      (if ((output offset A hA hN ε hε hsmall reports r hk start).value z).isSome then 1 else 0) := by
  have ht := MSManuscriptPhase.output_event_probability (factory offset A hA hN ε hε hsmall reports r)
    (by norm_num [epochTimeLimit]) hk (by norm_num) (by positivity) start 49377
  have hf := Sampler.failure_map (terminalSample offset A hA hN ε hε hsmall reports r hk start) (finish ε)
  have h1 := success_add_failure (terminalSample offset A hA hN ε hε hsmall reports r hk start)
  have h2 := success_add_failure (output offset A hA hN ε hε hsmall reports r hk start)
  change 1-49377*((1:ℝ)/2)^r ≤ (output offset A hA hN ε hε hsmall reports r hk start).expectation success
  change 1-(49377:ℝ)*((1:ℝ)/2)^r ≤ (terminalSample offset A hA hN ε hε hsmall reports r hk start).expectation success at ht
  change (output offset A hA hN ε hε hsmall reports r hk start).expectation MSManuscriptAdaptive.failure = _ at hf
  linarith

end MatrixSpencer.MSManuscriptHalfPhase
