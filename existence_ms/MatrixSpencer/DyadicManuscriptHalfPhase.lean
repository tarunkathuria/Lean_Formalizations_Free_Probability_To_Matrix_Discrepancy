import MatrixSpencer.DyadicManuscriptLiftedEpoch
import MatrixSpencer.DyadicHalfPhase
import MatrixSpencer.ActualHalfPhase


open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
namespace MatrixSpencer.DyadicManuscriptHalfPhase
open PhaseRestriction MSManuscriptAdaptive MSManuscriptPhase
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
universe u v
variable (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (B : ℝ) (hB : 2 ≤ B)
variable (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
  (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
  (ε : ℝ) (hε : 0 < ε) (hsmall : (Fintype.card ι : ℝ)*ε ≤ 1/1000)

def inputs (x : Point (ι := ι) ε) (hl : 32 ≤ Fintype.card (Live x.val))
    (hinputs : DyadicPhasePotential.HasEpochInputs n m θ B (Fintype.card ι)) :
    DyadicEpochAnalyticInputs (DyadicManuscriptLiftedEpoch.cfg m hm θ hθ B hB offset A hA hN ε hε hsmall x hl) :=
  Classical.choice (hinputs (Live x.val) _ rfl rfl rfl (Fintype.card_subtype_le _))

variable (hinputs : DyadicPhasePotential.HasEpochInputs n m θ B (Fintype.card ι))

structure Reports where
  value : ∀ (x : Point (ι := ι) ε) (_hl : 32 ≤ Fintype.card (Live x.val)), DyadicEpochState (Live x.val) → ℝ
  accuracy : ∀ x hl, DyadicManuscriptEpoch.ReportAccuracy
    (DyadicManuscriptLiftedEpoch.cfg m hm θ hθ B hB offset A hA hN ε hε hsmall x hl) (inputs m hm θ hθ B hB offset A hA hN ε hε hsmall x hl hinputs) (value x hl)

def analyticReports : Reports m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs where
  value x hl := DyadicManuscriptEpoch.score (DyadicManuscriptLiftedEpoch.cfg m hm θ hθ B hB offset A hA hN ε hε hsmall x hl) (inputs m hm θ hθ B hB offset A hA hN ε hε hsmall x hl hinputs)
  accuracy _ _ _ := by simp

private theorem large {x : Point (ι := ι) ε} (hx : ¬FiniteHalfPhase.Terminal x.val) :
    32 ≤ Fintype.card (Live x.val) := by
  simpa only [live_card, FiniteHalfPhase.liveCount] using FiniteHalfPhase.liveCount_large_of_nonterminal hx

def factory (reports : Reports m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs) (r : ℕ) :
    Factory (rectangularRemainingPotential m θ offset A hA) ε (RectangularEpochParameters.duration B) 22 (((1:ℝ)/2)^r) where
  sample x hx := DyadicManuscriptLiftedEpoch.sample m hm θ hθ B hB offset A hA hN ε hε hsmall x (large ε hx)
    (inputs m hm θ hθ B hB offset A hA hN ε hε hsmall x (large ε hx) hinputs)
    (reports.value x (large ε hx)) (reports.accuracy x (large ε hx)) r
  sound x hx := DyadicManuscriptLiftedEpoch.sample_sound m hm θ hθ B hB offset A hA hN ε hε hsmall x (large ε hx)
    (inputs m hm θ hθ B hB offset A hA hN ε hε hsmall x (large ε hx) hinputs)
    (reports.value x (large ε hx)) (reports.accuracy x (large ε hx)) r
  failure_le x hx := DyadicManuscriptLiftedEpoch.sample_failure m hm θ hθ B hB offset A hA hN ε hε hsmall x (large ε hx)
    (inputs m hm θ hθ B hB offset A hA hN ε hε hsmall x (large ε hx) hinputs)
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
      rectangularRemainingPotential m θ offset A hA (finish ε x).val ≤ rectangularRemainingPotential m θ offset A hA x.val +
        64*Real.sqrt (Fintype.card ι : ℝ) := by
  classical
  unfold finish
  split_ifs with hl
  · refine ⟨?_, ?_⟩
    · change 2*Fintype.card (Live (SmallLiveRounding.complete x.val)) ≤ _
      rw [SmallLiveRounding.complete_live_card]
      omega
    · have hb := DyadicSmallLiveRounding.complete_remainingPotential_le_small_sqrt m θ offset A hA hN x.property.1 hl
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

def terminalSample (reports : Reports m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs) (r : ℕ)
    (hk : 0 < Fintype.card ι) (start : Point (ι := ι) ε) : Sampler (Option (Point (ι := ι) ε)) :=
  MSManuscriptPhase.output (factory m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r)
    (RectangularEpochParameters.duration_pos hB) hk (by norm_num) (by positivity) start (RectangularEpochParameters.count B)

def output (reports : Reports m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs) (r : ℕ)
    (hk : 0 < Fintype.card ι) (start : Point (ι := ι) ε) : Sampler (Option (Point (ι := ι) ε)) :=
  (terminalSample m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r hk start).map (Option.map (finish ε))

theorem output_sound (reports : Reports m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs) (r : ℕ)
    (hk : 0 < Fintype.card ι) (start : Point (ι := ι) ε)
    (z : (output m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r hk start).Draws)
    (y : Point (ι := ι) ε) (ho : (output m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r hk start).value z = some y) :
    2*Fintype.card (Live y.val) ≤ Fintype.card ι ∧
      rectangularRemainingPotential m θ offset A hA y.val ≤ rectangularRemainingPotential m θ offset A hA start.val +
        DyadicHalfPhase.phaseCost B*Real.sqrt (Fintype.card ι : ℝ) := by
  change ((terminalSample m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r hk start).value z).map (finish ε) = some y at ho
  obtain ⟨w, hw, hwy⟩ := Option.map_eq_some_iff.mp ho
  subst y
  have ht := MSManuscriptPhase.output_sound (factory m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r)
    (RectangularEpochParameters.duration_pos hB) hk (by norm_num) (by positivity) start (RectangularEpochParameters.count B)
    (RectangularEpochParameters.count_sufficient hB) z w hw
  have hf := finish_sound m θ offset A hA hN ε w ht.1
  refine ⟨hf.1, ?_⟩
  have hc := RectangularEpochParameters.count_le hB
  have hb := DyadicHalfPhase.phaseCost_covers_rounding hB
  have hs := Real.sqrt_nonneg (Fintype.card ι : ℝ)
  have hmul := mul_le_mul_of_nonneg_right hc hs
  nlinarith [hf.2, ht.2]

theorem output_event_probability (reports : Reports m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs) (r : ℕ)
    (hk : 0 < Fintype.card ι) (start : Point (ι := ι) ε) :
    1-(RectangularEpochParameters.count B : ℝ)*((1:ℝ)/2)^r ≤ ∑ z, (output m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r hk start).weight z *
      (if ((output m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r hk start).value z).isSome then 1 else 0) := by
  have ht := MSManuscriptPhase.output_event_probability (factory m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r)
    (RectangularEpochParameters.duration_pos hB) hk (by norm_num) (by positivity) start (RectangularEpochParameters.count B)
  have hf := Sampler.failure_map (terminalSample m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r hk start) (finish ε)
  have h1 := success_add_failure (terminalSample m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r hk start)
  have h2 := success_add_failure (output m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r hk start)
  change 1-(RectangularEpochParameters.count B : ℝ)*((1:ℝ)/2)^r ≤ (output m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r hk start).expectation success
  change 1-(RectangularEpochParameters.count B : ℝ)*((1:ℝ)/2)^r ≤ (terminalSample m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r hk start).expectation success at ht
  change (output m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r hk start).expectation MSManuscriptAdaptive.failure = _ at hf
  linarith

end MatrixSpencer.DyadicManuscriptHalfPhase
