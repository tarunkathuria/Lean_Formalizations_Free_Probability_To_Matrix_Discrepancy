import MatrixSpencer.DyadicManuscriptEpoch
import MatrixSpencer.MSManuscriptPhase
import MatrixSpencer.DyadicPhasePotential

/-! The actual sampled restricted epoch is lifted back to all original labels.
The report-accuracy premise is numerical; no successful leaf is supplied. -/
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer.DyadicManuscriptLiftedEpoch
open PhaseRestriction MSManuscriptAdaptive MSManuscriptPhase
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

variable (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (B : ℝ) (hB : 2 ≤ B)
variable (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
  (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
  (ε : ℝ) (hε : 0 < ε) (hsmall : (Fintype.card ι : ℝ)*ε ≤ 1/1000)

abbrev cfg (x : Point (ι := ι) ε) (hl : 32 ≤ Fintype.card (Live x.val)) :=
  DyadicPhasePotential.epochConfig m hm θ hθ B hB offset A hA hN x.val ε hε hsmall x.property hl

theorem good_advance (x : Point (ι := ι) ε) (hl : 32 ≤ Fintype.card (Live x.val))
    (s : DyadicEpochState (Live x.val)) (hs : DyadicEpochGoodEndpoint (cfg m hm θ hθ B hB offset A hA hN ε hε hsmall x hl) s) :
    FiniteHalfPhase.EpochAdvance (rectangularRemainingPotential m θ offset A hA) (RectangularEpochParameters.duration B) 22
      x.val (liftPoint x.val s.point) s.time := by
  let c := cfg m hm θ hθ B hB offset A hA hN ε hε hsmall x hl
  refine ⟨(liftPoint_regular x.property hs.invariant.regular).1,
    frozen_subset_liftPoint _ _, hs.invariant.time_nonneg, ?_, ?_, ?_⟩
  · simpa only [live_card, FiniteHalfPhase.liveCount] using
      norm_gain_liftPoint x.val s.point _ hs.invariant.norm_progress
  · rcases hs.successful with ht | hf
    · exact Or.inl ht.ge
    · right
      rw [frozen_card_gain_real]
      simpa only [live_card, FiniteHalfPhase.liveCount] using hf
  · have hdrop := rectangularRemainingPotential_lift_le m θ offset A hA x.val s.point
    change rectangularRemainingPotential m θ offset A hA (liftPoint x.val s.point) ≤
      c.potential (c.center s.point) 1 at hdrop
    have hbase : c.potential c.anchor 1 = rectangularRemainingPotential m θ offset A hA x.val := by
      have hc := center_liftPoint offset A hA x.val (restrictPoint x.val)
      rw [liftPoint_restrictPoint] at hc
      change regularizedOwnerPotential
        (epochCenter (restrictedOffset offset A hA x.val) (restrictedFamily A x.val)
          (restrictedFamily_hermitian A hA x.val) (restrictPoint x.val)) (restrictedFamily A x.val) 1
          (dyadicTsallisRegularizer m θ) = _
      rw [← hc]
      rfl
    have hg := hs.reset_growth
    change c.potential (c.center s.point) 1 - c.potential c.anchor 1 ≤ _ at hg
    rw [hbase] at hg
    rw [FiniteHalfPhase.liveCount, ← live_card]
    linarith

def epochSampler (c : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs c) (report : DyadicEpochState ι → ℝ) (r : ℕ) : Sampler (Option (DyadicEpochState ι)) where
  Draws := DyadicManuscriptEpoch.Draws c inputs r
  fintypeDraws := inferInstance
  weight := DyadicManuscriptEpoch.drawWeight c inputs r
  value := DyadicManuscriptEpoch.output c inputs report r
  weight_nonneg := DyadicManuscriptEpoch.drawWeight_nonneg c inputs r
  weight_sum := DyadicManuscriptEpoch.drawWeight_sum c inputs r

theorem epochSampler_failure (c : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs c) (report : DyadicEpochState ι → ℝ)
    (hreport : DyadicManuscriptEpoch.ReportAccuracy c inputs report) (r : ℕ) :
    (epochSampler c inputs report r).expectation MSManuscriptAdaptive.failure ≤ ((1:ℝ)/2)^r := by
  have hp := DyadicManuscriptEpoch.output_event_probability_ge c inputs report hreport r
  have ht := success_add_failure (epochSampler c inputs report r)
  change 1-((1:ℝ)/2)^r ≤ (epochSampler c inputs report r).expectation success at hp
  linarith

def sample (x : Point (ι := ι) ε) (hl : 32 ≤ Fintype.card (Live x.val))
    (inputs : DyadicEpochAnalyticInputs (cfg m hm θ hθ B hB offset A hA hN ε hε hsmall x hl))
    (report : DyadicEpochState (Live x.val) → ℝ)
    (hreport : DyadicManuscriptEpoch.ReportAccuracy (cfg m hm θ hθ B hB offset A hA hN ε hε hsmall x hl) inputs report)
    (r : ℕ) : Sampler (Option (Point (ι := ι) ε × ℝ)) :=
  let c := cfg m hm θ hθ B hB offset A hA hN ε hε hsmall x hl
  let P := (epochSampler c inputs report r).certify (DyadicEpochGoodEndpoint c)
    (DyadicManuscriptEpoch.output_sound c inputs report hreport r)
  P.map (Option.map (fun s =>
    (⟨liftPoint x.val s.val.point, liftPoint_regular x.property s.property.invariant.regular⟩,
      s.val.time)))

theorem sample_sound (x : Point (ι := ι) ε) (hl : 32 ≤ Fintype.card (Live x.val))
    (inputs : DyadicEpochAnalyticInputs (cfg m hm θ hθ B hB offset A hA hN ε hε hsmall x hl))
    (report : DyadicEpochState (Live x.val) → ℝ)
    (hreport : DyadicManuscriptEpoch.ReportAccuracy (cfg m hm θ hθ B hB offset A hA hN ε hε hsmall x hl) inputs report)
    (r : ℕ) (z : (sample m hm θ hθ B hB offset A hA hN ε hε hsmall x hl inputs report hreport r).Draws) (y : Point (ι := ι) ε × ℝ)
    (ho : (sample m hm θ hθ B hB offset A hA hN ε hε hsmall x hl inputs report hreport r).value z = some y) :
    FiniteHalfPhase.EpochAdvance (rectangularRemainingPotential m θ offset A hA) (RectangularEpochParameters.duration B) 22 x.val y.1.val y.2 := by
  unfold sample Sampler.map at ho
  obtain ⟨s, _, hy⟩ := Option.map_eq_some_iff.mp ho
  subst y
  exact good_advance m hm θ hθ B hB offset A hA hN ε hε hsmall x hl s.val s.property

theorem sample_failure (x : Point (ι := ι) ε) (hl : 32 ≤ Fintype.card (Live x.val))
    (inputs : DyadicEpochAnalyticInputs (cfg m hm θ hθ B hB offset A hA hN ε hε hsmall x hl))
    (report : DyadicEpochState (Live x.val) → ℝ)
    (hreport : DyadicManuscriptEpoch.ReportAccuracy (cfg m hm θ hθ B hB offset A hA hN ε hε hsmall x hl) inputs report) (r : ℕ) :
    (sample m hm θ hθ B hB offset A hA hN ε hε hsmall x hl inputs report hreport r).expectation MSManuscriptAdaptive.failure ≤ ((1:ℝ)/2)^r := by
  unfold sample
  rw [Sampler.failure_map, Sampler.failure_certify]
  exact epochSampler_failure _ inputs report hreport r

end MatrixSpencer.DyadicManuscriptLiftedEpoch
