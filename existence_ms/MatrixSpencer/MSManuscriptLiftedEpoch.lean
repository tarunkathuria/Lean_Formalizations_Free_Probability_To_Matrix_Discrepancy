import MatrixSpencer.MSManuscriptEpoch
import MatrixSpencer.MSManuscriptPhase
import MatrixSpencer.PhasePotential

/-! The actual sampled restricted epoch is lifted back to all original labels.
The report-accuracy premise is numerical; no successful leaf is supplied. -/
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer.MSManuscriptLiftedEpoch
open PhaseRestriction MSManuscriptAdaptive MSManuscriptPhase
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

variable (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
  (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
  (ε : ℝ) (hε : 0 < ε) (hsmall : (Fintype.card ι : ℝ)*ε ≤ 1/1000)

abbrev cfg (x : Point (ι := ι) ε) (hl : 32 ≤ Fintype.card (Live x.val)) :=
  epochConfig offset A hA hN x.val ε hε hsmall x.property hl

theorem good_advance (x : Point (ι := ι) ε) (hl : 32 ≤ Fintype.card (Live x.val))
    (s : EpochState (Live x.val)) (hs : EpochGoodEndpoint (cfg offset A hA hN ε hε hsmall x hl) s) :
    FiniteHalfPhase.EpochAdvance (remainingPotential offset A hA) epochTimeLimit 22
      x.val (liftPoint x.val s.point) s.time := by
  let c := cfg offset A hA hN ε hε hsmall x hl
  refine ⟨(liftPoint_regular x.property hs.invariant.regular).1,
    frozen_subset_liftPoint _ _, hs.invariant.time_nonneg, ?_, ?_, ?_⟩
  · simpa only [live_card, FiniteHalfPhase.liveCount] using
      norm_gain_liftPoint x.val s.point _ hs.invariant.norm_progress
  · rcases hs.successful with ht | hf
    · exact Or.inl ht.ge
    · right
      rw [frozen_card_gain_real]
      simpa only [live_card, FiniteHalfPhase.liveCount] using hf
  · have hdrop := remainingPotential_lift_le offset A hA x.val s.point
    change remainingPotential offset A hA (liftPoint x.val s.point) ≤
      ownerPotential (c.center s.point) c.matrices 1 1 at hdrop
    have hbase : ownerPotential c.anchor c.matrices 1 1 = remainingPotential offset A hA x.val := by
      have hc := center_liftPoint offset A hA x.val (restrictPoint x.val)
      rw [liftPoint_restrictPoint] at hc
      change ownerPotential (epochCenter (restrictedOffset offset A hA x.val) (restrictedFamily A x.val)
          (restrictedFamily_hermitian A hA x.val) (restrictPoint x.val)) (restrictedFamily A x.val) 1 1 = _
      rw [← hc]
      rfl
    have hg := hs.reset_growth
    change ownerPotential (c.center s.point) c.matrices 1 1 - ownerPotential c.anchor c.matrices 1 1 ≤ _ at hg
    rw [hbase] at hg
    rw [FiniteHalfPhase.liveCount, ← live_card]
    linarith

def epochSampler (c : EpochConfig ι n) (report : EpochState ι → ℝ) (r : ℕ) : Sampler (Option (EpochState ι)) where
  Draws := MSManuscriptEpoch.Draws c r
  fintypeDraws := inferInstance
  weight := MSManuscriptEpoch.drawWeight c r
  value := MSManuscriptEpoch.output c report r
  weight_nonneg := MSManuscriptEpoch.drawWeight_nonneg c r
  weight_sum := MSManuscriptEpoch.drawWeight_sum c r

theorem epochSampler_failure (c : EpochConfig ι n) (report : EpochState ι → ℝ)
    (hreport : MSManuscriptEpoch.ReportAccuracy c report) (r : ℕ) :
    (epochSampler c report r).expectation MSManuscriptAdaptive.failure ≤ ((1:ℝ)/2)^r := by
  have hp := MSManuscriptEpoch.output_event_probability_ge c report hreport r
  have ht := success_add_failure (epochSampler c report r)
  change 1-((1:ℝ)/2)^r ≤ (epochSampler c report r).expectation success at hp
  linarith

def sample (x : Point (ι := ι) ε) (hl : 32 ≤ Fintype.card (Live x.val))
    (report : EpochState (Live x.val) → ℝ)
    (hreport : MSManuscriptEpoch.ReportAccuracy (cfg offset A hA hN ε hε hsmall x hl) report)
    (r : ℕ) : Sampler (Option (Point (ι := ι) ε × ℝ)) :=
  let c := cfg offset A hA hN ε hε hsmall x hl
  let P := (epochSampler c report r).certify (EpochGoodEndpoint c)
    (MSManuscriptEpoch.output_sound c report hreport r)
  P.map (Option.map (fun s =>
    (⟨liftPoint x.val s.val.point, liftPoint_regular x.property s.property.invariant.regular⟩,
      s.val.time)))

theorem sample_sound (x : Point (ι := ι) ε) (hl : 32 ≤ Fintype.card (Live x.val))
    (report : EpochState (Live x.val) → ℝ)
    (hreport : MSManuscriptEpoch.ReportAccuracy (cfg offset A hA hN ε hε hsmall x hl) report)
    (r : ℕ) (z : (sample offset A hA hN ε hε hsmall x hl report hreport r).Draws) (y : Point (ι := ι) ε × ℝ)
    (ho : (sample offset A hA hN ε hε hsmall x hl report hreport r).value z = some y) :
    FiniteHalfPhase.EpochAdvance (remainingPotential offset A hA) epochTimeLimit 22 x.val y.1.val y.2 := by
  unfold sample Sampler.map at ho
  obtain ⟨s, _, hy⟩ := Option.map_eq_some_iff.mp ho
  subst y
  exact good_advance offset A hA hN ε hε hsmall x hl s.val s.property

theorem sample_failure (x : Point (ι := ι) ε) (hl : 32 ≤ Fintype.card (Live x.val))
    (report : EpochState (Live x.val) → ℝ)
    (hreport : MSManuscriptEpoch.ReportAccuracy (cfg offset A hA hN ε hε hsmall x hl) report) (r : ℕ) :
    (sample offset A hA hN ε hε hsmall x hl report hreport r).expectation MSManuscriptAdaptive.failure ≤ ((1:ℝ)/2)^r := by
  unfold sample
  rw [Sampler.failure_map, Sampler.failure_certify]
  exact epochSampler_failure _ report hreport r

end MatrixSpencer.MSManuscriptLiftedEpoch
