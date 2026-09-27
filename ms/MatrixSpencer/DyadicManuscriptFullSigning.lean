import MatrixSpencer.DyadicManuscriptHalfPhase
import MatrixSpencer.MSManuscriptFullProcess
import MatrixSpencer.SigningPotential


open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.DyadicManuscriptFullSigning
open PhaseRestriction MSManuscriptAdaptive MSManuscriptPhase
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run
set_option maxRecDepth 4000
set_option maxHeartbeats 1500000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
variable (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (B : ℝ) (hB : 2 ≤ B)
variable (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
  (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
  (ε : ℝ) (hε : 0 < ε) (hsmall : (Fintype.card ι : ℝ)*ε ≤ 1/1000)

include hε hsmall in
theorem restricted_small (x : Point (ι := ι) ε) : (Fintype.card (Live x.val):ℝ)*ε ≤ 1/1000 := by
  have hc : (Fintype.card (Live x.val):ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x.val)
  exact (mul_le_mul_of_nonneg_right hc hε.le).trans hsmall

variable (hinputs : DyadicPhasePotential.HasEpochInputs n m θ B (Fintype.card ι))

def restricted_inputs (x : Point (ι := ι) ε) :
    DyadicPhasePotential.HasEpochInputs n m θ B (Fintype.card (Live x.val)) := by
  intro κ _ _ c hm hθ hB hc
  exact hinputs κ c hm hθ hB (hc.trans (Fintype.card_subtype_le _))

structure Reports where
  atPoint : ∀ x : Point (ι := ι) ε, DyadicManuscriptHalfPhase.Reports m hm θ hθ B hB
    (restrictedOffset offset A hA x.val) (restrictedFamily A x.val)
    (restrictedFamily_hermitian A hA x.val) (restrictedFamily_contractions A hN x.val)
    ε hε (restricted_small ε hε hsmall x) (restricted_inputs m θ B ε hinputs x)

def analyticReports : Reports m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs where
  atPoint _ := DyadicManuscriptHalfPhase.analyticReports m hm θ hθ B hB _ _ _ _ ε hε _ _

def sample (reports : Reports m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs) (r : ℕ)
    (x : Point (ι := ι) ε) (hx : 0 < Fintype.card (Live x.val)) : Sampler (Option (Point (ι := ι) ε)) :=
  (DyadicManuscriptHalfPhase.output m hm θ hθ B hB (restrictedOffset offset A hA x.val) (restrictedFamily A x.val)
    (restrictedFamily_hermitian A hA x.val) (restrictedFamily_contractions A hN x.val)
    ε hε (restricted_small ε hε hsmall x) (restricted_inputs m θ B ε hinputs x) (reports.atPoint x) r hx
    ⟨restrictPoint x.val, restrictPoint_regular x.property⟩).map
      (Option.map (fun y => ⟨liftPoint x.val y.val, liftPoint_regular x.property y.property⟩))

theorem sample_sound (reports : Reports m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs) (r : ℕ)
    (x : Point (ι := ι) ε) (hx : 0 < Fintype.card (Live x.val))
    (z : (sample m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r x hx).Draws) (y : Point (ι := ι) ε)
    (ho : (sample m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r x hx).value z = some y) :
    2*Fintype.card (Live y.val) ≤ Fintype.card (Live x.val) ∧
      rectangularRemainingPotential m θ offset A hA y.val ≤ rectangularRemainingPotential m θ offset A hA x.val+
        (DyadicHalfPhase.phaseCost B)*Real.sqrt (Fintype.card (Live x.val):ℝ) := by
  unfold sample Sampler.map at ho
  obtain ⟨w, hw, hwy⟩ := Option.map_eq_some_iff.mp ho
  subst y
  have ht := DyadicManuscriptHalfPhase.output_sound m hm θ hθ B hB (restrictedOffset offset A hA x.val)
    (restrictedFamily A x.val) (restrictedFamily_hermitian A hA x.val)
    (restrictedFamily_contractions A hN x.val) ε hε (restricted_small ε hε hsmall x) (restricted_inputs m θ B ε hinputs x)
    (reports.atPoint x) r hx ⟨restrictPoint x.val, restrictPoint_regular x.property⟩ z w hw
  refine ⟨?_, ?_⟩
  · change 2*Fintype.card (Live (liftPoint x.val w.val)) ≤ _
    rw [live_card_liftPoint]
    exact ht.1
  · have he := rectangularRemainingPotential_lift_le_nested m θ offset A hA x.val w.val
    have hs := rectangularRemainingPotential_nested_start_le m θ offset A hA x.val
    change rectangularRemainingPotential m θ offset A hA (liftPoint x.val w.val) ≤ _
    linarith [ht.2]

theorem sample_failure (reports : Reports m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs) (r : ℕ)
    (x : Point (ι := ι) ε) (hx : 0 < Fintype.card (Live x.val)) :
    (sample m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r x hx).expectation MSManuscriptAdaptive.failure ≤
      (RectangularEpochParameters.count B : ℝ)*((1:ℝ)/2)^r := by
  unfold sample
  rw [Sampler.failure_map]
  have hp := DyadicManuscriptHalfPhase.output_event_probability m hm θ hθ B hB (restrictedOffset offset A hA x.val)
    (restrictedFamily A x.val) (restrictedFamily_hermitian A hA x.val)
    (restrictedFamily_contractions A hN x.val) ε hε (restricted_small ε hε hsmall x) (restricted_inputs m θ B ε hinputs x)
    (reports.atPoint x) r hx ⟨restrictPoint x.val, restrictPoint_regular x.property⟩
  have he := success_add_failure (DyadicManuscriptHalfPhase.output m hm θ hθ B hB (restrictedOffset offset A hA x.val)
    (restrictedFamily A x.val) (restrictedFamily_hermitian A hA x.val)
    (restrictedFamily_contractions A hN x.val) ε hε (restricted_small ε hε hsmall x) (restricted_inputs m θ B ε hinputs x)
    (reports.atPoint x) r hx ⟨restrictPoint x.val, restrictPoint_regular x.property⟩)
  change 1-(RectangularEpochParameters.count B : ℝ)*((1:ℝ)/2)^r ≤ _ at hp
  change _ + _ = 1 at he
  change 1-(RectangularEpochParameters.count B : ℝ)*((1:ℝ)/2)^r ≤ (DyadicManuscriptHalfPhase.output m hm θ hθ B hB _ _ _ _ ε hε _ (restricted_inputs m θ B ε hinputs x) (reports.atPoint x) r hx _).expectation success at hp
  linarith

def factory (reports : Reports m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs) (r : ℕ) :
    MSManuscriptFullProcess.Factory (fun x : Point (ι := ι) ε => Fintype.card (Live x.val))
      (fun x => rectangularRemainingPotential m θ offset A hA x.val) (DyadicHalfPhase.phaseCost B) ((RectangularEpochParameters.count B : ℝ)*((1:ℝ)/2)^r) where
  sample := sample m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r
  sound := sample_sound m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r
  failure_le := sample_failure m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r

def output (reports : Reports m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs) (r : ℕ)
    (start : Point (ι := ι) ε) : Sampler (Option (Point (ι := ι) ε)) :=
  MSManuscriptFullProcess.output (factory m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r)
    (DyadicHalfPhase.phaseCost_nonneg hB) (by positivity) (Fintype.card ι)
    (fun x => Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x.val)) start

theorem output_sound (reports : Reports m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs) (r : ℕ)
    (start : Point (ι := ι) ε) (z : (output m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r start).Draws)
    (y : Point (ι := ι) ε) (ho : (output m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r start).value z = some y) :
    (∀ i, IsSign (y.val i)) ∧ rectangularRemainingPotential m θ offset A hA y.val ≤
      rectangularRemainingPotential m θ offset A hA start.val+4*(DyadicHalfPhase.phaseCost B)*Real.sqrt (Fintype.card (Live start.val):ℝ) := by
  have ht := MSManuscriptFullProcess.output_sound (factory m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r)
    (DyadicHalfPhase.phaseCost_nonneg hB) (by positivity) (Fintype.card ι)
    (fun x => Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x.val)) start z y ho
  exact ⟨full_signs_of_live_card_zero y.val ht.1, ht.2⟩

theorem output_event_probability (reports : Reports m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs) (r : ℕ)
    (start : Point (ι := ι) ε) :
    1-((Fintype.card ι+1:ℕ):ℝ)*((RectangularEpochParameters.count B : ℝ)*((1:ℝ)/2)^r) ≤
      ∑ z, (output m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r start).weight z *
        (if ((output m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r start).value z).isSome then 1 else 0) :=
  MSManuscriptFullProcess.output_event_probability (factory m hm θ hθ B hB offset A hA hN ε hε hsmall hinputs reports r)
    (DyadicHalfPhase.phaseCost_nonneg hB) (by positivity) (Fintype.card ι)
    (fun x => Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x.val)) start

end MatrixSpencer.DyadicManuscriptFullSigning
