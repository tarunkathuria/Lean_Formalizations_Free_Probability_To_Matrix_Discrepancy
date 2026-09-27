import MatrixSpencer.MSManuscriptHalfPhase
import MatrixSpencer.MSManuscriptFullProcess
import MatrixSpencer.SigningPotential


open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptFullSigning
open PhaseRestriction MSManuscriptAdaptive MSManuscriptPhase
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run
attribute [local irreducible] MSManuscriptHalfPhase.output
set_option maxRecDepth 4000
set_option maxHeartbeats 1500000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
variable (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
  (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
  (ε : ℝ) (hε : 0 < ε) (hsmall : (Fintype.card ι : ℝ)*ε ≤ 1/1000)

include hε hsmall in
theorem restricted_small (x : Point (ι := ι) ε) : (Fintype.card (Live x.val):ℝ)*ε ≤ 1/1000 := by
  have hc : (Fintype.card (Live x.val):ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x.val)
  exact (mul_le_mul_of_nonneg_right hc hε.le).trans hsmall

structure Reports where
  atPoint : ∀ x : Point (ι := ι) ε, MSManuscriptHalfPhase.Reports
    (restrictedOffset offset A hA x.val) (restrictedFamily A x.val)
    (restrictedFamily_hermitian A hA x.val) (restrictedFamily_contractions A hN x.val)
    ε hε (restricted_small ε hε hsmall x)

def analyticReports : Reports offset A hA hN ε hε hsmall where
  atPoint _ := MSManuscriptHalfPhase.analyticReports _ _ _ _ ε hε _

def sample (reports : Reports offset A hA hN ε hε hsmall) (r : ℕ)
    (x : Point (ι := ι) ε) (hx : 0 < Fintype.card (Live x.val)) : Sampler (Option (Point (ι := ι) ε)) :=
  (MSManuscriptHalfPhase.output (restrictedOffset offset A hA x.val) (restrictedFamily A x.val)
    (restrictedFamily_hermitian A hA x.val) (restrictedFamily_contractions A hN x.val)
    ε hε (restricted_small ε hε hsmall x) (reports.atPoint x) r hx
    ⟨restrictPoint x.val, restrictPoint_regular x.property⟩).map
      (Option.map (fun y => ⟨liftPoint x.val y.val, liftPoint_regular x.property y.property⟩))

theorem sample_sound (reports : Reports offset A hA hN ε hε hsmall) (r : ℕ)
    (x : Point (ι := ι) ε) (hx : 0 < Fintype.card (Live x.val))
    (z : (sample offset A hA hN ε hε hsmall reports r x hx).Draws) (y : Point (ι := ι) ε)
    (ho : (sample offset A hA hN ε hε hsmall reports r x hx).value z = some y) :
    2*Fintype.card (Live y.val) ≤ Fintype.card (Live x.val) ∧
      remainingPotential offset A hA y.val ≤ remainingPotential offset A hA x.val+
        squarePhaseCost*Real.sqrt (Fintype.card (Live x.val):ℝ) := by
  apply Sampler.map_option_sound
    (MSManuscriptHalfPhase.output (restrictedOffset offset A hA x.val) (restrictedFamily A x.val)
      (restrictedFamily_hermitian A hA x.val) (restrictedFamily_contractions A hN x.val)
      ε hε (restricted_small ε hε hsmall x) (reports.atPoint x) r hx
      ⟨restrictPoint x.val, restrictPoint_regular x.property⟩)
    (fun w : Point (ι := Live x.val) ε =>
      (⟨liftPoint x.val w.val, liftPoint_regular x.property w.property⟩ : Point (ι := ι) ε))
    (fun w => 2*Fintype.card (Live w.val) ≤ Fintype.card (Live x.val) ∧
      remainingPotential (restrictedOffset offset A hA x.val) (restrictedFamily A x.val)
        (restrictedFamily_hermitian A hA x.val) w.val ≤
      remainingPotential (restrictedOffset offset A hA x.val) (restrictedFamily A x.val)
        (restrictedFamily_hermitian A hA x.val) (restrictPoint x.val)+
      squarePhaseCost*Real.sqrt (Fintype.card (Live x.val):ℝ))
    (fun y : Point (ι := ι) ε => 2*Fintype.card (Live y.val) ≤ Fintype.card (Live x.val) ∧
      remainingPotential offset A hA y.val ≤ remainingPotential offset A hA x.val+
        squarePhaseCost*Real.sqrt (Fintype.card (Live x.val):ℝ))
    (MSManuscriptHalfPhase.output_sound _ _ _ _ ε hε _ (reports.atPoint x) r hx _)
    ?_ z y ho
  intro w ht
  refine ⟨?_, ?_⟩
  · change 2*Fintype.card (Live (liftPoint x.val w.val)) ≤ _
    rw [live_card_liftPoint]
    exact ht.1
  · have he := remainingPotential_lift_le_nested offset A hA x.val w.val
    have hs := remainingPotential_nested_start_le offset A hA x.val
    change remainingPotential offset A hA (liftPoint x.val w.val) ≤ _
    linarith [ht.2]

theorem sample_failure (reports : Reports offset A hA hN ε hε hsmall) (r : ℕ)
    (x : Point (ι := ι) ε) (hx : 0 < Fintype.card (Live x.val)) :
    (sample offset A hA hN ε hε hsmall reports r x hx).expectation MSManuscriptAdaptive.failure ≤
      49377*((1:ℝ)/2)^r := by
  unfold sample
  rw [Sampler.failure_map]
  have hp := MSManuscriptHalfPhase.output_event_probability (restrictedOffset offset A hA x.val)
    (restrictedFamily A x.val) (restrictedFamily_hermitian A hA x.val)
    (restrictedFamily_contractions A hN x.val) ε hε (restricted_small ε hε hsmall x)
    (reports.atPoint x) r hx ⟨restrictPoint x.val, restrictPoint_regular x.property⟩
  have he := success_add_failure (MSManuscriptHalfPhase.output (restrictedOffset offset A hA x.val)
    (restrictedFamily A x.val) (restrictedFamily_hermitian A hA x.val)
    (restrictedFamily_contractions A hN x.val) ε hε (restricted_small ε hε hsmall x)
    (reports.atPoint x) r hx ⟨restrictPoint x.val, restrictPoint_regular x.property⟩)
  change 1-49377*((1:ℝ)/2)^r ≤ _ at hp
  change _ + _ = 1 at he
  change 1-49377*((1:ℝ)/2)^r ≤ (MSManuscriptHalfPhase.output _ _ _ _ ε hε _ (reports.atPoint x) r hx _).expectation success at hp
  linarith

def factory (reports : Reports offset A hA hN ε hε hsmall) (r : ℕ) :
    MSManuscriptFullProcess.Factory (fun x : Point (ι := ι) ε => Fintype.card (Live x.val))
      (fun x => remainingPotential offset A hA x.val) squarePhaseCost (49377*((1:ℝ)/2)^r) where
  sample := sample offset A hA hN ε hε hsmall reports r
  sound := sample_sound offset A hA hN ε hε hsmall reports r
  failure_le := sample_failure offset A hA hN ε hε hsmall reports r

def output (reports : Reports offset A hA hN ε hε hsmall) (r : ℕ)
    (start : Point (ι := ι) ε) : Sampler (Option (Point (ι := ι) ε)) :=
  MSManuscriptFullProcess.output (factory offset A hA hN ε hε hsmall reports r)
    squarePhaseCost_nonneg (by positivity) (Fintype.card ι)
    (fun x => Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x.val)) start

theorem output_sound (reports : Reports offset A hA hN ε hε hsmall) (r : ℕ)
    (start : Point (ι := ι) ε) (z : (output offset A hA hN ε hε hsmall reports r start).Draws)
    (y : Point (ι := ι) ε) (ho : (output offset A hA hN ε hε hsmall reports r start).value z = some y) :
    (∀ i, IsSign (y.val i)) ∧ remainingPotential offset A hA y.val ≤
      remainingPotential offset A hA start.val+4*squarePhaseCost*Real.sqrt (Fintype.card (Live start.val):ℝ) := by
  have ht := MSManuscriptFullProcess.output_sound (factory offset A hA hN ε hε hsmall reports r)
    squarePhaseCost_nonneg (by positivity) (Fintype.card ι)
    (fun x => Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x.val)) start z y ho
  exact ⟨full_signs_of_live_card_zero y.val ht.1, ht.2⟩

theorem output_event_probability (reports : Reports offset A hA hN ε hε hsmall) (r : ℕ)
    (start : Point (ι := ι) ε) :
    1-((Fintype.card ι+1:ℕ):ℝ)*(49377*((1:ℝ)/2)^r) ≤
      ∑ z, (output offset A hA hN ε hε hsmall reports r start).weight z *
        (if ((output offset A hA hN ε hε hsmall reports r start).value z).isSome then 1 else 0) :=
  MSManuscriptFullProcess.output_event_probability (factory offset A hA hN ε hε hsmall reports r)
    squarePhaseCost_nonneg (by positivity) (Fintype.card ι)
    (fun x => Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x.val)) start

end MatrixSpencer.MSManuscriptFullSigning
