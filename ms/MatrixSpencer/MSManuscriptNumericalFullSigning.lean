import MatrixSpencer.MSManuscriptNumericalHalfPhase
import MatrixSpencer.MSManuscriptFullProcess
import MatrixSpencer.SigningPotential
import MatrixSpencer.PhasePotential

/-!
# Numerical adaptive full-signing composition

Each half-phase uses actual finite numerical epoch samplers supplied by the
visible `EpochProvider` interface. Restriction preserves original frozen
coefficients, lifting restores all original labels, and the full process
retains explicit failure. This module provides no analytic-report fallback.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalFullSigning
open PhaseRestriction MSManuscriptAdaptive MSManuscriptPhase MSManuscriptNumericalHalfPhase
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run
attribute [local irreducible] MSManuscriptNumericalHalfPhase.output
set_option maxRecDepth 4000
set_option maxHeartbeats 1500000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
variable (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
  (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1) (ε p : ℝ)

/-- The remaining numerical integration boundary: at every actual outer
state, supply the numerical epoch factory for its restricted family.
The factory contains actual samples, progress, cost, and failure bounds. -/
structure EpochProvider where
  atPoint : ∀ x : Point (ι := ι) ε, EpochFactory
    (restrictedOffset offset A hA x.val) (restrictedFamily A x.val)
    (restrictedFamily_hermitian A hA x.val) ε p

def sample (provider : EpochProvider offset A hA ε p) (hp : 0 ≤ p)
    (x : Point (ι := ι) ε) (hx : 0 < Fintype.card (Live x.val)) : Sampler (Option (Point (ι := ι) ε)) :=
  (MSManuscriptNumericalHalfPhase.output (restrictedOffset offset A hA x.val)
    (restrictedFamily A x.val) (restrictedFamily_hermitian A hA x.val) ε p
    (provider.atPoint x) hp hx ⟨restrictPoint x.val,restrictPoint_regular x.property⟩).map
      (Option.map (fun y => ⟨liftPoint x.val y.val,liftPoint_regular x.property y.property⟩))

include hN in
theorem sample_sound (provider : EpochProvider offset A hA ε p) (hp : 0 ≤ p)
    (x : Point (ι := ι) ε) (hx : 0 < Fintype.card (Live x.val))
    (z : (sample offset A hA ε p provider hp x hx).Draws) (y : Point (ι := ι) ε)
    (ho : (sample offset A hA ε p provider hp x hx).value z = some y) :
    2*Fintype.card (Live y.val) ≤ Fintype.card (Live x.val) ∧
      remainingPotential offset A hA y.val ≤ remainingPotential offset A hA x.val +
        phaseCost*Real.sqrt (Fintype.card (Live x.val):ℝ) := by
  apply Sampler.map_option_sound
    (MSManuscriptNumericalHalfPhase.output (restrictedOffset offset A hA x.val)
      (restrictedFamily A x.val) (restrictedFamily_hermitian A hA x.val) ε p
      (provider.atPoint x) hp hx ⟨restrictPoint x.val,restrictPoint_regular x.property⟩)
    (fun w : Point (ι := Live x.val) ε =>
      (⟨liftPoint x.val w.val,liftPoint_regular x.property w.property⟩ : Point (ι := ι) ε))
    (fun w => 2*Fintype.card (Live w.val) ≤ Fintype.card (Live x.val) ∧
      remainingPotential (restrictedOffset offset A hA x.val) (restrictedFamily A x.val)
        (restrictedFamily_hermitian A hA x.val) w.val ≤
      remainingPotential (restrictedOffset offset A hA x.val) (restrictedFamily A x.val)
        (restrictedFamily_hermitian A hA x.val) (restrictPoint x.val) +
          phaseCost*Real.sqrt (Fintype.card (Live x.val):ℝ))
    (fun y => 2*Fintype.card (Live y.val) ≤ Fintype.card (Live x.val) ∧
      remainingPotential offset A hA y.val ≤ remainingPotential offset A hA x.val +
        phaseCost*Real.sqrt (Fintype.card (Live x.val):ℝ))
    (MSManuscriptNumericalHalfPhase.output_sound _ _ _
      (restrictedFamily_contractions A hN x.val) ε p (provider.atPoint x) hp hx _)
    ?_ z y ho
  intro w ht
  refine ⟨?_,?_⟩
  · change 2*Fintype.card (Live (liftPoint x.val w.val)) ≤ _
    rw [live_card_liftPoint]
    exact ht.1
  · have he := remainingPotential_lift_le_nested offset A hA x.val w.val
    have hs := remainingPotential_nested_start_le offset A hA x.val
    change remainingPotential offset A hA (liftPoint x.val w.val) ≤ _
    linarith [ht.2]

theorem sample_failure (provider : EpochProvider offset A hA ε p) (hp : 0 ≤ p)
    (x : Point (ι := ι) ε) (hx : 0 < Fintype.card (Live x.val)) :
    (sample offset A hA ε p provider hp x hx).expectation MSManuscriptAdaptive.failure ≤ (epochCalls:ℝ)*p := by
  unfold sample
  rw [Sampler.failure_map]
  exact MSManuscriptNumericalHalfPhase.output_failure_le _ _ _ ε p (provider.atPoint x) hp hx _

def factory (provider : EpochProvider offset A hA ε p) (hp : 0 ≤ p) :
    MSManuscriptFullProcess.Factory (fun x : Point (ι := ι) ε => Fintype.card (Live x.val))
      (fun x => remainingPotential offset A hA x.val) phaseCost ((epochCalls:ℝ)*p) where
  sample := sample offset A hA ε p provider hp
  sound := sample_sound offset A hA hN ε p provider hp
  failure_le := sample_failure offset A hA ε p provider hp

def output (provider : EpochProvider offset A hA ε p) (hp : 0 ≤ p)
    (start : Point (ι := ι) ε) : Sampler (Option (Point (ι := ι) ε)) :=
  MSManuscriptFullProcess.output (factory offset A hA hN ε p provider hp)
    phaseCost_nonneg (by positivity) (Fintype.card ι)
    (fun x => Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x.val)) start

theorem output_sound (provider : EpochProvider offset A hA ε p) (hp : 0 ≤ p)
    (start : Point (ι := ι) ε) (z : (output offset A hA hN ε p provider hp start).Draws)
    (y : Point (ι := ι) ε) (ho : (output offset A hA hN ε p provider hp start).value z = some y) :
    (∀ i, IsSign (y.val i)) ∧ remainingPotential offset A hA y.val ≤
      remainingPotential offset A hA start.val+4*phaseCost*Real.sqrt (Fintype.card (Live start.val):ℝ) := by
  have ht := MSManuscriptFullProcess.output_sound (factory offset A hA hN ε p provider hp)
    phaseCost_nonneg (by positivity) (Fintype.card ι)
    (fun x => Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x.val)) start z y ho
  exact ⟨full_signs_of_live_card_zero y.val ht.1,ht.2⟩

theorem output_event_probability (provider : EpochProvider offset A hA ε p) (hp : 0 ≤ p)
    (start : Point (ι := ι) ε) :
    1-((Fintype.card ι+1:ℕ):ℝ)*((epochCalls:ℝ)*p) ≤
      ∑ z, (output offset A hA hN ε p provider hp start).weight z *
        (if ((output offset A hA hN ε p provider hp start).value z).isSome then 1 else 0) :=
  MSManuscriptFullProcess.output_event_probability (factory offset A hA hN ε p provider hp)
    phaseCost_nonneg (by positivity) (Fintype.card ι)
    (fun x => Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x.val)) start

end MatrixSpencer.MSManuscriptNumericalFullSigning
