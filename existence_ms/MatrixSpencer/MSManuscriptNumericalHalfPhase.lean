import MatrixSpencer.MSManuscriptPhase
import MatrixSpencer.SmallLiveRounding

/-!
# Adaptive numerical MS half-phase

The input factory is the actual numerical epoch sampler and its visible
correctness/probability contract. We retain every sampled branch, stop after
98,625 adaptive epoch calls, and explicitly complete a small live set.
There is no selected favorable endpoint or analytic report implementation.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalHalfPhase
open PhaseRestriction MSManuscriptAdaptive MSManuscriptPhase
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- The finite fixed-mesh run reaches at least half of timeLimit=1/1539. -/
def epochTime : ℝ := 1/3078

def epochCost : ℝ := 27

def epochCalls : ℕ := 98625

def phaseCost : ℝ := epochCost*epochCalls+64

def epochFailure (r : ℕ) : ℝ := (301/800:ℝ)^r

theorem epochTime_pos : 0 < epochTime := by norm_num [epochTime]
theorem epochCost_nonneg : 0 ≤ epochCost := by norm_num [epochCost]
theorem epochCalls_large : 32/epochTime+128 < (epochCalls:ℝ) := by norm_num [epochTime,epochCalls]
theorem phaseCost_eq : phaseCost = 2662939 := by norm_num [phaseCost,epochCost,epochCalls]
theorem phaseCost_nonneg : 0 ≤ phaseCost := by rw [phaseCost_eq]; positivity

theorem point_regular_of_signs (ε : ℝ) (x : EuclideanSpace ℝ ι) (hx : ∀ i, IsSign (x i)) :
    CubeRegular ε x := ⟨fun i => (hx i).abs_eq_one.le,fun i => Or.inl (hx i)⟩

/-- Required actual numerical epoch-return contract. Its sample contains
returned point and actual elapsed movement time, including numerical failures. -/
abbrev EpochFactory (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (ε p : ℝ) :=
  Factory (remainingPotential offset A hA) ε epochTime epochCost p

/-- The terminal small-live branch rounds each coordinate to its nearest sign. -/
def finish (ε : ℝ) (x : Point (ι := ι) ε) : Point (ι := ι) ε := by
  classical
  exact if Fintype.card (Live x.val) < 32 then
    ⟨SmallLiveRounding.complete x.val,point_regular_of_signs ε _ (SmallLiveRounding.complete_isSign _)⟩
    else x

theorem finish_sound (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1) (ε : ℝ)
    (x : Point (ι := ι) ε) (ht : FiniteHalfPhase.Terminal x.val) :
    2*Fintype.card (Live (finish ε x).val) ≤ Fintype.card ι ∧
      remainingPotential offset A hA (finish ε x).val ≤ remainingPotential offset A hA x.val +
        64*Real.sqrt (Fintype.card ι:ℝ) := by
  classical
  unfold finish
  split_ifs with hl
  · refine ⟨?_,?_⟩
    · change 2*Fintype.card (Live (SmallLiveRounding.complete x.val)) ≤ _
      rw [SmallLiveRounding.complete_live_card]
      omega
    · have hb := SmallLiveRounding.complete_remainingPotential_le_small_sqrt offset A hA hN x.property.1 hl
      have hc : (Fintype.card (Live x.val):ℝ) ≤ Fintype.card ι := by
        exact_mod_cast Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x.val)
      have hs := Real.sqrt_le_sqrt hc
      dsimp
      linarith
  · refine ⟨?_,?_⟩
    · rcases ht with hf | hs
      · rw [live_card]
        have hc := frozenCoordinates_card_le x.val
        omega
      · exact False.elim (hl (by simpa only [live_card,FiniteHalfPhase.liveCount] using hs))
    · exact le_add_of_nonneg_right (by positivity)

variable (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
  (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1) (ε p : ℝ)

def terminalSample (F : EpochFactory offset A hA ε p) (hp : 0 ≤ p)
    (hk : 0 < Fintype.card ι) (start : Point (ι := ι) ε) : Sampler (Option (Point (ι := ι) ε)) :=
  MSManuscriptPhase.output F epochTime_pos hk epochCost_nonneg hp start epochCalls

def output (F : EpochFactory offset A hA ε p) (hp : 0 ≤ p)
    (hk : 0 < Fintype.card ι) (start : Point (ι := ι) ε) : Sampler (Option (Point (ι := ι) ε)) :=
  (terminalSample offset A hA ε p F hp hk start).map (Option.map (finish ε))

include hN in
theorem output_sound (F : EpochFactory offset A hA ε p) (hp : 0 ≤ p)
    (hk : 0 < Fintype.card ι) (start : Point (ι := ι) ε)
    (z : (output offset A hA ε p F hp hk start).Draws) (y : Point (ι := ι) ε)
    (ho : (output offset A hA ε p F hp hk start).value z = some y) :
    2*Fintype.card (Live y.val) ≤ Fintype.card ι ∧
      remainingPotential offset A hA y.val ≤ remainingPotential offset A hA start.val +
        phaseCost*Real.sqrt (Fintype.card ι:ℝ) := by
  change ((terminalSample offset A hA ε p F hp hk start).value z).map (finish ε) = some y at ho
  obtain ⟨w,hw,hwy⟩ := Option.map_eq_some_iff.mp ho
  subst y
  have ht := MSManuscriptPhase.output_sound F epochTime_pos hk epochCost_nonneg hp start
    epochCalls epochCalls_large z w hw
  have hf := finish_sound offset A hA hN ε w ht.1
  refine ⟨hf.1,?_⟩
  unfold phaseCost
  linarith [hf.2,ht.2]

theorem output_event_probability (F : EpochFactory offset A hA ε p) (hp : 0 ≤ p)
    (hk : 0 < Fintype.card ι) (start : Point (ι := ι) ε) :
    1-(epochCalls:ℝ)*p ≤ ∑ z, (output offset A hA ε p F hp hk start).weight z *
      (if ((output offset A hA ε p F hp hk start).value z).isSome then 1 else 0) := by
  have ht := MSManuscriptPhase.output_event_probability F epochTime_pos hk epochCost_nonneg hp start epochCalls
  have hf := Sampler.failure_map (terminalSample offset A hA ε p F hp hk start) (finish ε)
  have h1 := success_add_failure (terminalSample offset A hA ε p F hp hk start)
  have h2 := success_add_failure (output offset A hA ε p F hp hk start)
  change 1-(epochCalls:ℝ)*p ≤ (output offset A hA ε p F hp hk start).expectation success
  change 1-(epochCalls:ℝ)*p ≤ (terminalSample offset A hA ε p F hp hk start).expectation success at ht
  change (output offset A hA ε p F hp hk start).expectation MSManuscriptAdaptive.failure = _ at hf
  linarith

theorem output_failure_le (F : EpochFactory offset A hA ε p) (hp : 0 ≤ p)
    (hk : 0 < Fintype.card ι) (start : Point (ι := ι) ε) :
    (output offset A hA ε p F hp hk start).expectation MSManuscriptAdaptive.failure ≤ (epochCalls:ℝ)*p := by
  have hs := output_event_probability offset A hA ε p F hp hk start
  have ht := success_add_failure (output offset A hA ε p F hp hk start)
  change 1-(epochCalls:ℝ)*p ≤ (output offset A hA ε p F hp hk start).expectation success at hs
  linarith

end MatrixSpencer.MSManuscriptNumericalHalfPhase
