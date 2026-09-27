import MatrixSpencer.RectangularRidgePhaseProgress
import MatrixSpencer.MSManuscriptSamplerTools
import MatrixSpencer.SmallLiveRounding

/-!
# Finite composition of original-universe epochs

This is a sampler combinator, with its epoch sampler supplied explicitly.
The epoch interface is to be instantiated by the concrete numerical epoch;
the theorems here do not assert that interface exists. Every sampled branch
is retained and failure remains an explicit `none` output.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgePhaseAssembly
open RectangularRidgeRemainingPotential RectangularRidgePhaseProgress MSManuscriptAdaptive
variable {N : ℕ}

abbrev Point (ε : ℝ) := {x : EuclideanSpace ℝ (Fin N) // CubeRegular ε x}

structure EpochFactory (f : EuclideanSpace ℝ (Fin N) → ℝ) (ε τ K p : ℝ) where
  sample : ∀ x : Point (N := N) ε, 32 ≤ liveCount x.val → Sampler (Option (Point (N := N) ε × ℝ))
  sound : ∀ x hx z y, (sample x hx).value z = some y →
    FiniteHalfPhase.EpochAdvance f τ K x.val y.1.val y.2
  failure_le : ∀ x hx, (sample x hx).expectation failure ≤ p

abbrev PhasePoint {ε : ℝ} (start : Point (N := N) ε) :=
  {x : Point (N := N) ε // frozenCoordinates start.val ⊆ frozenCoordinates x.val}

variable {f : EuclideanSpace ℝ (Fin N) → ℝ} {ε τ K p : ℝ}

def rawStep (F : EpochFactory f ε τ K p) (start : Point (N := N) ε) (x : PhasePoint start) :
    Sampler (Option (PhasePoint start)) := by
  classical
  by_cases ht : terminal start.val x.val.val
  · exact Sampler.pure (some x)
  · have hx : 32 ≤ liveCount x.val.val := Nat.le_of_not_gt (fun h => ht (Or.inr h))
    let T := F.sample x.val hx
    exact {
      Draws := T.Draws
      fintypeDraws := inferInstance
      weight := T.weight
      value z := match he : T.value z with
        | none => none
        | some y => some ⟨y.1, x.property.trans (F.sound x.val hx z y he).frozen⟩
      weight_nonneg := T.weight_nonneg
      weight_sum := T.weight_sum }

theorem rawStep_sound (F : EpochFactory f ε τ K p) (hτ : 0 < τ) (hK : 0 ≤ K)
    (start : Point (N := N) ε) (hs : 0 < liveCount start.val) (x : PhasePoint start)
    (hx : ¬terminal start.val x.val.val) (z : (rawStep F start x).Draws)
    (y : PhasePoint start) (ho : (rawStep F start x).value z = some y) :
    progress τ start.val x.val.val + 1 ≤ progress τ start.val y.val.val ∧
      f y.val.val ≤ f x.val.val + K * Real.sqrt (liveCount start.val : ℝ) := by
  have hall : ∀ (z : (rawStep F start x).Draws) (y : PhasePoint start),
      (rawStep F start x).value z = some y →
      progress τ start.val x.val.val + 1 ≤ progress τ start.val y.val.val ∧
        f y.val.val ≤ f x.val.val + K * Real.sqrt (liveCount start.val : ℝ) := by
    classical
    unfold rawStep
    rw [dif_neg hx]
    intro z y ho
    dsimp only at ho
    split at ho
    · contradiction
    · rename_i w hw
      have hy := Option.some.inj ho
      subst y
      have ha := F.sound x.val _ z w hw
      have hl := Real.sqrt_le_sqrt (Nat.cast_le.mpr (liveCount_antitone x.property))
      have hc := mul_le_mul_of_nonneg_left hl hK
      have hcost := ha.cost
      have he : FiniteHalfPhase.liveCount x.val.val = liveCount x.val.val := by
        simp only [FiniteHalfPhase.liveCount, liveCount, RectangularRidgeLiveOwner.count_eq,
          Fintype.card_fin]
      rw [he] at hcost
      exact ⟨progress_advance hτ hs ha hx, hcost.trans (add_le_add_left hc _)⟩
  exact hall z y ho

theorem rawStep_failure (F : EpochFactory f ε τ K p) (hp : 0 ≤ p)
    (start : Point (N := N) ε) (x : PhasePoint start) :
    (rawStep F start x).expectation failure ≤ p := by
  classical
  unfold rawStep
  split_ifs with ht
  · simpa using hp
  · convert F.failure_le x.val (Nat.le_of_not_gt (fun h => ht (Or.inr h))) using 1
    unfold Sampler.expectation
    apply Finset.sum_congr rfl
    intro z _
    dsimp
    split <;> simp_all [MSManuscriptAdaptive.failure]

def config (F : EpochFactory f ε τ K p) (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (start : Point (N := N) ε) (hs : 0 < liveCount start.val) :
    MSManuscriptBoundedProcess.Config (PhasePoint start) where
  initial := ⟨start, Finset.Subset.refl _⟩
  terminal x := terminal start.val x.val.val
  progress x := progress τ start.val x.val.val
  bound := 32 / τ + 128
  progress_nonneg x := progress_nonneg hτ x.property
  progress_le x := progress_le hτ start.val hs x.val.property.1
  potential x := f x.val.val
  cost := K * Real.sqrt (liveCount start.val : ℝ)
  cost_nonneg := mul_nonneg hK (Real.sqrt_nonneg _)
  failureBound := p
  failure_nonneg := hp
  step := rawStep F start
  step_sound := rawStep_sound F hτ hK start hs
  step_failure x _ := rawStep_failure F hp start x

def output (F : EpochFactory f ε τ K p) (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (start : Point (N := N) ε) (hs : 0 < liveCount start.val) (calls : ℕ) :=
  MSManuscriptBoundedProcess.output (config F hτ hK hp start hs) calls

theorem output_sound (F : EpochFactory f ε τ K p) (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (start : Point (N := N) ε) (hs : 0 < liveCount start.val) (calls : ℕ)
    (hcalls : 32 / τ + 128 < (calls : ℝ))
    (z : (output F hτ hK hp start hs calls).Draws) (y : PhasePoint start)
    (ho : (output F hτ hK hp start hs calls).value z = some y) :
    terminal start.val y.val.val ∧ f y.val.val ≤ f start.val +
      (calls : ℝ) * K * Real.sqrt (liveCount start.val : ℝ) := by
  have ht := MSManuscriptBoundedProcess.output_sound (config F hτ hK hp start hs)
    calls hcalls z y ho
  change terminal start.val y.val.val ∧ f y.val.val ≤ f start.val +
    (calls : ℝ) * (K * Real.sqrt (liveCount start.val : ℝ)) at ht
  simpa only [mul_assoc] using ht

theorem output_probability (F : EpochFactory f ε τ K p) (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (start : Point (N := N) ε) (hs : 0 < liveCount start.val) (calls : ℕ) :
    1 - (calls : ℝ) * p ≤ ∑ z, (output F hτ hK hp start hs calls).weight z *
      (if ((output F hτ hK hp start hs calls).value z).isSome then 1 else 0) :=
  MSManuscriptBoundedProcess.output_event_probability (config F hτ hK hp start hs) calls

section MixedRounding
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance ridgePhaseAssemblyCStar : CStarAlgebra (Matrix n n ℂ) := {}

theorem complete_potential_le (m : ℕ) (θ κ : ℝ) (offset : selfAdjoint (Matrix n n ℂ))
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hAn : ∀ i, ‖A i‖ ≤ 1)
    {x : EuclideanSpace ℝ (Fin N)} (hx : FiniteHalfPhase.Cube x) :
    potential m θ κ offset A hA (SmallLiveRounding.complete x) ≤
      potential m θ κ offset A hA x + liveCount x := by
  have hf : frozenCoordinates x ⊆ frozenCoordinates (SmallLiveRounding.complete x) := by
    rw [SmallLiveRounding.complete_frozen_eq_univ]
    exact Finset.subset_univ _
  have hd := deletion_le m θ κ offset A hA hf
  have hl := RectangularRidgeOwnerBounds.sub_le_norm m
    (epochCenter offset A hA x).property (epochCenter offset A hA (SmallLiveRounding.complete x)).property
    A hA (projection_posSemidef (frozenCoordinates x)) θ κ
  have hn := SmallLiveRounding.complete_center_norm_le offset A hA hAn hx
  rw [← liveCount_eq] at hn
  change _ - potential m θ κ offset A hA x ≤ _ at hl
  linarith

def finish (x : Point (N := N) ε) : Point (N := N) ε := by
  classical
  exact if liveCount x.val < 32 then
    ⟨SmallLiveRounding.complete x.val, SmallLiveRounding.complete_regular x.val ε⟩ else x

theorem finish_sound (m : ℕ) (θ κ : ℝ) (offset : selfAdjoint (Matrix n n ℂ))
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hAn : ∀ i, ‖A i‖ ≤ 1)
    (start x : Point (N := N) ε) (hF : frozenCoordinates start.val ⊆ frozenCoordinates x.val)
    (ht : terminal start.val x.val) :
    2 * liveCount (finish x).val ≤ liveCount start.val ∧
      potential m θ κ offset A hA (finish x).val ≤ potential m θ κ offset A hA x.val +
        64 * Real.sqrt (liveCount start.val : ℝ) := by
  classical
  unfold finish
  split_ifs with hl
  · have hz : liveCount (SmallLiveRounding.complete x.val) = 0 := by
      rw [liveCount_eq, SmallLiveRounding.complete_live_card]
    refine ⟨by simp [hz], ?_⟩
    have hc := complete_potential_le m θ κ offset A hA hAn x.property.1
    have hs := (SmallLiveRounding.small_nat_le_sqrt hl).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.cast_le.mpr (liveCount_antitone hF)))
        (by norm_num : (0 : ℝ) ≤ 64))
    exact hc.trans (add_le_add_left hs _)
  · exact ⟨ht.resolve_right hl, le_add_of_nonneg_right (by positivity)⟩

end MixedRounding
end MatrixSpencer.RectangularRidgePhaseAssembly
