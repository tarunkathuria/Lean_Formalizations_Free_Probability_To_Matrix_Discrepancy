import MatrixSpencer.RectangularRidgePhaseAssembly
import MatrixSpencer.MSManuscriptFullProcess

/-!
# Finite full-signing composition for the mixed potential

The input is an explicitly supplied epoch sampler and its local theorem.
The definitions run its finite branches through bounded half phases and
then bounded full coloring, preserving the original labels and full center.
This compositional theorem is not a claim that the input interface has yet
been instantiated by a concrete implementation.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeFullAssembly
open RectangularRidgeRemainingPotential RectangularRidgePhaseAssembly MSManuscriptAdaptive
attribute [local irreducible] MSManuscriptBoundedProcess.run MSManuscriptAdaptive.run
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance ridgeFullAssemblyCStar : CStarAlgebra (Matrix n n ℂ) := {}
variable (m : ℕ) (θ κ : ℝ) (offset : selfAdjoint (Matrix n n ℂ))
  (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
  (hAn : ∀ i, ‖A i‖ ≤ 1) {ε τ K p : ℝ}

abbrev Input := EpochFactory (potential m θ κ offset A hA) ε τ K p

def phaseOutput (F : Input m θ κ offset A hA (ε := ε) (τ := τ) (K := K) (p := p)) (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (start : Point (N := N) ε) (hs : 0 < liveCount start.val) (calls : ℕ) :
    Sampler (Option (Point (N := N) ε)) :=
  (RectangularRidgePhaseAssembly.output F hτ hK hp start hs calls).map
    (Option.map (fun y => finish y.val))

include hAn in
theorem phaseOutput_sound (F : Input m θ κ offset A hA (ε := ε) (τ := τ) (K := K) (p := p)) (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (start : Point (N := N) ε) (hs : 0 < liveCount start.val) (calls : ℕ)
    (hcalls : 32 / τ + 128 < (calls : ℝ))
    (z : (phaseOutput m θ κ offset A hA F hτ hK hp start hs calls).Draws)
    (y : Point (N := N) ε)
    (ho : (phaseOutput m θ κ offset A hA F hτ hK hp start hs calls).value z = some y) :
    2 * liveCount y.val ≤ liveCount start.val ∧
      potential m θ κ offset A hA y.val ≤ potential m θ κ offset A hA start.val +
        ((calls : ℝ) * K + 64) * Real.sqrt (liveCount start.val : ℝ) := by
  change ((RectangularRidgePhaseAssembly.output F hτ hK hp start hs calls).value z).map
    (fun w => finish w.val) = some y at ho
  obtain ⟨w, hw, hwy⟩ := Option.map_eq_some_iff.mp ho
  subst y
  have ht := RectangularRidgePhaseAssembly.output_sound F hτ hK hp start hs calls hcalls z w hw
  have hf := finish_sound m θ κ offset A hA hAn start w.val w.property ht.1
  exact ⟨hf.1, by linarith [ht.2, hf.2]⟩

omit [Nonempty n] in
theorem phaseOutput_failure (F : Input m θ κ offset A hA (ε := ε) (τ := τ) (K := K) (p := p)) (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (start : Point (N := N) ε) (hs : 0 < liveCount start.val) (calls : ℕ) :
    (phaseOutput m θ κ offset A hA F hτ hK hp start hs calls).expectation
      MSManuscriptAdaptive.failure ≤ (calls : ℝ) * p := by
  have ht := RectangularRidgePhaseAssembly.output_probability F hτ hK hp start hs calls
  have h1 := success_add_failure (RectangularRidgePhaseAssembly.output F hτ hK hp start hs calls)
  have he := Sampler.failure_map (RectangularRidgePhaseAssembly.output F hτ hK hp start hs calls)
    (fun y => finish y.val)
  change 1 - (calls : ℝ) * p ≤
    (RectangularRidgePhaseAssembly.output F hτ hK hp start hs calls).expectation success at ht
  change (phaseOutput m θ κ offset A hA F hτ hK hp start hs calls).expectation
    MSManuscriptAdaptive.failure = _ at he
  linarith

def fullFactory (F : Input m θ κ offset A hA (ε := ε) (τ := τ) (K := K) (p := p)) (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (calls : ℕ) (hcalls : 32 / τ + 128 < (calls : ℝ)) :
    MSManuscriptFullProcess.Factory (fun x : Point (N := N) ε => liveCount x.val)
      (fun x => potential m θ κ offset A hA x.val) ((calls : ℝ) * K + 64) ((calls : ℝ) * p) where
  sample := fun start hs => phaseOutput m θ κ offset A hA F hτ hK hp start hs calls
  sound := fun start hs z y ho => phaseOutput_sound m θ κ offset A hA hAn F hτ hK hp
    start hs calls hcalls z y ho
  failure_le := fun start hs => phaseOutput_failure m θ κ offset A hA F hτ hK hp start hs calls

def output (F : Input m θ κ offset A hA (ε := ε) (τ := τ) (K := K) (p := p)) (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (calls : ℕ) (hcalls : 32 / τ + 128 < (calls : ℝ)) (start : Point (N := N) ε) :=
  MSManuscriptFullProcess.output (fullFactory m θ κ offset A hA hAn F hτ hK hp calls hcalls)
    (by positivity) (by positivity) N (fun x => liveCount_le x.val) start

theorem output_sound (F : Input m θ κ offset A hA (ε := ε) (τ := τ) (K := K) (p := p)) (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (calls : ℕ) (hcalls : 32 / τ + 128 < (calls : ℝ)) (start : Point (N := N) ε)
    (z : (output m θ κ offset A hA hAn F hτ hK hp calls hcalls start).Draws)
    (y : Point (N := N) ε)
    (ho : (output m θ κ offset A hA hAn F hτ hK hp calls hcalls start).value z = some y) :
    liveCount y.val = 0 ∧ potential m θ κ offset A hA y.val ≤
      potential m θ κ offset A hA start.val +
        4 * ((calls : ℝ) * K + 64) * Real.sqrt (liveCount start.val : ℝ) :=
  MSManuscriptFullProcess.output_sound (fullFactory m θ κ offset A hA hAn F hτ hK hp calls hcalls)
    (by positivity) (by positivity) N (fun x => liveCount_le x.val) start z y ho

theorem output_probability (F : Input m θ κ offset A hA (ε := ε) (τ := τ) (K := K) (p := p)) (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (calls : ℕ) (hcalls : 32 / τ + 128 < (calls : ℝ)) (start : Point (N := N) ε) :
    1 - ((N + 1 : ℕ) : ℝ) * ((calls : ℝ) * p) ≤
      ∑ z, (output m θ κ offset A hA hAn F hτ hK hp calls hcalls start).weight z *
        (if ((output m θ κ offset A hA hAn F hτ hK hp calls hcalls start).value z).isSome
          then 1 else 0) :=
  MSManuscriptFullProcess.output_event_probability
    (fullFactory m θ κ offset A hA hAn F hτ hK hp calls hcalls)
      (by positivity) (by positivity) N (fun x => liveCount_le x.val) start

end MatrixSpencer.RectangularRidgeFullAssembly
