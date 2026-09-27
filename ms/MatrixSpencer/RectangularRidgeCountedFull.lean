import MatrixSpencer.RectangularRidgeCountedPhase
import MatrixSpencer.RectangularRidgeFullAssembly
import MatrixSpencer.MSCountedFullProcess

/-! Counted execution of the exact fixed-universe half/full sampler.
The concrete numerical accepted epoch supplies `E`; all outer scans,
terminal tests, proof attachment and final nearest-sign rounding are counted
here. Only the selected history is executed. -/
open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeCountedFull
open MSManuscriptAdaptive MSCountedSampler RectangularRidgePhaseAssembly
open RectangularRidgeRemainingPotential RectangularRidgeFullAssembly
open RealRAM.JacobiIteration (Counted)
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable (m : ℕ) (θ κ : ℝ) (offset : selfAdjoint (Matrix n n ℂ))
  (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hAn : ∀ i, ‖A i‖ ≤ 1)
  {ε τ K p : ℝ}

def finish (x : Point (N := N) ε) : Counted (Point (N := N) ε) :=
  RealRAM.MSPoint.finish (RealRAM.MSPoint.finTable N) ε x

theorem finish_value (x : Point (N := N) ε) :
    (finish x).value = RectangularRidgePhaseAssembly.finish x := by
  rw [finish, RealRAM.MSPoint.finish_value]
  simp only [MSManuscriptNumericalHalfPhase.finish, RectangularRidgePhaseAssembly.finish, liveCount_eq]

theorem finish_cost (x : Point (N := N) ε) : (finish x).cost ≤ 17 * N + 8 := by
  simpa only [finish, Fintype.card_fin] using RealRAM.MSPoint.finish_cost (RealRAM.MSPoint.finTable N) ε x

def finishOptional (start : Point (N := N) ε) : Option (PhasePoint start) → Counted (Option (Point (N := N) ε))
  | none => ⟨none, 1⟩
  | some x => let y := finish x.val; ⟨some y.value, y.cost + 1⟩

theorem finishOptional_value (start : Point (N := N) ε) (x : Option (PhasePoint start)) :
    (finishOptional start x).value = x.map (fun y => RectangularRidgePhaseAssembly.finish y.val) := by
  cases x <;> simp only [finishOptional, finish_value, Option.map_none, Option.map_some]

theorem finishOptional_cost (start : Point (N := N) ε) (x : Option (PhasePoint start)) :
    (finishOptional start x).cost ≤ 17 * N + 9 := by
  cases x with
  | none => simp only [finishOptional]; omega
  | some x => exact Nat.add_le_add_right (finish_cost x.val) 1

def phase (F : Input m θ κ offset A hA (ε := ε) (τ := τ) (K := K) (p := p))
    (E : ∀ x hx, Implementation (F.sample x hx))
    (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p) (start : Point (N := N) ε)
    (hs : 0 < liveCount start.val) (calls : ℕ) :
    Implementation (phaseOutput m θ κ offset A hA F hτ hK hp start hs calls) :=
  congr (by
    have he : (fun x => (finishOptional start x).value) =
        Option.map (fun y => RectangularRidgePhaseAssembly.finish y.val) := by
      funext x
      exact finishOptional_value start x
    rw [he]
    rfl)
    (map (RectangularRidgeCountedPhase.output F E hτ hK hp start hs calls) (finishOptional start))

omit [Nonempty n] in
theorem phase_bounded (F : Input m θ κ offset A hA (ε := ε) (τ := τ) (K := K) (p := p))
    (E : ∀ x hx, Implementation (F.sample x hx))
    (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p) (start : Point (N := N) ε)
    (hs : 0 < liveCount start.val) (calls : ℕ) {B R : ℕ}
    (hE : ∀ x hx, Bounded (E x hx) B R) :
    Bounded (phase m θ κ offset A hA F E hτ hK hp start hs calls)
      (calls * (B + 44 * N + 39) + 17 * N + 15) (calls * R) := by
  unfold phase
  apply congr_bounded
  have hh := map_bounded _ (finishOptional start)
    (RectangularRidgeCountedPhase.output_bounded F E hτ hK hp start hs calls hE)
    (finishOptional_cost start)
  convert hh using 1
  ring

def emptyTest (x : Point (N := N) ε) : Counted Bool :=
  RealRAM.MSPoint.emptyTest (RealRAM.MSPoint.finTable N) x.val

theorem emptyTest_value (x : Point (N := N) ε) :
    (emptyTest x).value = decide (liveCount x.val = 0) := by
  simp only [emptyTest, RealRAM.MSPoint.emptyTest_value, liveCount_eq]

theorem emptyTest_cost (x : Point (N := N) ε) : (emptyTest x).cost = 11 * N + 6 := by
  simp only [emptyTest, RealRAM.MSPoint.emptyTest_cost, Fintype.card_fin]

def output (F : Input m θ κ offset A hA (ε := ε) (τ := τ) (K := K) (p := p))
    (E : ∀ x hx, Implementation (F.sample x hx))
    (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p) (calls : ℕ)
    (hcalls : 32 / τ + 128 < (calls : ℝ)) (start : Point (N := N) ε) :
    Implementation (RectangularRidgeFullAssembly.output m θ κ offset A hA hAn F hτ hK hp calls hcalls start) :=
  MSCountedFullProcess.output (fullFactory m θ κ offset A hA hAn F hτ hK hp calls hcalls)
    emptyTest emptyTest_value (fun x hx => phase m θ κ offset A hA F E hτ hK hp x hx calls)
    (by positivity) (by positivity) N (fun x => liveCount_le x.val) start

def operations (N calls B : ℕ) : ℕ :=
  (N + 1) * (calls * (B + 44 * N + 39) + 39 * N + 36) + 4

theorem output_bounded (F : Input m θ κ offset A hA (ε := ε) (τ := τ) (K := K) (p := p))
    (E : ∀ x hx, Implementation (F.sample x hx))
    (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p) (calls : ℕ)
    (hcalls : 32 / τ + 128 < (calls : ℝ)) (start : Point (N := N) ε)
    {B R : ℕ} (hE : ∀ x hx, Bounded (E x hx) B R) :
    Bounded (output m θ κ offset A hA hAn F E hτ hK hp calls hcalls start)
      (operations N calls B) ((N + 1) * (calls * R)) := by
  have hh := MSCountedFullProcess.output_bounded
    (fullFactory m θ κ offset A hA hAn F hτ hK hp calls hcalls)
    emptyTest emptyTest_value (fun x hx => phase m θ κ offset A hA F E hτ hK hp x hx calls)
    (by positivity) (by positivity) N (fun x => liveCount_le x.val) start
    (fun x => (emptyTest_cost x).le) (fun x hx => phase_bounded m θ κ offset A hA F E hτ hK hp x hx calls hE)
  unfold operations
  convert hh using 1
  ring

end MatrixSpencer.RectangularRidgeCountedFull
