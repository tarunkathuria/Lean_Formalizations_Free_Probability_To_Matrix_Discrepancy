import HigherRankKSRuntime.CleanMovement

/-! The explicit controller preserves every already fixed original sign. -/
noncomputable section
namespace HigherRankKSRuntime.ControllerLoop
open AugmentedHigherRankKS
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def PreservesFrozen (z z' : EpochState ι) : Prop :=
  ∀ i, |position z i| = 1 → position z' i = position z i

theorem run_preservesFrozen {a R step h : ℝ} (ha : 0 < a)
    (next : EpochState ι → Counted (Event ι))
    (sound : ∀ z ∈ epochDomain a R, (next z).value.Valid a R step h z)
    (hfrozen : ∀ z ∈ epochDomain a R, PreservesFrozen z ((next z).value.apply a step h z))
    (fuel : ℕ) {z : EpochState ι} (hz : z ∈ epochDomain a R) :
    PreservesFrozen z (run a step h next fuel z).state := by
  induction fuel generalizing z with
  | zero => intro i hi; rfl
  | succ fuel ih =>
    have hf := Event.valid_feasible ha hz (sound z hz)
    have hp := hfrozen z hz
    generalize he : (next z).value = ev at hf hp
    cases ev with
    | done => intro i hi; simp only [run,he]
    | prepare j =>
      have hr := ih hf
      intro i hi
      have heq := hp i hi
      have hr' := hr i (by rw [heq]; exact hi)
      simpa only [run,he,Result.after] using hr'.trans heq
    | move g =>
      have hr := ih hf
      intro i hi
      have heq := hp i hi
      have hr' := hr i (by rw [heq]; exact hi)
      simpa only [run,he,Result.after] using hr'.trans heq
    | round j =>
      have hr := ih hf
      intro i hi
      have heq := hp i hi
      have hr' := hr i (by rw [heq]; exact hi)
      simpa only [run,he,Result.after] using hr'.trans heq
    | exhaust j =>
      have hr := ih hf
      intro i hi
      have heq := hp i hi
      have hr' := hr i (by rw [heq]; exact hi)
      simpa only [run,he,Result.after] using hr'.trans heq
end HigherRankKSRuntime.ControllerLoop

namespace HigherRankKSRuntime.NextEvent
open AugmentedHigherRankKS ControllerLoop ActiveEnumeration Tangent
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {N : ℕ}

theorem faceSign_of_face {x : ℝ} (hx : |x| = 1) : faceSign x = x := by
  rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hx with h | h
  · rw [h]; norm_num [faceSign]
  · rw [h]; norm_num [faceSign]

theorem round_preservesFrozen (z : EpochState (Fin N)) (j : Fin N) :
    PreservesFrozen z (roundOwner z j) := by
  intro i hi
  by_cases hij : i=j
  · subst i; rw [roundOwner_position]; exact faceSign_of_face hi
  · simp only [roundOwner,position,Function.update_of_ne hij]

theorem afterRejection_preservesFrozen (query : EpochState (Fin N) → Counted ℝ)
    (a step t h : ℝ) {ρ ζ : ℝ} (hρ : 0 ≤ ρ) (z : EpochState (Fin N))
    (hc : Clean z ρ ζ) :
    PreservesFrozen z ((afterRejection query a t h z).value.apply a step h z) := by
  intro i hi
  have hi0 : ¬ 0 < reserve z i := by
    intro hp
    have hh := (hc i hp).1
    rw [hi] at hh
    linarith
  by_cases hr : 0 < (Frame.canonical (count z) (restrictedPosition z)).rank
  · rw [afterRejection_value query a t h z hr]
    exact (movement_inactive z _ a h i hi0).1
  · simp only [afterRejection,dif_neg hr,Event.apply]

theorem compute_preservesFrozen (query : EpochState (Fin N) → Counted ℝ)
    (a step h t p0 ρ ζ : ℝ) (hρ : 0 ≤ ρ) (z : EpochState (Fin N)) :
    PreservesFrozen z ((compute query a step h t p0 ρ ζ z).value.apply a step h z) := by
  generalize he : (CleanupScan.scan z ρ ζ (List.finRange N)).value = cleanup
  cases cleanup with
  | some e =>
    cases e with
    | round i =>
      simp only [compute,he,CleanupScan.Cleanup.event,Event.apply]
      exact round_preservesFrozen z i
    | exhaust i =>
      intro j hj
      simp only [compute,he,CleanupScan.Cleanup.event,Event.apply]
      rfl
  | none =>
    by_cases hc : count z = 0
    · intro j hj; simp only [compute,he,hc,↓reduceIte,Event.apply]
    · generalize hp : (PreparationScan.scan (fun i => query (prepareOwner a z i step))
          (query z).value (-(step*p0/(4*a))) (labels z)).value = prep
      cases prep with
      | some i =>
        intro j hj
        simp only [compute,he,hc,↓reduceIte,hp,Event.apply]
        rfl
      | none =>
        simp only [compute,he,hc,↓reduceIte,hp]
        exact afterRejection_preservesFrozen query a step t h hρ z (clean_of_scan_none he)
end HigherRankKSRuntime.NextEvent
