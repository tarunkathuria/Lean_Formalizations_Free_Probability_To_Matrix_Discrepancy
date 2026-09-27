import HigherRankKSRuntime.InvariantControllerLoop
import HigherRankKSRuntime.InactiveCoordinates

/-! Original-owner invariants on the executed controller, including the
permanent removal of globally negligible input atoms. -/
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKSRuntime.ControllerLoop
open AugmentedHigherRankKS
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem run_preservesFrozen_on {a R step h : ℝ} (ha : 0 < a)
    (P : EpochState ι → Prop)
    (next : EpochState ι → Counted (Event ι))
    (sound : ∀ z ∈ epochDomain a R, P z → (next z).value.Valid a R step h z)
    (closed : ∀ z ∈ epochDomain a R, P z → P ((next z).value.apply a step h z))
    (hfrozen : ∀ z ∈ epochDomain a R, PreservesFrozen z ((next z).value.apply a step h z))
    (fuel : ℕ) {z : EpochState ι} (hz : z ∈ epochDomain a R) (hP : P z) :
    PreservesFrozen z (run a step h next fuel z).state := by
  induction fuel generalizing z with
  | zero => intro i hi; rfl
  | succ fuel ih =>
    have hf := Event.valid_feasible ha hz (sound z hz hP)
    have hnext := closed z hz hP
    have hp := hfrozen z hz
    generalize he : (next z).value = ev at hf hp hnext
    cases ev with
    | done => intro i hi; simp only [run,he]
    | prepare j =>
      have hr := ih hf hnext
      intro i hi
      have heq := hp i hi
      have hr' := hr i (by rw [heq]; exact hi)
      simpa only [run,he,Result.after] using hr'.trans heq
    | move g =>
      have hr := ih hf hnext
      intro i hi
      have heq := hp i hi
      have hr' := hr i (by rw [heq]; exact hi)
      simpa only [run,he,Result.after] using hr'.trans heq
    | round j =>
      have hr := ih hf hnext
      intro i hi
      have heq := hp i hi
      have hr' := hr i (by rw [heq]; exact hi)
      simpa only [run,he,Result.after] using hr'.trans heq
    | exhaust j =>
      have hr := ih hf hnext
      intro i hi
      have heq := hp i hi
      have hr' := hr i (by rw [heq]; exact hi)
      simpa only [run,he,Result.after] using hr'.trans heq

theorem run_preservesInactive_on {a R step h : ℝ} (ha : 0 < a)
    (P : EpochState ι → Prop)
    (next : EpochState ι → Counted (Event ι))
    (sound : ∀ z ∈ epochDomain a R, P z → (next z).value.Valid a R step h z)
    (closed : ∀ z ∈ epochDomain a R, P z → P ((next z).value.apply a step h z))
    (hinactive : ∀ z ∈ epochDomain a R, PreservesInactive z ((next z).value.apply a step h z))
    (fuel : ℕ) {z : EpochState ι} (hz : z ∈ epochDomain a R) (hP : P z) :
    PreservesInactive z (run a step h next fuel z).state := by
  induction fuel generalizing z with
  | zero => intro i hi; exact ⟨rfl,rfl,hi⟩
  | succ fuel ih =>
    have hf := Event.valid_feasible ha hz (sound z hz hP)
    have hnext := closed z hz hP
    have hp := hinactive z hz
    generalize he : (next z).value = ev at hf hp hnext
    cases ev with
    | done => intro i hi; simp only [run,he]; exact ⟨trivial,trivial,hi⟩
    | prepare j =>
      have hr := ih hf hnext
      intro i hi
      obtain ⟨hp,hsp,hc⟩ := hp i hi
      obtain ⟨hp',hsp',hc'⟩ := hr i hc
      exact ⟨by simpa only [run,he,Result.after] using hp'.trans hp,
        by simpa only [run,he,Result.after] using hsp'.trans hsp,
        by simpa only [run,he,Result.after] using hc'⟩
    | move g =>
      have hr := ih hf hnext
      intro i hi
      obtain ⟨hp,hsp,hc⟩ := hp i hi
      obtain ⟨hp',hsp',hc'⟩ := hr i hc
      exact ⟨by simpa only [run,he,Result.after] using hp'.trans hp,
        by simpa only [run,he,Result.after] using hsp'.trans hsp,
        by simpa only [run,he,Result.after] using hc'⟩
    | round j =>
      have hr := ih hf hnext
      intro i hi
      obtain ⟨hp,hsp,hc⟩ := hp i hi
      obtain ⟨hp',hsp',hc'⟩ := hr i hc
      exact ⟨by simpa only [run,he,Result.after] using hp'.trans hp,
        by simpa only [run,he,Result.after] using hsp'.trans hsp,
        by simpa only [run,he,Result.after] using hc'⟩
    | exhaust j =>
      have hr := ih hf hnext
      intro i hi
      obtain ⟨hp,hsp,hc⟩ := hp i hi
      obtain ⟨hp',hsp',hc'⟩ := hr i hc
      exact ⟨by simpa only [run,he,Result.after] using hp'.trans hp,
        by simpa only [run,he,Result.after] using hsp'.trans hsp,
        by simpa only [run,he,Result.after] using hc'⟩
end HigherRankKSRuntime.ControllerLoop

namespace HigherRankKSRuntime.NextEvent
open AugmentedHigherRankKS ControllerLoop
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

def LargeOwners (A : Fin N → Matrix n n ℂ) (η : ℝ) (z : EpochState (Fin N)) : Prop :=
  ∀ i, 0 < reserve z i → η ≤ ‖A i‖

theorem largeOwners_preserved (A : Fin N → Matrix n n ℂ) (η : ℝ)
    {a R : ℝ} {z z' : EpochState (Fin N)} (hz : z ∈ epochDomain a R)
    (hi : PreservesInactive z z') (hlarge : LargeOwners A η z) : LargeOwners A η z' := by
  intro i hp
  apply hlarge i
  by_contra hn
  have hc : reserve z i = 0 := le_antisymm (le_of_not_gt hn) (hz i).2.2.2.2.1
  have he := (hi i hc).2.2
  rw [he] at hp
  exact lt_irrefl 0 hp

theorem compute_largeOwners (A : Fin N → Matrix n n ℂ) (η : ℝ)
    (query : EpochState (Fin N) → Counted ℝ) (a R step h t p0 ρ ζ : ℝ)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain a R) (hl : LargeOwners A η z) :
    LargeOwners A η ((compute query a step h t p0 ρ ζ z).value.apply a step h z) :=
  largeOwners_preserved A η hz (compute_preservesInactive query a step h t p0 ρ ζ z) hl
end HigherRankKSRuntime.NextEvent
