import HigherRankKSRuntime.FrozenCoordinates

/-! A reserve-zero owner is completely untouched by the local controller.
In particular, globally frozen owners retain zero spent mass across an epoch. -/
noncomputable section
namespace HigherRankKSRuntime.ControllerLoop
open AugmentedHigherRankKS
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def PreservesInactive (z z' : EpochState ι) : Prop :=
  ∀ i, reserve z i = 0 → position z' i = position z i ∧
    spent z' i = spent z i ∧ reserve z' i = 0

theorem run_preservesInactive {a R step h : ℝ} (ha : 0 < a)
    (next : EpochState ι → Counted (Event ι))
    (sound : ∀ z ∈ epochDomain a R, (next z).value.Valid a R step h z)
    (hinactive : ∀ z ∈ epochDomain a R, PreservesInactive z ((next z).value.apply a step h z))
    (fuel : ℕ) {z : EpochState ι} (hz : z ∈ epochDomain a R) :
    PreservesInactive z (run a step h next fuel z).state := by
  induction fuel generalizing z with
  | zero => intro i hi; exact ⟨rfl,rfl,hi⟩
  | succ fuel ih =>
    have hf := Event.valid_feasible ha hz (sound z hz)
    have hp := hinactive z hz
    generalize he : (next z).value = ev at hf hp
    cases ev with
    | done => intro i hi; simp only [run,he]; exact ⟨trivial,trivial,hi⟩
    | prepare j =>
      have hr := ih hf
      intro i hi
      obtain ⟨hp,hsp,hc⟩ := hp i hi
      obtain ⟨hp',hsp',hc'⟩ := hr i hc
      exact ⟨by simpa only [run,he,Result.after] using hp'.trans hp,
        by simpa only [run,he,Result.after] using hsp'.trans hsp,
        by simpa only [run,he,Result.after] using hc'⟩
    | move g =>
      have hr := ih hf
      intro i hi
      obtain ⟨hp,hsp,hc⟩ := hp i hi
      obtain ⟨hp',hsp',hc'⟩ := hr i hc
      exact ⟨by simpa only [run,he,Result.after] using hp'.trans hp,
        by simpa only [run,he,Result.after] using hsp'.trans hsp,
        by simpa only [run,he,Result.after] using hc'⟩
    | round j =>
      have hr := ih hf
      intro i hi
      obtain ⟨hp,hsp,hc⟩ := hp i hi
      obtain ⟨hp',hsp',hc'⟩ := hr i hc
      exact ⟨by simpa only [run,he,Result.after] using hp'.trans hp,
        by simpa only [run,he,Result.after] using hsp'.trans hsp,
        by simpa only [run,he,Result.after] using hc'⟩
    | exhaust j =>
      have hr := ih hf
      intro i hi
      obtain ⟨hp,hsp,hc⟩ := hp i hi
      obtain ⟨hp',hsp',hc'⟩ := hr i hc
      exact ⟨by simpa only [run,he,Result.after] using hp'.trans hp,
        by simpa only [run,he,Result.after] using hsp'.trans hsp,
        by simpa only [run,he,Result.after] using hc'⟩
end HigherRankKSRuntime.ControllerLoop

namespace HigherRankKSRuntime.NextEvent
open AugmentedHigherRankKS ControllerLoop ActiveEnumeration Tangent
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {N : ℕ}

theorem afterRejection_preservesInactive (query : EpochState (Fin N) → Counted ℝ)
    (a step t h : ℝ) (z : EpochState (Fin N)) :
    PreservesInactive z ((afterRejection query a t h z).value.apply a step h z) := by
  intro i hi
  by_cases hr : 0 < (Frame.canonical (count z) (restrictedPosition z)).rank
  · rw [afterRejection_value query a t h z hr]
    have he := movement_inactive z
      (WalkExecution.compute (chartReport query a z) (restrictedPosition z) t h hr).value
      a h i (by rw [hi]; exact lt_irrefl 0)
    exact ⟨he.1,he.2.1,he.2.2.trans hi⟩
  · simp only [afterRejection,dif_neg hr,Event.apply]
    exact ⟨trivial,trivial,hi⟩

theorem compute_preservesInactive (query : EpochState (Fin N) → Counted ℝ)
    (a step h t p0 ρ ζ : ℝ) (z : EpochState (Fin N)) :
    PreservesInactive z ((compute query a step h t p0 ρ ζ z).value.apply a step h z) := by
  generalize he : (CleanupScan.scan z ρ ζ (List.finRange N)).value = cleanup
  cases cleanup with
  | some e =>
    have hen := (CleanupScan.scan_some z ρ ζ (List.finRange N) he).2
    cases e with
    | round i =>
      intro j hj
      have hji : j≠i := by intro hh; subst j; have := hen.1; rw [hj] at this; linarith
      simp only [compute,he,CleanupScan.Cleanup.event,Event.apply,roundOwner,
        position,spent,reserve,Function.update_of_ne hji]
      exact ⟨trivial,trivial,hj⟩
    | exhaust i =>
      intro j hj
      have hji : j≠i := by intro hh; subst j; have := hen.1; rw [hj] at this; linarith
      simp only [compute,he,CleanupScan.Cleanup.event,Event.apply,exhaustOwner,
        prepareOwner,preparation,position,spent,reserve,Pi.single_eq_of_ne hji,
        zero_div,add_zero,sub_zero]
      exact ⟨trivial,trivial,hj⟩
  | none =>
    by_cases hc : count z = 0
    · intro j hj
      simp only [compute,he,hc,↓reduceIte,Event.apply]
      exact ⟨trivial,trivial,hj⟩
    · generalize hp : (PreparationScan.scan (fun i => query (prepareOwner a z i step))
          (query z).value (-(step*p0/(4*a))) (labels z)).value = prep
      cases prep with
      | some i =>
        have hi := (mem_labels z i).mp (PreparationScan.scan_some _ _ _ _ hp).1
        intro j hj
        have hji : j≠i := by intro hh; subst j; rw [hj] at hi; linarith
        simp only [compute,he,hc,↓reduceIte,hp,Event.apply]
        simpa [prepareOwner,preparation,position,spent,reserve,hji] using hj
      | none =>
        simp only [compute,he,hc,↓reduceIte,hp]
        exact afterRejection_preservesInactive query a step t h z
end HigherRankKSRuntime.NextEvent
