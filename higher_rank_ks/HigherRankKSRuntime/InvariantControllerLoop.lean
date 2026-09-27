import HigherRankKSRuntime.ControllerLoop

/-! The concrete finite loop with a proved state invariant. This permits
permanently discarded original owners to remain in the storage layout with
zero reserve. The invariant is propagated by actual updates. -/
noncomputable section
namespace HigherRankKSRuntime.ControllerLoop
open AugmentedHigherRankKS
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem run_spec_on {a R step h : ℝ} (ha : 0 < a)
    (P : EpochState ι → Prop)
    (next : EpochState ι → Counted (Event ι))
    (sound : ∀ z ∈ epochDomain a R, P z → (next z).value.Valid a R step h z)
    (closed : ∀ z ∈ epochDomain a R, P z → P ((next z).value.apply a step h z))
    (fuel : ℕ) {z : EpochState ι} (hz : z ∈ epochDomain a R) (hP : P z) :
    let r := run a step h next fuel z
    P r.state ∧ r.state ∈ epochDomain a R ∧
      CountedTrace a R step h z r.state r.walks r.preps r.cleanups ∧
      (Terminal r.state ∨ r.walks + r.preps + r.cleanups = fuel) := by
  induction fuel generalizing z with
  | zero => exact ⟨hP, hz, .nil, Or.inr rfl⟩
  | succ fuel ih =>
    have hs := sound z hz hP
    have hf := Event.valid_feasible ha hz hs
    have ht := Event.trace hz hs
    have hnext := closed z hz hP
    generalize he : (next z).value = ev at hs hf ht hnext
    cases ev with
    | done =>
      simp only [run, he]
      exact ⟨hP, hz, .nil, Or.inl hs⟩
    | prepare i =>
      simp only [run, he, Result.after]
      obtain ⟨hrP, hrf, hrt, hrn⟩ := ih hf hnext
      refine ⟨hrP, hrf, trace_append ht hrt, ?_⟩
      rcases hrn with hn | hn
      · exact Or.inl hn
      · right
        simpa only [run, he, Result.after, Event.walks, Event.preps, Event.cleanups] using
          (show 0 + (run a step h next fuel (Event.apply a step h z (.prepare i))).walks +
            (1 + (run a step h next fuel (Event.apply a step h z (.prepare i))).preps) +
            (0 + (run a step h next fuel (Event.apply a step h z (.prepare i))).cleanups) =
              fuel + 1 by omega)
    | move g =>
      simp only [run, he, Result.after]
      obtain ⟨hrP, hrf, hrt, hrn⟩ := ih hf hnext
      refine ⟨hrP, hrf, trace_append ht hrt, ?_⟩
      rcases hrn with hn | hn
      · exact Or.inl hn
      · right
        simp only [run, he, Result.after, Event.walks, Event.preps, Event.cleanups]
        change (1 + (run a step h next fuel _).walks) +
          (0 + (run a step h next fuel _).preps) +
          (0 + (run a step h next fuel _).cleanups) = _
        omega
    | round i =>
      simp only [run, he, Result.after]
      obtain ⟨hrP, hrf, hrt, hrn⟩ := ih hf hnext
      refine ⟨hrP, hrf, trace_append ht hrt, ?_⟩
      rcases hrn with hn | hn
      · exact Or.inl hn
      · right
        simp only [run, he, Result.after, Event.walks, Event.preps, Event.cleanups]
        change (0 + (run a step h next fuel _).walks) +
          (0 + (run a step h next fuel _).preps) +
          (1 + (run a step h next fuel _).cleanups) = _
        omega
    | exhaust i =>
      simp only [run, he, Result.after]
      obtain ⟨hrP, hrf, hrt, hrn⟩ := ih hf hnext
      refine ⟨hrP, hrf, trace_append ht hrt, ?_⟩
      rcases hrn with hn | hn
      · exact Or.inl hn
      · right
        simp only [run, he, Result.after, Event.walks, Event.preps, Event.cleanups]
        change (0 + (run a step h next fuel _).walks) +
          (0 + (run a step h next fuel _).preps) +
          (1 + (run a step h next fuel _).cleanups) = _
        omega

theorem run_terminal_on {a R step h : ℝ} (ha : 0 < a) (hstep : 0 < step) (hh : h ≠ 0)
    (P : EpochState ι → Prop)
    (next : EpochState ι → Counted (Event ι))
    (sound : ∀ z ∈ epochDomain a R, P z → (next z).value.Valid a R step h z)
    (closed : ∀ z ∈ epochDomain a R, P z → P ((next z).value.apply a step h z))
    (fuel : ℕ) (hfuel : (Fintype.card ι : ℝ) / h ^ 2 +
      (Fintype.card ι : ℝ) * (a * R) / step + Fintype.card ι < fuel)
    {z : EpochState ι} (hz : z ∈ epochDomain a R) (hP : P z) :
    Terminal (run a step h next fuel z).state := by
  obtain ⟨_, hfeas, htr, hn⟩ := run_spec_on ha P next sound closed fuel hz hP
  rcases hn with hn | hn
  · exact hn
  · have hb := htr.length_bound ha.le hstep hh hz hfeas
    have he : ((run a step h next fuel z).walks + (run a step h next fuel z).preps +
        (run a step h next fuel z).cleanups : ℝ) = fuel := by exact_mod_cast hn
    linarith

theorem run_work_le_on {a R step h : ℝ} (ha : 0 < a)
    (P : EpochState ι → Prop)
    (next : EpochState ι → Counted (Event ι))
    (sound : ∀ z ∈ epochDomain a R, P z → (next z).value.Valid a R step h z)
    (closed : ∀ z ∈ epochDomain a R, P z → P ((next z).value.apply a step h z))
    {Q : ℕ} (hwork : ∀ z ∈ epochDomain a R, P z → (next z).cost ≤ Q)
    (fuel : ℕ) {z : EpochState ι} (hz : z ∈ epochDomain a R) (hP : P z) :
    (run a step h next fuel z).work ≤ fuel * Q := by
  induction fuel generalizing z with
  | zero => simp [run, Result.stay]
  | succ fuel ih =>
    have hf := Event.valid_feasible ha hz (sound z hz hP)
    have hnext := closed z hz hP
    have hw := hwork z hz hP
    generalize he : (next z).value = ev at hf hnext
    cases ev with
    | done => simp only [run, he]; nlinarith
    | prepare i =>
      have hr := ih hf hnext
      simp only [run, he, Result.after]
      nlinarith
    | move g =>
      have hr := ih hf hnext
      simp only [run, he, Result.after]
      nlinarith
    | round i =>
      have hr := ih hf hnext
      simp only [run, he, Result.after]
      nlinarith
    | exhaust i =>
      have hr := ih hf hnext
      simp only [run, he, Result.after]
      nlinarith

theorem run_potential_le_on {a R step h : ℝ} (ha : 0 < a)
    (P : EpochState ι → Prop)
    (next : EpochState ι → Counted (Event ι))
    (sound : ∀ z ∈ epochDomain a R, P z → (next z).value.Valid a R step h z)
    (closed : ∀ z ∈ epochDomain a R, P z → P ((next z).value.apply a step h z))
    (E : EpochState ι → ℝ) (κ : ℝ)
    (hsafe : ∀ z ∈ epochDomain a R, P z →
      E ((next z).value.apply a step h z) ≤ E z + ((next z).value.cleanups : ℝ) * κ)
    (fuel : ℕ) {z : EpochState ι} (hz : z ∈ epochDomain a R) (hP : P z) :
    E (run a step h next fuel z).state ≤ E z + (run a step h next fuel z).cleanups * κ := by
  induction fuel generalizing z with
  | zero => simp [run, Result.stay]
  | succ fuel ih =>
    have hf := Event.valid_feasible ha hz (sound z hz hP)
    have hnext := closed z hz hP
    have hepot := hsafe z hz hP
    generalize he : (next z).value = ev at hf hepot hnext
    cases ev with
    | done => simp [run, he]
    | prepare i =>
      have hr := ih hf hnext
      simp only [run, he, Result.after, Event.cleanups, zero_add]
      simp only [Event.cleanups, Nat.cast_zero, zero_mul, add_zero] at hepot
      exact hr.trans (add_le_add_right hepot _)
    | move g =>
      have hr := ih hf hnext
      simp only [run, he, Result.after, Event.cleanups, zero_add]
      simp only [Event.cleanups, Nat.cast_zero, zero_mul, add_zero] at hepot
      exact hr.trans (add_le_add_right hepot _)
    | round i =>
      have hr := ih hf hnext
      simp only [run, he, Result.after, Event.cleanups, Nat.cast_add, Nat.cast_one]
      simp only [Event.cleanups, Nat.cast_one, one_mul] at hepot
      linarith
    | exhaust i =>
      have hr := ih hf hnext
      simp only [run, he, Result.after, Event.cleanups, Nat.cast_add, Nat.cast_one]
      simp only [Event.cleanups, Nat.cast_one, one_mul] at hepot
      linarith

theorem run_potential_card_bound_on {a R step h : ℝ} (ha : 0 < a) (hstep : 0 ≤ step)
    (P : EpochState ι → Prop)
    (next : EpochState ι → Counted (Event ι))
    (sound : ∀ z ∈ epochDomain a R, P z → (next z).value.Valid a R step h z)
    (closed : ∀ z ∈ epochDomain a R, P z → P ((next z).value.apply a step h z))
    (E : EpochState ι → ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hsafe : ∀ z ∈ epochDomain a R, P z →
      E ((next z).value.apply a step h z) ≤ E z + ((next z).value.cleanups : ℝ) * κ)
    (fuel : ℕ) {z : EpochState ι} (hz : z ∈ epochDomain a R) (hP : P z) :
    E (run a step h next fuel z).state ≤ E z + Fintype.card ι * κ := by
  have hs := run_spec_on ha P next sound closed fuel hz hP
  have ht := hs.2.2.1.cleanup_bound ha.le hstep
  have hc : (run a step h next fuel z).cleanups ≤ Fintype.card ι := by
    have hn := activeCount_le_card z
    omega
  have hc' : ((run a step h next fuel z).cleanups : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast hc
  exact (run_potential_le_on ha P next sound closed E κ hsafe fuel hz hP).trans
    (add_le_add_left (mul_le_mul_of_nonneg_right hc' hκ) _)

end HigherRankKSRuntime.ControllerLoop
