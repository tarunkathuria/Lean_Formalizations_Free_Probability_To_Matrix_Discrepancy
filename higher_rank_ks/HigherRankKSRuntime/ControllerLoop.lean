import HigherRankKSRuntime.CleanupCount
import MatrixSpencer.RealRAMJacobiIteration

/-! The finite controller executes tagged concrete updates. Its resource
bound is derived from the executed updates. The local soundness interface
in this module is intermediate and is discharged by the source-specific
value, curvature, and query-domain theorems at the public endpoint. -/

open scoped BigOperators
noncomputable section
namespace HigherRankKSRuntime.ControllerLoop
open AugmentedHigherRankKS
open MatrixSpencer.RealRAM.JacobiIteration (Counted)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

inductive Event (ι : Type*)
  | done
  | prepare (i : ι)
  | move (g : ι → ℝ)
  | round (i : ι)
  | exhaust (i : ι)

def Event.apply (a step h : ℝ) (z : EpochState ι) : Event ι → EpochState ι
  | .done => z
  | .prepare i => prepareOwner a z i step
  | .move g => movement a z g h
  | .round i => roundOwner z i
  | .exhaust i => exhaustOwner a z i

def Event.walks : Event ι → ℕ | .move _ => 1 | _ => 0
def Event.preps : Event ι → ℕ | .prepare _ => 1 | _ => 0
def Event.cleanups : Event ι → ℕ | .round _ | .exhaust _ => 1 | _ => 0

def Terminal (z : EpochState ι) : Prop := ∀ i, reserve z i = 0

def Event.Valid (a R step h : ℝ) (z : EpochState ι) : Event ι → Prop
  | .done => Terminal z
  | .prepare i => prepareOwner a z i step ∈ epochDomain a R
  | .move g => (∑ i, position z i * g i = 0) ∧ (∑ i, (g i) ^ 2 = 1) ∧
      movement a z g h ∈ epochDomain a R
  | .round i => 0 < reserve z i
  | .exhaust i => 0 < reserve z i

theorem Event.valid_feasible {a R step h : ℝ} (ha : 0 < a)
    {z : EpochState ι} (hz : z ∈ epochDomain a R) {e : Event ι}
    (he : e.Valid a R step h z) : e.apply a step h z ∈ epochDomain a R := by
  cases e with
  | done => exact hz
  | prepare i => exact he
  | move g => exact he.2.2
  | round i => exact roundOwner_feasible hz i
  | exhaust i => exact exhaustOwner_feasible hz ha i

theorem Event.trace {a R step h : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) {e : Event ι} (he : e.Valid a R step h z) :
    CountedTrace a R step h z (e.apply a step h z) e.walks e.preps e.cleanups := by
  cases e with
  | done => exact .nil
  | prepare i => exact .prepare .nil i
  | move g => exact .move .nil g he.1 he.2.1
  | round i => exact .round .nil hz i he
  | exhaust i => exact .exhaust .nil hz i he

theorem trace_append {a R step h : ℝ} {x y z : EpochState ι}
    {w₁ p₁ c₁ w₂ p₂ c₂ : ℕ}
    (h₁ : CountedTrace a R step h x y w₁ p₁ c₁)
    (h₂ : CountedTrace a R step h y z w₂ p₂ c₂) :
    CountedTrace a R step h x z (w₁ + w₂) (p₁ + p₂) (c₁ + c₂) := by
  induction h₂ with
  | nil => simpa using h₁
  | prepare prior i ih => simpa only [Nat.add_assoc] using CountedTrace.prepare ih i
  | move prior g ho hu ih => simpa only [Nat.add_assoc] using CountedTrace.move ih g ho hu
  | round prior hz i hi ih => simpa only [Nat.add_assoc] using CountedTrace.round ih hz i hi
  | exhaust prior hz i hi ih => simpa only [Nat.add_assoc] using CountedTrace.exhaust ih hz i hi

structure Result (ι : Type*) where
  state : EpochState ι
  walks : ℕ
  preps : ℕ
  cleanups : ℕ
  work : ℕ

def Result.stay (z : EpochState ι) : Result ι := ⟨z, 0, 0, 0, 0⟩

def Result.after (e : Event ι) (work : ℕ) (r : Result ι) : Result ι :=
  ⟨r.state, e.walks + r.walks, e.preps + r.preps, e.cleanups + r.cleanups, work + r.work⟩

/-- The only early exit is the controller's actual `done` branch. -/
def run (a step h : ℝ) (next : EpochState ι → Counted (Event ι)) :
    ℕ → EpochState ι → Result ι
  | 0, z => Result.stay z
  | fuel + 1, z =>
      let e := next z
      match e.value with
      | .done => ⟨z, 0, 0, 0, e.cost⟩
      | ev => Result.after ev e.cost (run a step h next fuel (ev.apply a step h z))

theorem run_spec {a R step h : ℝ} (ha : 0 < a)
    (next : EpochState ι → Counted (Event ι))
    (sound : ∀ z ∈ epochDomain a R, (next z).value.Valid a R step h z)
    (fuel : ℕ) {z : EpochState ι} (hz : z ∈ epochDomain a R) :
    let r := run a step h next fuel z
    r.state ∈ epochDomain a R ∧
      CountedTrace a R step h z r.state r.walks r.preps r.cleanups ∧
      (Terminal r.state ∨ r.walks + r.preps + r.cleanups = fuel) := by
  induction fuel generalizing z with
  | zero => exact ⟨hz, .nil, Or.inr rfl⟩
  | succ fuel ih =>
    have hs := sound z hz
    have hf := Event.valid_feasible ha hz hs
    have ht := Event.trace hz hs
    generalize he : (next z).value = ev at hs hf ht
    cases ev with
    | done =>
      simp only [run, he]
      exact ⟨hz, .nil, Or.inl hs⟩
    | prepare i =>
      simp only [run, he, Result.after]
      obtain ⟨hrf, hrt, hrn⟩ := ih hf
      refine ⟨hrf, trace_append ht hrt, ?_⟩
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
      obtain ⟨hrf, hrt, hrn⟩ := ih hf
      refine ⟨hrf, trace_append ht hrt, ?_⟩
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
      obtain ⟨hrf, hrt, hrn⟩ := ih hf
      refine ⟨hrf, trace_append ht hrt, ?_⟩
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
      obtain ⟨hrf, hrt, hrn⟩ := ih hf
      refine ⟨hrf, trace_append ht hrt, ?_⟩
      rcases hrn with hn | hn
      · exact Or.inl hn
      · right
        simp only [run, he, Result.after, Event.walks, Event.preps, Event.cleanups]
        change (0 + (run a step h next fuel _).walks) +
          (0 + (run a step h next fuel _).preps) +
          (1 + (run a step h next fuel _).cleanups) = _
        omega

theorem run_terminal {a R step h : ℝ} (ha : 0 < a) (hstep : 0 < step) (hh : h ≠ 0)
    (next : EpochState ι → Counted (Event ι))
    (sound : ∀ z ∈ epochDomain a R, (next z).value.Valid a R step h z)
    (fuel : ℕ) (hfuel : (Fintype.card ι : ℝ) / h ^ 2 +
      (Fintype.card ι : ℝ) * (a * R) / step + Fintype.card ι < fuel)
    {z : EpochState ι} (hz : z ∈ epochDomain a R) :
    Terminal (run a step h next fuel z).state := by
  obtain ⟨hfeas, htr, hn⟩ := run_spec ha next sound fuel hz
  rcases hn with hn | hn
  · exact hn
  · have hb := htr.length_bound ha.le hstep hh hz hfeas
    have he : ((run a step h next fuel z).walks + (run a step h next fuel z).preps +
        (run a step h next fuel z).cleanups : ℝ) = fuel := by exact_mod_cast hn
    linarith

theorem run_work_le {a R step h : ℝ} (ha : 0 < a)
    (next : EpochState ι → Counted (Event ι))
    (sound : ∀ z ∈ epochDomain a R, (next z).value.Valid a R step h z)
    {Q : ℕ} (hwork : ∀ z ∈ epochDomain a R, (next z).cost ≤ Q)
    (fuel : ℕ) {z : EpochState ι} (hz : z ∈ epochDomain a R) :
    (run a step h next fuel z).work ≤ fuel * Q := by
  induction fuel generalizing z with
  | zero => simp [run, Result.stay]
  | succ fuel ih =>
    have hf := Event.valid_feasible ha hz (sound z hz)
    have hw := hwork z hz
    generalize he : (next z).value = ev at hf
    cases ev with
    | done => simp only [run, he]; nlinarith
    | prepare i =>
      have hr := ih hf
      simp only [run, he, Result.after]
      nlinarith
    | move g =>
      have hr := ih hf
      simp only [run, he, Result.after]
      nlinarith
    | round i =>
      have hr := ih hf
      simp only [run, he, Result.after]
      nlinarith
    | exhaust i =>
      have hr := ih hf
      simp only [run, he, Result.after]
      nlinarith

theorem run_potential_le {a R step h : ℝ} (ha : 0 < a)
    (next : EpochState ι → Counted (Event ι))
    (sound : ∀ z ∈ epochDomain a R, (next z).value.Valid a R step h z)
    (E : EpochState ι → ℝ) (κ : ℝ)
    (hsafe : ∀ z ∈ epochDomain a R,
      E ((next z).value.apply a step h z) ≤ E z + ((next z).value.cleanups : ℝ) * κ)
    (fuel : ℕ) {z : EpochState ι} (hz : z ∈ epochDomain a R) :
    E (run a step h next fuel z).state ≤ E z + (run a step h next fuel z).cleanups * κ := by
  induction fuel generalizing z with
  | zero => simp [run, Result.stay]
  | succ fuel ih =>
    have hf := Event.valid_feasible ha hz (sound z hz)
    have hepot := hsafe z hz
    generalize he : (next z).value = ev at hf hepot
    cases ev with
    | done => simp [run, he]
    | prepare i =>
      have hr := ih hf
      simp only [run, he, Result.after, Event.cleanups, zero_add]
      simp only [Event.cleanups, Nat.cast_zero, zero_mul, add_zero] at hepot
      exact hr.trans (add_le_add_right hepot _)
    | move g =>
      have hr := ih hf
      simp only [run, he, Result.after, Event.cleanups, zero_add]
      simp only [Event.cleanups, Nat.cast_zero, zero_mul, add_zero] at hepot
      exact hr.trans (add_le_add_right hepot _)
    | round i =>
      have hr := ih hf
      simp only [run, he, Result.after, Event.cleanups, Nat.cast_add, Nat.cast_one]
      simp only [Event.cleanups, Nat.cast_one, one_mul] at hepot
      linarith
    | exhaust i =>
      have hr := ih hf
      simp only [run, he, Result.after, Event.cleanups, Nat.cast_add, Nat.cast_one]
      simp only [Event.cleanups, Nat.cast_one, one_mul] at hepot
      linarith

theorem run_potential_card_bound {a R step h : ℝ} (ha : 0 < a) (hstep : 0 ≤ step)
    (next : EpochState ι → Counted (Event ι))
    (sound : ∀ z ∈ epochDomain a R, (next z).value.Valid a R step h z)
    (E : EpochState ι → ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hsafe : ∀ z ∈ epochDomain a R,
      E ((next z).value.apply a step h z) ≤ E z + ((next z).value.cleanups : ℝ) * κ)
    (fuel : ℕ) {z : EpochState ι} (hz : z ∈ epochDomain a R) :
    E (run a step h next fuel z).state ≤ E z + Fintype.card ι * κ := by
  have hs := run_spec ha next sound fuel hz
  have ht := hs.2.1.cleanup_bound ha.le hstep
  have hc : (run a step h next fuel z).cleanups ≤ Fintype.card ι := by
    have hn := activeCount_le_card z
    omega
  have hc' : ((run a step h next fuel z).cleanups : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast hc
  exact (run_potential_le ha next sound E κ hsafe fuel hz).trans
    (add_le_add_left (mul_le_mul_of_nonneg_right hc' hκ) _)

end HigherRankKSRuntime.ControllerLoop
