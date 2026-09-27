import MatrixSpencer.MSManuscriptBoundedProcess
import MatrixSpencer.PartialColoringIteration

/-! Adaptive finite full-coloring composition from actual half-coloring samplers.
All branches are retained. Each phase is charged to the remaining square-root
budget, and failed phases remain an explicit `none` output. -/
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSManuscriptFullProcess
open MSManuscriptAdaptive
variable {State : Type*}

structure Factory (live : State → ℕ) (potential : State → ℝ) (B p : ℝ) where
  sample : ∀ s, 0 < live s → Sampler (Option State)
  sound : ∀ s hs z y, (sample s hs).value z = some y →
    2*live y ≤ live s ∧ potential y ≤ potential s + B*Real.sqrt (live s : ℝ)
  failure_le : ∀ s hs, (sample s hs).expectation MSManuscriptAdaptive.failure ≤ p

variable {live : State → ℕ} {potential : State → ℝ} {B p : ℝ}

def rawStep (F : Factory live potential B p) (s : State) : Sampler (Option State) := by
  classical
  exact if hs : 0 < live s then F.sample s hs else Sampler.pure (some s)

def ledger (live : State → ℕ) (potential : State → ℝ) (B : ℝ) (s : State) : ℝ :=
  potential s+4*B*Real.sqrt (live s : ℝ)

theorem rawStep_sound (F : Factory live potential B p) (hB : 0 ≤ B) (s : State) (hs : live s ≠ 0) :
    ∀ z y, (rawStep F s).value z = some y → live y+1 ≤ live s ∧
      ledger live potential B y ≤ ledger live potential B s := by
  classical
  have hp : 0 < live s := Nat.pos_of_ne_zero hs
  unfold rawStep
  rw [dif_pos hp]
  intro z y ho
  obtain ⟨hl, hc⟩ := F.sound s hp z y ho
  have hhalf : (live y:ℝ) ≤ (1-(1:ℝ)/2)*(live s:ℝ) := by
    have h := Nat.cast_le (α := ℝ).mpr hl
    push_cast at h
    linarith
  have hb := PartialColoringIteration.phase_cost_le_budget_drop (β := (1:ℝ)/2)
    (by norm_num) (by norm_num) hB hhalf
  norm_num only [div_div, div_one, mul_one] at hb
  refine ⟨by omega, ?_⟩
  unfold ledger
  convert (show potential y+4*B*Real.sqrt (live y:ℝ) ≤ potential s+4*B*Real.sqrt (live s:ℝ) from by
    nlinarith [hb]) using 1

def config (F : Factory live potential B p) (hB : 0 ≤ B) (hp : 0 ≤ p)
    (N : ℕ) (hlive : ∀ s, live s ≤ N) (start : State) : MSManuscriptBoundedProcess.Config State where
  initial := start
  terminal s := live s = 0
  progress s := (N:ℝ)-(live s:ℝ)
  bound := N
  progress_nonneg s := sub_nonneg.mpr (Nat.cast_le.mpr (hlive s))
  progress_le s := sub_le_self _ (Nat.cast_nonneg _)
  potential := ledger live potential B
  cost := 0
  cost_nonneg := le_rfl
  failureBound := p
  failure_nonneg := hp
  step := rawStep F
  step_sound s hs z y ho := by
    obtain ⟨hl, hc⟩ := rawStep_sound F hB s hs z y ho
    have hcast : (live y:ℝ)+1 ≤ live s := by exact_mod_cast hl
    refine ⟨by linarith, by simpa using hc⟩
  step_failure s hs := by
    classical
    unfold rawStep
    rw [dif_pos (Nat.pos_of_ne_zero hs)]
    exact F.failure_le s _

def output (F : Factory live potential B p) (hB : 0 ≤ B) (hp : 0 ≤ p)
    (N : ℕ) (hlive : ∀ s, live s ≤ N) (start : State) : Sampler (Option State) :=
  MSManuscriptBoundedProcess.output (config F hB hp N hlive start) (N+1)

theorem output_sound (F : Factory live potential B p) (hB : 0 ≤ B) (hp : 0 ≤ p)
    (N : ℕ) (hlive : ∀ s, live s ≤ N) (start : State)
    (z : (output F hB hp N hlive start).Draws) (y : State)
    (ho : (output F hB hp N hlive start).value z = some y) :
    live y = 0 ∧ potential y ≤ potential start+4*B*Real.sqrt (live start:ℝ) := by
  have ht := MSManuscriptBoundedProcess.output_sound (config F hB hp N hlive start) (N+1)
    (by change (N:ℝ) < ((N+1:ℕ):ℝ); exact_mod_cast Nat.lt_succ_self N) z y ho
  change live y = 0 ∧ ledger live potential B y ≤ ledger live potential B start+(N+1:ℕ)*0 at ht
  refine ⟨ht.1, ?_⟩
  simpa only [ledger, ht.1, Nat.cast_zero, Real.sqrt_zero, mul_zero, add_zero] using ht.2

theorem output_event_probability (F : Factory live potential B p) (hB : 0 ≤ B) (hp : 0 ≤ p)
    (N : ℕ) (hlive : ∀ s, live s ≤ N) (start : State) :
    1-((N+1:ℕ):ℝ)*p ≤ ∑ z, (output F hB hp N hlive start).weight z *
      (if ((output F hB hp N hlive start).value z).isSome then 1 else 0) :=
  MSManuscriptBoundedProcess.output_event_probability (config F hB hp N hlive start) (N+1)

end MatrixSpencer.MSManuscriptFullProcess
