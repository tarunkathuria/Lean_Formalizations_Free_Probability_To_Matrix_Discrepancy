import MatrixSpencer.MSManuscriptAdaptive

/-! Bounded adaptive epochs with actual returned-state progress and costs.
The data and quantitative one-step hypotheses must be instantiated by an epoch
sampler; no selected successful execution is assumed. -/
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSManuscriptBoundedProcess
open MSManuscriptAdaptive

structure Config (State : Type*) where
  initial : State
  terminal : State → Prop
  progress : State → ℝ
  bound : ℝ
  progress_nonneg : ∀ s, 0 ≤ progress s
  progress_le : ∀ s, progress s ≤ bound
  potential : State → ℝ
  cost : ℝ
  cost_nonneg : 0 ≤ cost
  failureBound : ℝ
  failure_nonneg : 0 ≤ failureBound
  step : State → Sampler (Option State)
  step_sound : ∀ s, ¬ terminal s → ∀ z y, (step s).value z = some y →
    progress s + 1 ≤ progress y ∧ potential y ≤ potential s + cost
  step_failure : ∀ s, ¬ terminal s → (step s).expectation failure ≤ failureBound

variable {State : Type*}

/-- Successful stage states retain the actual scalar progress and cost ledgers. -/
def Stage (P : Config State) (k : ℕ) :=
  {s : State // (P.terminal s ∨ (k:ℝ) ≤ P.progress s) ∧
    P.potential s ≤ P.potential P.initial + (k:ℝ)*P.cost}

def initial (P : Config State) : Stage P 0 :=
  ⟨P.initial, Or.inr (by simpa using P.progress_nonneg P.initial), by simp⟩

def rawStep (P : Config State) (s : State) : Sampler (Option State) :=
  by
    classical
    exact if P.terminal s then Sampler.pure (some s) else P.step s

theorem rawStep_sound (P : Config State) (k : ℕ) (s : Stage P k)
    (z : (rawStep P s.val).Draws) (y : State) (ho : (rawStep P s.val).value z = some y) :
    (P.terminal y ∨ ((k+1:ℕ):ℝ) ≤ P.progress y) ∧
      P.potential y ≤ P.potential P.initial + ((k+1:ℕ):ℝ)*P.cost := by
  have hall : ∀ (z : (rawStep P s.val).Draws) (y : State),
      (rawStep P s.val).value z = some y →
      (P.terminal y ∨ ((k+1:ℕ):ℝ) ≤ P.progress y) ∧
        P.potential y ≤ P.potential P.initial + ((k+1:ℕ):ℝ)*P.cost := by
    classical
    unfold rawStep
    by_cases ht : P.terminal s.val
    · rw [if_pos ht]
      intro z y ho
      have hy : s.val = y := by simpa [Sampler.pure] using ho
      subst y
      refine ⟨Or.inl ht, ?_⟩
      have h := s.property.2
      push_cast
      nlinarith [P.cost_nonneg]
    · rw [if_neg ht]
      intro z y ho
      have hh := P.step_sound s.val ht z y ho
      have hp : (k:ℝ) ≤ P.progress s.val := s.property.1.resolve_left ht
      refine ⟨Or.inr ?_, ?_⟩
      · push_cast; linarith
      · have h := s.property.2
        push_cast; nlinarith
  exact hall z y ho

/-- Proof certificates are attached to actual sampled values without testing them. -/
def step (P : Config State) (k : ℕ) (s : Stage P k) : Sampler (Option (Stage P (k+1))) where
  Draws := (rawStep P s.val).Draws
  fintypeDraws := inferInstance
  weight := (rawStep P s.val).weight
  value z := match he : (rawStep P s.val).value z with
    | none => none
    | some y => some ⟨y, rawStep_sound P k s z y he⟩
  weight_nonneg := (rawStep P s.val).weight_nonneg
  weight_sum := (rawStep P s.val).weight_sum

theorem step_failure (P : Config State) (k : ℕ) (s : Stage P k) :
    (step P k s).expectation failure ≤ P.failureBound := by
  have he : (step P k s).expectation failure = (rawStep P s.val).expectation failure := by
    unfold Sampler.expectation
    apply Finset.sum_congr rfl
    intro z _
    simp only [step]
    split <;> simp_all [MSManuscriptAdaptive.failure]
  rw [he]
  by_cases ht : P.terminal s.val
  · simpa [rawStep, ht] using P.failure_nonneg
  · simpa [rawStep, ht] using P.step_failure s.val ht

def run (P : Config State) (k : ℕ) : Sampler (Option (Stage P k)) :=
  MSManuscriptAdaptive.run (step P) (initial P) k

theorem run_success_probability (P : Config State) (k : ℕ) :
    1-(k:ℝ)*P.failureBound ≤ (run P k).expectation success := by
  simpa using MSManuscriptAdaptive.run_success_ge (step P) (initial P)
    (fun _ => P.failureBound) (fun _ => P.failure_nonneg) (step_failure P) k

theorem final_terminal (P : Config State) (k : ℕ) (hk : P.bound < (k:ℝ))
    (s : Stage P k) : P.terminal s.val := by
  rcases s.property.1 with ht | hp
  · exact ht
  · have hb := P.progress_le s.val
    linarith

/-- The final data output forgets only the proof of the ledgers. -/
def output (P : Config State) (k : ℕ) : Sampler (Option State) where
  Draws := (run P k).Draws
  fintypeDraws := inferInstance
  weight := (run P k).weight
  value z := ((run P k).value z).map Subtype.val
  weight_nonneg := (run P k).weight_nonneg
  weight_sum := (run P k).weight_sum

theorem output_sound (P : Config State) (k : ℕ) (hk : P.bound < (k:ℝ))
    (z : (output P k).Draws) (s : State) (ho : (output P k).value z = some s) :
    P.terminal s ∧ P.potential s ≤ P.potential P.initial + (k:ℝ)*P.cost := by
  change ((run P k).value z).map Subtype.val = some s at ho
  cases h : (run P k).value z with
  | none => simp [h] at ho
  | some t =>
    simp [h] at ho
    subst s
    exact ⟨final_terminal P k hk t, t.property.2⟩

theorem output_event_probability (P : Config State) (k : ℕ) :
    1-(k:ℝ)*P.failureBound ≤ ∑ z, (output P k).weight z *
      (if ((output P k).value z).isSome then 1 else 0) := by
  have h := run_success_probability P k
  convert h using 1
  unfold Sampler.expectation output
  apply Finset.sum_congr rfl
  intro z _
  cases hh : (run P k).value z <;> simp [hh, success]

end MatrixSpencer.MSManuscriptBoundedProcess
