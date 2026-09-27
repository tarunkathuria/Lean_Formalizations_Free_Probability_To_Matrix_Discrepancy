import MatrixSpencer.MSManuscriptEpochProbability

/-!
# Finite stopped-epoch sampling and local-to-global moment accounting

The executable skeleton tests the current state, prepares its stored owner,
tests again, and otherwise samples the actual move. It never selects a good
sample. Finite stopping and the good-event probability are deduced from local
clock/account identities. This reusable layer does not supply the ridge
preparation or matched-move correctness facts needed by an instantiation.
-/
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RectangularRidgeStoppedSampler
open MSManuscriptAdaptive
variable {α : Type*} (stop : α → Prop) [DecidablePred stop]
    (prepare : α → α) (move : α → Sampler α)

/-- Both stopping tests are made before the corresponding new random draw. -/
def step (s : α) : Sampler α :=
  if stop s then Sampler.pure s else
    let p := prepare s
    if stop p then Sampler.pure p else move p

/-- Every next distribution depends on the actual previously sampled state. -/
def run : ℕ → α → Sampler α
  | 0, s => Sampler.pure s
  | k + 1, s => (step stop prepare move s).bind (run k)

theorem step_account_le (f : α → ℝ)
    (hprepare : ∀ s, f (prepare s) ≤ f s)
    (hmove : ∀ s, ¬stop s → (move s).expectation f ≤ f s) (s : α) :
    (step stop prepare move s).expectation f ≤ f s := by
  classical
  by_cases hs : stop s
  · rw [step, if_pos hs]
    simp only [Sampler.expectation_pure, le_refl]
  · rw [step, if_neg hs]
    dsimp only
    by_cases hp : stop (prepare s)
    · rw [if_pos hp, Sampler.expectation_pure]
      exact hprepare s
    · rw [if_neg hp]
      exact (hmove _ hp).trans (hprepare s)

/-- Conditional account inequalities telescope through an adaptive finite run. -/
theorem run_account_le (f : α → ℝ)
    (hprepare : ∀ s, f (prepare s) ≤ f s)
    (hmove : ∀ s, ¬stop s → (move s).expectation f ≤ f s) (k : ℕ) (s : α) :
    (run stop prepare move k s).expectation f ≤ f s := by
  induction k generalizing s with
  | zero => simp only [run, Sampler.expectation_pure, le_refl]
  | succ k ih =>
    rw [run, Sampler.expectation_bind]
    exact ((step stop prepare move s).expectation_mono (fun q => ih q)).trans
      (step_account_le stop prepare move f hprepare hmove s)

@[simp] theorem step_stopped (s : α) (hs : stop s) : step stop prepare move s = Sampler.pure s := by
  simp only [step, if_pos hs]

/-- Stopped states are literally absorbing, not merely stationary in expectation. -/
theorem run_stopped (k : ℕ) (s : α) (hs : stop s) :
    ∀ z : (run stop prepare move k s).Draws, (run stop prepare move k s).value z = s := by
  induction k with
  | zero => intro z; rfl
  | succ k ih =>
    rw [run, step_stopped stop prepare move s hs]
    intro z
    exact ih z.2

variable (clock : α → ℝ) (Δ : ℝ)

theorem step_nonstopped_clock
    (hprepare : ∀ s, clock (prepare s) = clock s)
    (hmove : ∀ s, ¬stop s → ∀ z : (move s).Draws,
      clock ((move s).value z) = clock s + Δ) (s : α) :
    ∀ z : (step stop prepare move s).Draws, ¬stop ((step stop prepare move s).value z) →
      clock ((step stop prepare move s).value z) = clock s + Δ := by
  classical
  by_cases hs : stop s
  · rw [step_stopped stop prepare move s hs]
    intro z hz
    exact (hz hs).elim
  · rw [step, if_neg hs]
    dsimp only
    by_cases hp : stop (prepare s)
    · rw [if_pos hp]
      intro z hz
      exact (hz hp).elim
    · rw [if_neg hp]
      intro z _
      exact (hmove (prepare s) hp z).trans (by rw [hprepare s])

theorem run_nonstopped_clock
    (hprepare : ∀ s, clock (prepare s) = clock s)
    (hmove : ∀ s, ¬stop s → ∀ z : (move s).Draws,
      clock ((move s).value z) = clock s + Δ) (k : ℕ) (s : α) :
    ∀ z : (run stop prepare move k s).Draws, ¬stop ((run stop prepare move k s).value z) →
      clock ((run stop prepare move k s).value z) = clock s + (k : ℝ) * Δ := by
  induction k generalizing s with
  | zero => intro z hz; simp [run, Sampler.pure]
  | succ k ih =>
    intro z hz
    let mid := (step stop prepare move s).value z.1
    have hm : ¬stop mid := by
      intro hmid
      have he := run_stopped stop prepare move k mid hmid z.2
      exact hz (he.symm ▸ hmid)
    have htime := step_nonstopped_clock stop prepare move clock Δ hprepare hmove s z.1 hm
    have htail := ih mid z.2 hz
    change clock ((run stop prepare move k mid).value z.2) = _
    rw [htail]
    change clock mid = _ at htime
    rw [htime]
    push_cast
    ring

/-- The cap is explicit arithmetic in operational duration and squared mesh. -/
def count (τ Δ : ℝ) : ℕ := ⌊τ / Δ⌋₊ + 1

omit stop prepare move in
lemma count_clock_gt (τ : ℝ) (hΔ : 0 < Δ) : τ < (count τ Δ : ℝ) * Δ := by
  have h := Nat.lt_floor_add_one (τ / Δ)
  have hh : τ / Δ < (count τ Δ : ℝ) := by simpa only [count, Nat.cast_add, Nat.cast_one] using h
  exact (div_lt_iff₀ hΔ).mp hh

/-- Every leaf stops by the explicit finite cap, independently of any probability estimate. -/
theorem output_stopped (τ : ℝ) (hΔ : 0 < Δ)
    (hprepare : ∀ s, clock (prepare s) = clock s)
    (hmove : ∀ s, ¬stop s → ∀ z : (move s).Draws,
      clock ((move s).value z) = clock s + Δ)
    (hbound : ∀ s, clock s ≤ τ) (s : α) (hs : 0 ≤ clock s)
    (z : (run stop prepare move (count τ Δ) s).Draws) :
    stop ((run stop prepare move (count τ Δ) s).value z) := by
  by_contra hn
  have h := run_nonstopped_clock stop prepare move clock Δ hprepare hmove (count τ Δ) s z hn
  have hb := hbound ((run stop prepare move (count τ Δ) s).value z)
  have hc := count_clock_gt Δ τ hΔ
  linarith

end MatrixSpencer.RectangularRidgeStoppedSampler
