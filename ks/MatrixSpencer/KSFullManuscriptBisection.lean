import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic



noncomputable section
namespace MatrixSpencer.KSFullManuscriptBisection

structure Interval where
  lower : ℝ
  upper : ℝ

def width (b : Interval) : ℝ := b.upper - b.lower
def midpoint (b : Interval) : ℝ := (b.lower + b.upper) / 2
def Contains (b : Interval) (opt : ℝ) : Prop := b.lower ≤ opt ∧ opt ≤ b.upper

def CorrectFeasibility (feasible : ℝ → Bool) (opt τ : ℝ) : Prop :=
  ∀ z, (feasible z = true → z ≤ opt) ∧ (feasible z = false → opt ≤ z + τ)

/-- The precise stopping and branch rules from Part II.5. -/
def step (feasible : ℝ → Bool) (ω τ : ℝ) (b : Interval) : Interval :=
  if width b ≤ 2 * ω then b
  else if feasible (midpoint b) then ⟨midpoint b, b.upper⟩
  else ⟨b.lower, midpoint b + τ⟩

def run (feasible : ℝ → Bool) (ω τ : ℝ) : ℕ → Interval → Interval
  | 0, b => b
  | T + 1, b => step feasible ω τ (run feasible ω τ T b)

theorem step_of_stopped (feasible : ℝ → Bool) (ω τ : ℝ) (b : Interval)
    (hb : width b ≤ 2 * ω) : step feasible ω τ b = b := by
  simp only [step, if_pos hb]

theorem step_contains (feasible : ℝ → Bool) (ω τ : ℝ) {opt : ℝ}
    (hf : CorrectFeasibility feasible opt τ) {b : Interval} (hb : Contains b opt) :
    Contains (step feasible ω τ b) opt := by
  unfold step
  split
  · exact hb
  · split
    · exact ⟨(hf _).1 (by assumption), hb.2⟩
    · exact ⟨hb.1, (hf _).2 (by simpa using ‹¬feasible (midpoint b) = true›)⟩

theorem run_contains (feasible : ℝ → Bool) (ω τ : ℝ) {opt : ℝ}
    (hf : CorrectFeasibility feasible opt τ) {b : Interval} (hb : Contains b opt) (T : ℕ) :
    Contains (run feasible ω τ T b) opt := by
  induction T with
  | zero => exact hb
  | succ T ih => exact step_contains feasible ω τ hf ih

theorem active_width_bound (feasible : ℝ → Bool) (ω : ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (b : Interval) (hb : ¬width b ≤ 2 * ω) :
    width (step feasible ω τ b) ≤ width b / 2 + τ := by
  rw [step, if_neg hb]
  split <;> dsimp [width, midpoint] <;> linarith

/-- Either the actual loop has stopped, or its width obeys the geometric
error estimate. No correctness premise on the feasibility answers is needed
for this finite arithmetic contraction statement. -/
theorem run_stopped_or_width_bound (feasible : ℝ → Bool) (ω : ℝ) {τ : ℝ}
    (hτ : 0 ≤ τ) (b : Interval) (T : ℕ) :
    width (run feasible ω τ T b) ≤ 2 * ω ∨
      width (run feasible ω τ T b) ≤ width b / (2 : ℝ) ^ T + 2 * τ := by
  induction T with
  | zero => right; simp only [run, pow_zero, div_one]; linarith
  | succ T ih =>
    by_cases hs : width (run feasible ω τ T b) ≤ 2 * ω
    · left
      rw [run, step_of_stopped feasible ω τ _ hs]
      exact hs
    · right
      have hprev := ih.resolve_left hs
      have hnext := active_width_bound feasible ω hτ (run feasible ω τ T b) hs
      change width (step feasible ω τ (run feasible ω τ T b)) ≤ _
      have he : width b / (2 : ℝ) ^ (T + 1) = (width b / (2 : ℝ) ^ T) / 2 := by
        rw [pow_succ, div_mul_eq_div_div]
      rw [he]
      linarith

/-- An explicit logarithmic number of bisections, expressed with integer
ceiling and integer ceiling-logarithm. -/
def budget (ω : ℝ) (b : Interval) : ℕ := Nat.clog 2 ⌈max 0 (width b / ω)⌉₊

theorem budget_div_width_le {ω : ℝ} (hω : 0 < ω) (b : Interval) :
    width b / (2 : ℝ) ^ budget ω b ≤ ω := by
  have hnat := Nat.le_pow_clog (by norm_num : 1 < 2) ⌈max 0 (width b / ω)⌉₊
  have hpow : (⌈max 0 (width b / ω)⌉₊ : ℝ) ≤ (2 : ℝ) ^ budget ω b := by
    exact_mod_cast hnat
  have hr : width b / ω ≤ (2 : ℝ) ^ budget ω b :=
    (le_max_right _ _).trans ((Nat.le_ceil _).trans hpow)
  have hp : 0 < (2 : ℝ) ^ budget ω b := by positivity
  apply (div_le_iff₀ hp).mpr
  have hx := (div_le_iff₀ hω).mp hr
  nlinarith

theorem run_budget_stopped (feasible : ℝ → Bool) {ω τ : ℝ}
    (hω : 0 < ω) (hτ : 0 ≤ τ) (hτω : τ ≤ ω / 4) (b : Interval) :
    width (run feasible ω τ (budget ω b) b) ≤ 2 * ω := by
  rcases run_stopped_or_width_bound feasible ω hτ b (budget ω b) with hs | hs
  · exact hs
  · have hb := budget_div_width_le hω b
    linarith

def report (feasible : ℝ → Bool) (ω τ : ℝ) (b : Interval) : ℝ :=
  midpoint (run feasible ω τ (budget ω b) b)

/-- The midpoint produced by the actual finite recursion has the requested
value accuracy once the specific feasibility procedure is certified. -/
theorem report_accuracy (feasible : ℝ → Bool) {ω τ opt : ℝ}
    (hω : 0 < ω) (hτ : 0 ≤ τ) (hτω : τ ≤ ω / 4)
    (hf : CorrectFeasibility feasible opt τ) {b : Interval} (hb : Contains b opt) :
    |report feasible ω τ b - opt| ≤ ω := by
  have hc := run_contains feasible ω τ hf hb (budget ω b)
  have hw := run_budget_stopped feasible hω hτ hτω b
  unfold report midpoint
  dsimp [Contains] at hc
  dsimp [width] at hw
  exact abs_le.mpr ⟨by linarith [hc.1, hc.2], by linarith [hc.1, hc.2]⟩

end MatrixSpencer.KSFullManuscriptBisection
