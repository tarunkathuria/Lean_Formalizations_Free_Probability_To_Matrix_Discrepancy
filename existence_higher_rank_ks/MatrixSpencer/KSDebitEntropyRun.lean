import MatrixSpencer.KSCubeEntropyMovement
import MatrixSpencer.KSDebitWalkRun

/-!
# Entropy stopping bounds for the actual debit walk

These estimates use the already defined binary proposal-and-preparation run.
The proved entropy decrease removes the extra inverse-margin factor from the
earlier squared-coordinate-energy stopping estimate. Report accuracy and
unit live-supported directions are still the controller's explicit inputs;
potential drift and final discrepancy quality are not asserted here.
-/

open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSDebitEntropyRun

open KSDebitWalkRun KSCubeEntropyMovement
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

def progress (C : Controller N n) (s : State C) : ℝ :=
  (N : ℝ) * (2 * Real.log 2) - entropy s.coeff

theorem progress_nonneg (C : Controller N n) (s : State C) : 0 ≤ progress C s :=
  sub_nonneg.mpr (entropy_bounds s.cube).2

theorem progress_le (C : Controller N n) (s : State C) :
    progress C s ≤ (N : ℝ) * (2 * Real.log 2) :=
  sub_le_self _ (entropy_bounds s.cube).1

theorem step_entropy_drop (C : Controller N n) (s : State C) (ht : ¬terminal s) :
    (entropy (step C s false).coeff + entropy (step C s true).coeff) / 2 ≤
      entropy s.coeff - C.stepSize ^ 2 := by
  have hp := prepared_entropy_drop (t := C.stepSize) C.η C.report s.coeff s.cube
    (C.direction s) (C.direction_norm s ht) (C.direction_frozen s ht)
    C.δ_pos (by simpa only [abs_of_pos C.step_pos] using C.step_le) s.margin
  rw [step_active_coeff C s ht false, step_active_coeff C s ht true]
  simpa only [signedStep, Bool.false_eq_true, ↓reduceIte, add_comm] using hp

theorem step_progress (C : Controller N n) (s : State C) (ht : ¬terminal s) :
    progress C s + C.stepSize ^ 2 ≤
      (progress C (step C s false) + progress C (step C s true)) / 2 := by
  have hp := step_entropy_drop C s ht
  unfold progress
  linarith


theorem expectedMovements_le (C : Controller N n) (T : ℕ) (s : State C) :
    expectedMovements C T s ≤ ((N : ℝ) * (2 * Real.log 2)) / C.stepSize ^ 2 :=
  KSFiniteCoinRun.expectedSteps_le terminal (step C) (progress C)
    (sq_pos_of_pos C.step_pos) (progress_le C) (step_progress C) T s (progress_nonneg C s)

theorem cutoffProbability_le (C : Controller N n) (T : ℕ) (hT : 0 < T) (s : State C) :
    cutoffProbability C T s ≤ ((N : ℝ) * (2 * Real.log 2)) / (C.stepSize ^ 2 * (T : ℝ)) :=
  KSFiniteCoinRun.activeProbability_le terminal (step C) (progress C)
    (sq_pos_of_pos C.step_pos) (progress_le C) (step_progress C) T hT s (progress_nonneg C s)

theorem cutoffProbability_from_zero_le (C : Controller N n) (T : ℕ) (hT : 0 < T) :
    cutoffProbability C T (initialState C) ≤
      ((N : ℝ) * (2 * Real.log 2)) / (C.stepSize ^ 2 * (T : ℝ)) :=
  cutoffProbability_le C T hT (initialState C)

end MatrixSpencer.KSDebitEntropyRun
