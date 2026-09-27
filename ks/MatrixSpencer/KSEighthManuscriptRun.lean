import MatrixSpencer.KSEighthManuscriptMovement
import MatrixSpencer.KSEighthManuscriptBranchingDrift

/-!
# The actual finite LDL-column eighth-cube run

Every active state factors its supplied high-trace covariance, draws a uniform
live LDL column and sign, moves by that column, then executes the actual snap
and endpoint-preparation loop. The covariance and value procedures are explicit
controller fields, whose numerical implementation is assembled separately.
This module proves the actual finite branching geometry and timeout bound;
it does not assume a successful signing or a drift bound for the potential.
-/

open Matrix Set
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptRun
open KSEighthWalkRun (PreparedState terminal signing terminal_full_signing)
open KSEighthLiveEnumeration KSEighthManuscriptMovement
open FiniteBranchingTermination
variable {N : ℕ}

structure Controller (N : ℕ) where
  ρ : ℝ
  ρ_pos : 0 < ρ
  τ : ℝ
  report : (Fin N → ℝ) → ℝ
  stepSize : ℝ
  step_pos : 0 < stepSize
  step_le : stepSize * Real.sqrt (N : ℝ) ≤ ρ
  covariance : (s : PreparedState N ρ τ report) →
    Matrix (Fin (count s.coeff)) (Fin (count s.coeff)) ℝ
  covariance_posSemidef : ∀ s, (covariance s).PosSemidef
  covariance_le_one : ∀ s, covariance s ≤ 1
  covariance_trace : ∀ s, ¬terminal s → (3/4 : ℝ)*count s.coeff ≤ Matrix.trace (covariance s)

abbrev State (C : Controller N) := PreparedState N C.ρ C.τ C.report

def makeState (C : Controller N) (x : Fin N → ℝ) (hx : x ∈ ksCube (1/8)) : State C where
  coeff := KSEighthPreparedState.prepareState (1/8) C.τ C.ρ C.report x
  cube := KSEighthPreparedState.prepareState_mem_cube (by norm_num) C.report hx
  exhausted := KSEighthPreparedState.prepareState_exhausts_tests (by norm_num) C.report x
  margin := KSEighthPreparedState.prepareState_live_margin (by norm_num) C.report x

def initialState (C : Controller N) : State C := makeState C 0 (ksCube_zero (by norm_num))

def child (C : Controller N) (s : State C) (z : Fin (count s.coeff) × Bool) : State C :=
  makeState C (proposal s.coeff (C.covariance s) C.stepSize z)
    (proposal_mem_cube s.cube (C.covariance_posSemidef s) (C.covariance_le_one s)
      (by simpa only [abs_of_pos C.step_pos] using C.step_le) s.margin z)

def step (C : Controller N) (s : State C) : Transition (State C) := by
  classical
  exact if ht : terminal s then
    { arity := 1, child := fun _ => s, weight := fun _ => 1,
      weight_pos := fun _ => zero_lt_one, weight_sum := by simp }
  else Transition.ofFintype (child C s) KSEighthManuscriptSampler.weight
    (KSEighthManuscriptSampler.weight_pos (count_pos_of_not_vertex s.cube ht))
    (KSEighthManuscriptSampler.weight_sum (count_pos_of_not_vertex s.cube ht))

theorem step_active_expectation (C : Controller N) (s : State C) (ht : ¬terminal s)
    (f : State C → ℝ) :
    (∑i, (step C s).weight i * f ((step C s).child i)) =
      ∑z, KSEighthManuscriptSampler.weight z * f (child C s z) := by
  classical
  have he : step C s = Transition.ofFintype (child C s) KSEighthManuscriptSampler.weight
      (KSEighthManuscriptSampler.weight_pos (count_pos_of_not_vertex s.cube ht))
      (KSEighthManuscriptSampler.weight_sum (count_pos_of_not_vertex s.cube ht)) := by
    unfold step
    exact dif_neg ht
  rw [he]
  exact Transition.ofFintype_expectation (child C s) KSEighthManuscriptSampler.weight
    (KSEighthManuscriptSampler.weight_pos (count_pos_of_not_vertex s.cube ht))
    (KSEighthManuscriptSampler.weight_sum (count_pos_of_not_vertex s.cube ht)) f

theorem child_preserves_frozen (C : Controller N) (s : State C)
    (z : Fin (count s.coeff) × Bool) (i : Fin N) (hi : |s.coeff i| = (1/8 : ℝ)) :
    (child C s z).coeff i = s.coeff i := by
  change KSEighthPreparedState.prepareState _ _ _ _ _ i = _
  have hp := proposal_frozen s.coeff (C.covariance s) C.stepSize z i hi
  rw [KSEighthPreparedState.prepareState_preserves_frozen C.report _ i (by rwa [hp]), hp]

theorem step_preserves_frozen (C : Controller N) (s : State C)
    (j : Fin (step C s).arity) (i : Fin N) (hi : |s.coeff i| = (1/8 : ℝ)) :
    ((step C s).child j).coeff i = s.coeff i := by
  classical
  have hstep : (∀ j : Fin (step C s).arity, ((step C s).child j).coeff i = s.coeff i) := by
    generalize he : step C s = b
    have hh : b = step C s := he.symm
    unfold step at hh
    split at hh
    · rw [hh]
      intro j
      rfl
    · rw [hh]
      intro j
      exact child_preserves_frozen C s _ i hi
  exact hstep j

def energy (C : Controller N) (s : State C) := KSCubePreparation.energy s.coeff

theorem energy_nonneg (C : Controller N) (s : State C) : 0 ≤ energy C s :=
  (KSCubePreparation.energy_bounds s.cube).1

theorem energy_le (C : Controller N) (s : State C) : energy C s ≤ (N : ℝ)/64 := by
  have he := (KSCubePreparation.energy_bounds s.cube).2
  convert he using 1
  norm_num
  ring

theorem step_energy_progress (C : Controller N) (s : State C) (ht : ¬terminal s) :
    energy C s + C.stepSize^2/2 ≤ ∑i, (step C s).weight i * energy C ((step C s).child i) := by
  rw [step_active_expectation C s ht]
  have he := proposal_energy_progress s.coeff (C.covariance_posSemidef s)
    (count_pos_of_not_vertex s.cube ht) (C.covariance_trace s ht) C.stepSize
  apply he.trans
  apply Finset.sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_left _ (KSEighthManuscriptSampler.weight_pos
    (count_pos_of_not_vertex s.cube ht) z).le
  exact KSEighthPreparedState.prepareState_energy_progress (by norm_num) C.report
    (proposal_mem_cube s.cube (C.covariance_posSemidef s) (C.covariance_le_one s)
      (by simpa only [abs_of_pos C.step_pos] using C.step_le) s.margin z)

def run (C : Controller N) (T : ℕ) (s : State C) :=
  KSEighthManuscriptBranchingRun.runTree terminal (step C) T s

def expectedMovements (C : Controller N) (T : ℕ) (s : State C) :=
  KSEighthManuscriptBranchingRun.expectedSteps terminal (step C) T s

def cutoffProbability (C : Controller N) (T : ℕ) (s : State C) :=
  KSEighthManuscriptBranchingRun.activeProbability terminal (step C) T s

theorem expectedMovements_le (C : Controller N) (T : ℕ) (s : State C) :
    expectedMovements C T s ≤ ((N : ℝ)/64)/(C.stepSize^2/2) :=
  KSEighthManuscriptBranchingRun.expectedSteps_le terminal (step C) (energy C)
    (div_pos (sq_pos_of_pos C.step_pos) (by norm_num)) (energy_le C)
    (step_energy_progress C) T s (energy_nonneg C s)

theorem cutoffProbability_le (C : Controller N) (T : ℕ) (hT : 0 < T) (s : State C) :
    cutoffProbability C T s ≤ ((N : ℝ)/64)/(C.stepSize^2/2*(T : ℝ)) :=
  KSEighthManuscriptBranchingRun.activeProbability_le terminal (step C) (energy C)
    (div_pos (sq_pos_of_pos C.step_pos) (by norm_num)) (energy_le C)
    (step_energy_progress C) T hT s (energy_nonneg C s)

theorem terminal_leaf_full_signing (C : Controller N) (T : ℕ) (s : State C)
    (l : (run C T s).Leaves) (ht : terminal ((run C T s).leafState l)) :
    ∀i, IsSign (signing ((run C T s).leafState l) i) := terminal_full_signing _ ht

end MatrixSpencer.KSEighthManuscriptRun
