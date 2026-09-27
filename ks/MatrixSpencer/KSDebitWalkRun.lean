import MatrixSpencer.KSDebitPreparedMargin
import MatrixSpencer.KSDebitMovement
import MatrixSpencer.KSFiniteCoinRun



open Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSDebitWalkRun

variable {N : ℕ}

/-- A state produced by the actual exhaustive endpoint preparation. -/
structure PreparedState (N : ℕ) (δ η : ℝ) (report : (Fin N → ℝ) → ℝ) where
  coeff : Fin N → ℝ
  cube : coeff ∈ ksCube 1
  exhausted : KSDebitPreparation.Retirement.select 1 (-η) report coeff = none
  margin : ∀ i, |coeff i| < 1 → δ < 1 - |coeff i|

/-- The terminal predicate checks every original label. -/
def terminal {δ η : ℝ} {report : (Fin N → ℝ) → ℝ}
    (s : PreparedState N δ η report) : Prop := ksVertex 1 s.coeff

theorem terminal_iff_full_signing {δ η : ℝ} {report : (Fin N → ℝ) → ℝ}
    (s : PreparedState N δ η report) : terminal s ↔ ∀ i, IsSign (s.coeff i) := by
  constructor <;> intro h i <;> exact (h i).symm

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Data and the outstanding numerical-controller guarantees. The geometric
progress inequality is not an input: it is proved below for the actual step. -/
structure Controller (N : ℕ) (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n] where
  vectors : Fin N → n → ℂ
  δ : ℝ
  δ_pos : 0 < δ
  η : ℝ
  η_nonneg : 0 ≤ η
  θ : ℝ
  θ_pos : 0 < θ
  report : (Fin N → ℝ) → ℝ
  accuracy : ∀ x ∈ ksCube 1,
    |report x - KSDebitPreparation.statePotential vectors δ η θ x| ≤ η / 8
  stepSize : ℝ
  step_pos : 0 < stepSize
  step_le : stepSize ≤ δ / 4
  direction : PreparedState N δ η report → EuclideanSpace ℝ (Fin N)
  direction_norm : ∀ s, ¬terminal s → ‖direction s‖ = 1
  direction_frozen : ∀ s, ¬terminal s → ∀ i, |s.coeff i| = 1 → direction s i = 0

abbrev State (C : Controller N n) := PreparedState N C.δ C.η C.report

/-- Every field is populated from the actual numerical preparation proofs. -/
def makeState (C : Controller N n) (x : Fin N → ℝ) (hx : x ∈ ksCube 1) : State C where
  coeff := KSDebitPreparation.prepare C.η C.report x
  cube := KSDebitPreparation.prepare_mem_cube C.η C.report hx
  exhausted := KSDebitPreparation.prepare_exhausts_tests C.η C.report x
  margin := KSDebitPreparedMargin.prepared_live_margin C.vectors
    C.δ_pos.le C.η_nonneg C.θ_pos C.report C.accuracy hx

def initialState (C : Controller N n) : State C :=
  makeState C 0 (ksCube_zero (by norm_num))

def signedStep (C : Controller N n) (b : Bool) : ℝ := if b then C.stepSize else -C.stepSize

theorem signedStep_abs_le (C : Controller N n) (b : Bool) : |signedStep C b| ≤ C.δ / 4 := by
  cases b <;> simpa [signedStep, abs_of_pos C.step_pos] using C.step_le

/-- Terminal states are absorbed. Otherwise the actual weighted proposal is
followed immediately by the defined exhaustive numerical retirement loop. -/
def step (C : Controller N n) (s : State C) (b : Bool) : State C := by
  classical
  exact if ht : terminal s then s else
    makeState C (KSDebitMovement.proposal s.coeff (C.direction s) (signedStep C b))
      (KSDebitMovement.proposal_mem_cube s.coeff s.cube (C.direction s)
        (C.direction_norm s ht) C.δ_pos (signedStep_abs_le C b) s.margin)

theorem step_terminal (C : Controller N n) (s : State C) (ht : terminal s) (b : Bool) :
    step C s b = s := by simp [step, ht]

theorem step_active_coeff (C : Controller N n) (s : State C) (ht : ¬terminal s) (b : Bool) :
    (step C s b).coeff = KSDebitPreparation.prepare C.η C.report
      (KSDebitMovement.proposal s.coeff (C.direction s) (signedStep C b)) := by
  simp [step, ht, makeState]

theorem step_preserves_frozen (C : Controller N n) (s : State C) (b : Bool)
    (i : Fin N) (hi : |s.coeff i| = 1) : (step C s b).coeff i = s.coeff i := by
  classical
  by_cases ht : terminal s
  · rw [step_terminal C s ht b]
  · rw [step_active_coeff C s ht b]
    have hp := KSDebitMovement.proposal_preserves_frozen s.coeff (C.direction s) (signedStep C b) i hi
    rw [KSDebitPreparation.prepare_preserves_frozen C.η C.report _ i (by rwa [hp]), hp]

def energy (C : Controller N n) (s : State C) : ℝ := KSCubePreparation.energy s.coeff

theorem energy_nonneg (C : Controller N n) (s : State C) : 0 ≤ energy C s :=
  (KSCubePreparation.energy_bounds s.cube).1

theorem energy_le (C : Controller N n) (s : State C) : energy C s ≤ N := by
  simpa only [one_pow, mul_one] using (KSCubePreparation.energy_bounds s.cube).2

/-- The positive drift is derived for the controller's actual two successors,
using the proved weighted proposal and actual preparation operations. -/
theorem step_energy_progress (C : Controller N n) (s : State C) (ht : ¬terminal s) :
    energy C s + C.δ * C.stepSize ^ 2 ≤
      (energy C (step C s false) + energy C (step C s true)) / 2 := by
  have hp := KSDebitMovement.prepared_symmetric_energy_progress (t := C.stepSize)
    C.η C.report s.coeff s.cube
    (C.direction s) (C.direction_norm s ht) (C.direction_frozen s ht)
    C.δ_pos (by simpa only [abs_of_pos C.step_pos] using C.step_le) s.margin
  unfold energy
  rw [step_active_coeff C s ht false, step_active_coeff C s ht true]
  simpa only [signedStep, Bool.false_eq_true, ↓reduceIte, add_comm] using hp

/-- The actual finite leaf tree retains nonterminal cutoff states explicitly. -/
def run (C : Controller N n) (T : ℕ) (s : State C) :=
  KSFiniteCoinRun.runTree terminal (step C) T s

def expectedMovements (C : Controller N n) (T : ℕ) (s : State C) : ℝ :=
  KSFiniteCoinRun.expectedSteps terminal (step C) T s

def cutoffProbability (C : Controller N n) (T : ℕ) (s : State C) : ℝ :=
  KSFiniteCoinRun.activeProbability terminal (step C) T s

theorem expectedMovements_le (C : Controller N n) (T : ℕ) (s : State C) :
    expectedMovements C T s ≤ (N : ℝ) / (C.δ * C.stepSize ^ 2) :=
  KSFiniteCoinRun.expectedSteps_le terminal (step C) (energy C)
    (mul_pos C.δ_pos (sq_pos_of_pos C.step_pos)) (energy_le C) (step_energy_progress C)
    T s (energy_nonneg C s)

theorem cutoffProbability_le (C : Controller N n) (T : ℕ) (hT : 0 < T) (s : State C) :
    cutoffProbability C T s ≤ (N : ℝ) / (C.δ * C.stepSize ^ 2 * (T : ℝ)) :=
  KSFiniteCoinRun.activeProbability_le terminal (step C) (energy C)
    (mul_pos C.δ_pos (sq_pos_of_pos C.step_pos)) (energy_le C) (step_energy_progress C)
    T hT s (energy_nonneg C s)

/-- The designated start is the actual preparation of the zero vector. -/
theorem expectedMovements_from_zero_le (C : Controller N n) (T : ℕ) :
    expectedMovements C T (initialState C) ≤ (N : ℝ) / (C.δ * C.stepSize ^ 2) :=
  expectedMovements_le C T (initialState C)

theorem cutoffProbability_from_zero_le (C : Controller N n) (T : ℕ) (hT : 0 < T) :
    cutoffProbability C T (initialState C) ≤
      (N : ℝ) / (C.δ * C.stepSize ^ 2 * (T : ℝ)) :=
  cutoffProbability_le C T hT (initialState C)

attribute [local instance] Classical.propDecidable

/-- The cutoff quantity is literally the leaf probability of failing to
have a sign on every original label. Repeated endpoint states retain their
separate path occurrences and their correct finite coin weights. -/
theorem cutoffProbability_eq_leaf_sum (C : Controller N n) (T : ℕ) (s : State C) :
    cutoffProbability C T s =
      ∑ l : (run C T s).Leaves, (run C T s).leafWeight l *
        (if ∀ i, IsSign (((run C T s).leafState l).coeff i) then 0 else 1) := by
  classical
  unfold cutoffProbability KSFiniteCoinRun.activeProbability KSFiniteCoinRun.expectation
    FiniteBranchingTermination.Tree.expectation
  apply Finset.sum_congr rfl
  intro l _
  rw [KSStoppedProgress.activeIndicator, terminal_iff_full_signing]
  by_cases hs : ∀ i, IsSign (((run C T s).leafState l).coeff i)
  · dsimp only [run] at hs ⊢
    simp only [if_pos hs]
  · dsimp only [run] at hs ⊢
    simp only [if_neg hs]

theorem leaf_mem_cube (C : Controller N n) (T : ℕ) (s : State C)
    (l : (run C T s).Leaves) : ((run C T s).leafState l).coeff ∈ ksCube 1 :=
  ((run C T s).leafState l).cube

/-- Each original endpoint remains fixed on every actual finite path. -/
theorem leaf_preserves_frozen (C : Controller N n) (T : ℕ) (s : State C)
    (i : Fin N) (hi : |s.coeff i| = 1) (l : (run C T s).Leaves) :
    ((run C T s).leafState l).coeff i = s.coeff i := by
  apply FiniteBranchingTermination.Tree.leaf_invariant (run C T s)
    (fun a => a.coeff i = s.coeff i) rfl _ l
  intro a b hb ha j
  rcases hb with ⟨_, rfl⟩
  change (step C a (decide (j.val = 0))).coeff i = s.coeff i
  rw [step_preserves_frozen C a _ i (by rwa [ha]), ha]

/-- A terminal leaf is a signing on all original labels. A cutoff leaf is
deliberately not declared successful by the finite tree's leaf constructor. -/
theorem terminal_leaf_full_signing (C : Controller N n) (T : ℕ) (s : State C)
    (l : (run C T s).Leaves) (ht : terminal ((run C T s).leafState l)) :
    ∀ i, IsSign (((run C T s).leafState l).coeff i) :=
  (terminal_iff_full_signing _).mp ht

end MatrixSpencer.KSDebitWalkRun
