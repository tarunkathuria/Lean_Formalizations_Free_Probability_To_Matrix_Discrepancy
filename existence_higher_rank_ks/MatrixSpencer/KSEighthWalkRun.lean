import MatrixSpencer.KSEighthPreparedState
import MatrixSpencer.KSSymmetricProgress
import MatrixSpencer.KSFiniteCoinRun

/-!
# Actual finite binary walk geometry on the radius-1/8 cube

The operation first snaps near-boundary coordinates and exhausts the numerical
endpoint tests, then uses a symmetric weighted unit-direction proposal. This is
a one-direction numerical variant of the eighth-cube covariance walk: the
original radius, natural weight `1-x_i^2`, snapping and endpoint deletions are
retained. No full-unit-cube walk is invoked. Numerical direction/value accuracy
and potential drift are separate inputs to later controller assembly.
-/

open Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthWalkRun

variable {N : ℕ}

structure PreparedState (N : ℕ) (ρ τ : ℝ) (report : (Fin N → ℝ) → ℝ) where
  coeff : Fin N → ℝ
  cube : coeff ∈ ksCube (1/8)
  exhausted : KSEighthRetirementLoop.select (1/8) τ report coeff = none
  margin : ∀ i, |coeff i| < 1/8 → ρ < 1/8 - |coeff i|

def terminal {ρ τ : ℝ} {report : (Fin N → ℝ) → ℝ}
    (s : PreparedState N ρ τ report) : Prop := ksVertex (1/8) s.coeff

def signing {ρ τ : ℝ} {report : (Fin N → ℝ) → ℝ}
    (s : PreparedState N ρ τ report) : Fin N → ℝ := fun i => 8 * s.coeff i

theorem terminal_full_signing {ρ τ : ℝ} {report : (Fin N → ℝ) → ℝ}
    (s : PreparedState N ρ τ report) (hs : terminal s) : ∀ i, IsSign (signing s i) := by
  intro i
  rcases hs i with hi | hi <;> simp [signing, hi, IsSign]

structure Controller (N : ℕ) where
  ρ : ℝ
  ρ_pos : 0 < ρ
  τ : ℝ
  report : (Fin N → ℝ) → ℝ
  stepSize : ℝ
  step_pos : 0 < stepSize
  step_le : stepSize ≤ ρ
  direction : PreparedState N ρ τ report → EuclideanSpace ℝ (Fin N)
  direction_norm : ∀ s, ¬terminal s → ‖direction s‖ = 1
  direction_frozen : ∀ s, ¬terminal s → ∀ i, |s.coeff i| = 1/8 → direction s i = 0

abbrev State (C : Controller N) := PreparedState N C.ρ C.τ C.report

def makeState (C : Controller N) (x : Fin N → ℝ) (hx : x ∈ ksCube (1/8)) : State C where
  coeff := KSEighthPreparedState.prepareState (1/8) C.τ C.ρ C.report x
  cube := KSEighthPreparedState.prepareState_mem_cube (by norm_num) C.report hx
  exhausted := KSEighthPreparedState.prepareState_exhausts_tests (by norm_num) C.report x
  margin := KSEighthPreparedState.prepareState_live_margin (by norm_num) C.report x

def initialState (C : Controller N) : State C :=
  makeState C 0 (ksCube_zero (by norm_num))

def proposal (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin N)) (t : ℝ) : Fin N → ℝ :=
  fun i => x i + t * (Real.sqrt (1 - x i ^ 2) * v i)

theorem proposal_eq (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    proposal x v t = WithLp.ofLp ((WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N)) +
      t • KSSymmetricProgress.weightedDirection x v) := rfl

theorem proposal_preserves_frozen (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin N))
    (t : ℝ) (i : Fin N) (hv : v i = 0) : proposal x v t i = x i := by simp [proposal, hv]

theorem proposal_displacement_le (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin N))
    (hv : ‖v‖ = 1) (t : ℝ) (i : Fin N) : |proposal x v t i - x i| ≤ |t| := by
  have hvone : |v i| ≤ 1 := by simpa only [Real.norm_eq_abs, hv] using PiLp.norm_apply_le v i
  have hs : Real.sqrt (1 - x i ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg (x i)])
  simp only [proposal, add_sub_cancel_left, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hm : Real.sqrt (1 - x i ^ 2) * |v i| ≤ 1 := by
    nlinarith [Real.sqrt_nonneg (1 - x i ^ 2), abs_nonneg (v i)]
  simpa only [mul_assoc, mul_one] using mul_le_mul_of_nonneg_left hm (abs_nonneg t)

theorem proposal_mem_cube (x : Fin N → ℝ) (hx : x ∈ ksCube (1/8))
    (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖ = 1)
    (hf : ∀ i, |x i| = 1/8 → v i = 0) {ρ t : ℝ} (ht : |t| ≤ ρ)
    (hm : ∀ i, |x i| < 1/8 → ρ < 1/8 - |x i|) : proposal x v t ∈ ksCube (1/8) := by
  have hall (i : Fin N) : |proposal x v t i| ≤ 1/8 := by
    rcases lt_or_eq_of_le (abs_le.mpr ⟨hx.1 i, hx.2 i⟩) with hi | hi
    · have hd := proposal_displacement_le x v hv t i
      have ha : |proposal x v t i| ≤ |x i| + |proposal x v t i - x i| := by
        calc
          _ = |x i + (proposal x v t i - x i)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      linarith [hm i hi]
    · rw [proposal_preserves_frozen x v t i (hf i hi), hi]
  exact ⟨fun i => (abs_le.mp (hall i)).1, fun i => (abs_le.mp (hall i)).2⟩

theorem weighted_norm_lower (x : Fin N → ℝ) (hx : x ∈ ksCube (1/8))
    (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖ = 1) :
    (1/2 : ℝ) ≤ ‖KSSymmetricProgress.weightedDirection x v‖^2 := by
  have hsq (i : Fin N) : x i ^ 2 ≤ (1/8 : ℝ)^2 :=
    KSCubePreparation.coordinate_sq_le ⟨hx.1 i, hx.2 i⟩
  have hh : (1/2 : ℝ) * ‖v‖^2 ≤ ‖KSSymmetricProgress.weightedDirection x v‖^2 := by
    rw [KSSymmetricProgress.weightedDirection_norm_sq x v (fun i => by nlinarith [hsq i]),
      EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simp only [Real.norm_eq_abs, sq_abs]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hsq i]) (sq_nonneg (v i))
  simpa only [hv, one_pow, mul_one] using hh

def signedStep (C : Controller N) (b : Bool) : ℝ := if b then C.stepSize else -C.stepSize

theorem signedStep_abs_le (C : Controller N) (b : Bool) : |signedStep C b| ≤ C.ρ := by
  cases b <;> simpa [signedStep, abs_of_pos C.step_pos] using C.step_le

def step (C : Controller N) (s : State C) (b : Bool) : State C := by
  classical
  exact if ht : terminal s then s else
    makeState C (proposal s.coeff (C.direction s) (signedStep C b))
      (proposal_mem_cube s.coeff s.cube (C.direction s) (C.direction_norm s ht)
        (C.direction_frozen s ht) (signedStep_abs_le C b) s.margin)

theorem step_terminal (C : Controller N) (s : State C) (ht : terminal s) (b : Bool) :
    step C s b = s := by simp [step, ht]

theorem step_active_coeff (C : Controller N) (s : State C) (ht : ¬terminal s) (b : Bool) :
    (step C s b).coeff = KSEighthPreparedState.prepareState (1/8) C.τ C.ρ C.report
      (proposal s.coeff (C.direction s) (signedStep C b)) := by simp [step, ht, makeState]

theorem step_preserves_frozen (C : Controller N) (s : State C) (b : Bool)
    (i : Fin N) (hi : |s.coeff i| = 1/8) : (step C s b).coeff i = s.coeff i := by
  classical
  by_cases ht : terminal s
  · rw [step_terminal C s ht b]
  · rw [step_active_coeff C s ht b]
    have hp := proposal_preserves_frozen s.coeff (C.direction s) (signedStep C b) i
      (C.direction_frozen s ht i hi)
    rw [KSEighthPreparedState.prepareState_preserves_frozen C.report _ i (by rwa [hp]), hp]

def energy (C : Controller N) (s : State C) : ℝ := KSCubePreparation.energy s.coeff

theorem energy_nonneg (C : Controller N) (s : State C) : 0 ≤ energy C s :=
  (KSCubePreparation.energy_bounds s.cube).1

theorem energy_le (C : Controller N) (s : State C) : energy C s ≤ (N : ℝ) / 64 := by
  have he := (KSCubePreparation.energy_bounds s.cube).2
  convert he using 1
  norm_num
  ring

theorem step_energy_progress (C : Controller N) (s : State C) (ht : ¬terminal s) :
    energy C s + C.stepSize^2/2 ≤ (energy C (step C s false) + energy C (step C s true))/2 := by
  have hp (b : Bool) := KSEighthPreparedState.prepareState_energy_progress
    (a := (1/8 : ℝ)) (τ := C.τ) (ρ := C.ρ) (by norm_num) C.report
    (proposal_mem_cube s.coeff s.cube (C.direction s) (C.direction_norm s ht)
      (C.direction_frozen s ht) (signedStep_abs_le C b) s.margin)
  have he : KSCubePreparation.energy s.coeff + C.stepSize^2/2 ≤
      (KSCubePreparation.energy (proposal s.coeff (C.direction s) C.stepSize) +
        KSCubePreparation.energy (proposal s.coeff (C.direction s) (-C.stepSize)))/2 := by
    rw [KSSymmetricProgress.energy_eq_norm_sq, proposal_eq, proposal_eq]
    simp only [KSSymmetricProgress.energy_eq_norm_sq, WithLp.toLp_ofLp, neg_smul, ← sub_eq_add_neg]
    rw [KSSymmetricProgress.symmetric_norm_sq]
    nlinarith [mul_le_mul_of_nonneg_right (weighted_norm_lower s.coeff s.cube
      (C.direction s) (C.direction_norm s ht)) (sq_nonneg C.stepSize)]
  unfold energy
  rw [step_active_coeff C s ht false, step_active_coeff C s ht true]
  simp only [signedStep, Bool.false_eq_true, ↓reduceIte] at hp ⊢
  have hp0 := hp false
  have hp1 := hp true
  simp only [Bool.false_eq_true, ↓reduceIte] at hp0 hp1
  linarith

def run (C : Controller N) (T : ℕ) (s : State C) := KSFiniteCoinRun.runTree terminal (step C) T s

def expectedMovements (C : Controller N) (T : ℕ) (s : State C) : ℝ :=
  KSFiniteCoinRun.expectedSteps terminal (step C) T s

def cutoffProbability (C : Controller N) (T : ℕ) (s : State C) : ℝ :=
  KSFiniteCoinRun.activeProbability terminal (step C) T s

theorem expectedMovements_le (C : Controller N) (T : ℕ) (s : State C) :
    expectedMovements C T s ≤ ((N : ℝ)/64)/(C.stepSize^2/2) :=
  KSFiniteCoinRun.expectedSteps_le terminal (step C) (energy C)
    (div_pos (sq_pos_of_pos C.step_pos) (by norm_num)) (energy_le C) (step_energy_progress C) T s (energy_nonneg C s)

theorem cutoffProbability_le (C : Controller N) (T : ℕ) (hT : 0 < T) (s : State C) :
    cutoffProbability C T s ≤ ((N : ℝ)/64)/(C.stepSize^2/2 * (T : ℝ)) :=
  KSFiniteCoinRun.activeProbability_le terminal (step C) (energy C)
    (div_pos (sq_pos_of_pos C.step_pos) (by norm_num)) (energy_le C) (step_energy_progress C) T hT s (energy_nonneg C s)

theorem leaf_mem_cube (C : Controller N) (T : ℕ) (s : State C) (l : (run C T s).Leaves) :
    ((run C T s).leafState l).coeff ∈ ksCube (1/8) := ((run C T s).leafState l).cube

theorem terminal_leaf_full_signing (C : Controller N) (T : ℕ) (s : State C)
    (l : (run C T s).Leaves) (ht : terminal ((run C T s).leafState l)) :
    ∀ i, IsSign (signing ((run C T s).leafState l) i) := terminal_full_signing _ ht

end MatrixSpencer.KSEighthWalkRun
