import MatrixSpencer.RectangularRidgeEpochInput
import MatrixSpencer.RectangularRidgeStoppedSampler
import MatrixSpencer.MSManuscriptSamplerTools

/-!
# Actual finite fixed-universe rectangular ridge epoch

Preparation executes the proved finite SDP-value-difference controller and
finite stored-frame cleanup. Movement samples the exact positive LDL columns
of the computed frozen/radial short, withdraws its matched covariance and
rounds newly frozen coordinates. Neither preparation success nor a favorable
random draw is supplied. The literal natural-number iteration cap is a
polynomial; the operational stopping time uses the actual response coefficient.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeEpochRun
open MSManuscriptAdaptive MSManuscriptSupportedOwner
open MSManuscriptNumericalEpochLedger (State Q Draws afterMove CenteredInvariant samplingSpace)
open RectangularRidgeEpochInput
open RectangularRidgePreparationData (floor)
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgeEpochRunCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1400000
set_option exponentiation.threshold 2048
set_option maxRecDepth 16384
attribute [local irreducible] RectangularRidgePreparation.prepare RectangularRidgePreparationRun.output
  RectangularRidgePreparationRun.run RectangularRidgeSolverPreparation.report

abbrev Certified (c : Config N d) := {s : State N //
  RectangularRidgeLiveEpochLedger.Invariant (margin N) floor (‖c.start‖ ^ 2) (live c) (oldFrozen c) s ∧
    CenteredInvariant c.start s ∧ s.time ≤ duration c}

def Stopped (c : Config N d) (s : State N) : Prop :=
  RectangularRidgeLiveEpochLedger.Terminal (duration c) (live c) (oldFrozen c) s ∨
    duration c < s.time + mesh c ^ 2

def initial (c : Config N d) : Certified c :=
  ⟨RectangularRidgeLiveOwner.initial c.start,
    RectangularRidgeLiveOwner.initial_invariant (by norm_num [floor]) c.start c.start_regular,
    RectangularRidgeLiveOwner.initial_centered c.start, (duration_pos c).le⟩

def preparationResult (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (s : Certified c) : Owner N × ℕ :=
  (RectangularRidgePreparation.prepare solver a (params c s.val.point)
    (params_valid c s.val.point s.property.1.regular.1) s.val.owner).get
      (RectangularRidgePreparation.prepare_isSome solver a (params c s.val.point)
        (params_valid c s.val.point s.property.1.regular.1) s.val.owner
        ⟨s.property.1.owner_valid, s.property.1.owner_le_one, s.property.1.dim_le.trans (live_le c)⟩)

theorem preparationResult_eq (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (s : Certified c) :
    RectangularRidgePreparation.prepare solver a (params c s.val.point)
      (params_valid c s.val.point s.property.1.regular.1) s.val.owner =
        some (preparationResult solver a c s) := (Option.some_get _).symm

theorem prepare_certificate (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (s : Certified c) :
    RectangularRidgePreparationRun.Certificate (params c s.val.point) s.val.owner
      (RectangularRidgePreparationRun.budget (params c s.val.point)) (preparationResult solver a c s) :=
  RectangularRidgePreparation.prepare_sound solver a (params c s.val.point)
    (params_valid c s.val.point s.property.1.regular.1) s.val.owner
    ⟨s.property.1.owner_valid, s.property.1.owner_le_one, s.property.1.dim_le.trans (live_le c)⟩
    (preparationResult_eq solver a c s)

private def certifiedPreparation (c : Config N d) (s : Certified c)
    (y : Owner N × ℕ)
    (hc : RectangularRidgePreparationRun.Certificate (params c s.val.point) s.val.owner
      (RectangularRidgePreparationRun.budget (params c s.val.point)) y) : Certified c :=
  ⟨RectangularRidgeEpochLedger.afterPrepare (params c s.val.point) s.val y,
    RectangularRidgeLiveEpochLedger.afterPrepare_of_certificate (params c s.val.point)
      (live_le c) s.property.1 hc,
    RectangularRidgeEpochLedger.centered_afterPrepare _ s.property.2.1 _, s.property.2.2⟩

private theorem certifiedPreparation_floor (c : Config N d) (s : Certified c)
    (y : Owner N × ℕ)
    (hc : RectangularRidgePreparationRun.Certificate (params c s.val.point) s.val.owner
      (RectangularRidgePreparationRun.budget (params c s.val.point)) y) :
    (certifiedPreparation c s y hc).val.owner.Valid (2 * floor) := hc.valid

def prepare (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (s : Certified c) : Certified c :=
  certifiedPreparation c s (preparationResult solver a c s) (prepare_certificate solver a c s)

theorem prepare_floor (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (s : Certified c) : (prepare solver a c s).val.owner.Valid (2 * floor) :=
  certifiedPreparation_floor c s (preparationResult solver a c s) (prepare_certificate solver a c s)

private theorem certifiedPreparation_val (c : Config N d) (s : Certified c)
    (y : Owner N × ℕ)
    (hc : RectangularRidgePreparationRun.Certificate (params c s.val.point) s.val.owner
      (RectangularRidgePreparationRun.budget (params c s.val.point)) y) :
    (certifiedPreparation c s y hc).val = RectangularRidgeEpochLedger.afterPrepare (params c s.val.point) s.val y := rfl

theorem prepare_val (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (s : Certified c) :
    (prepare solver a c s).val = RectangularRidgeEpochLedger.afterPrepare (params c s.val.point) s.val
      (preparationResult solver a c s) :=
  certifiedPreparation_val c s (preparationResult solver a c s) (prepare_certificate solver a c s)

private theorem certifiedPreparation_fields (c : Config N d) (s : Certified c)
    (y : Owner N × ℕ)
    (hc : RectangularRidgePreparationRun.Certificate (params c s.val.point) s.val.owner
      (RectangularRidgePreparationRun.budget (params c s.val.point)) y) :
    (certifiedPreparation c s y hc).val.point = s.val.point ∧
    (certifiedPreparation c s y hc).val.centered = s.val.centered ∧
    (certifiedPreparation c s y hc).val.rounding = s.val.rounding := ⟨rfl, rfl, rfl⟩

@[simp] theorem prepare_point (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (s : Certified c) : (prepare solver a c s).val.point = s.val.point :=
  (certifiedPreparation_fields c s (preparationResult solver a c s) (prepare_certificate solver a c s)).1

@[simp] theorem prepare_centered (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (s : Certified c) : (prepare solver a c s).val.centered = s.val.centered :=
  (certifiedPreparation_fields c s (preparationResult solver a c s) (prepare_certificate solver a c s)).2.1

@[simp] theorem prepare_rounding (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (s : Certified c) : (prepare solver a c s).val.rounding = s.val.rounding :=
  (certifiedPreparation_fields c s (preparationResult solver a c s) (prepare_certificate solver a c s)).2.2

private theorem certifiedPreparation_owner_paid (c : Config N d) (s : Certified c)
    (y : Owner N × ℕ)
    (hc : RectangularRidgePreparationRun.Certificate (params c s.val.point) s.val.owner
      (RectangularRidgePreparationRun.budget (params c s.val.point)) y) :
    (certifiedPreparation c s y hc).val.owner = y.1 ∧
    (certifiedPreparation c s y hc).val.paid = s.val.paid +
      RectangularRidgePreparationData.paidSize (params c s.val.point) * (y.2 : ℝ) := ⟨rfl, rfl⟩

@[simp] theorem prepare_owner (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (s : Certified c) :
    (prepare solver a c s).val.owner = (preparationResult solver a c s).1 :=
  (certifiedPreparation_owner_paid c s (preparationResult solver a c s) (prepare_certificate solver a c s)).1

@[simp] theorem prepare_paid (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (s : Certified c) : (prepare solver a c s).val.paid = s.val.paid +
      RectangularRidgePreparationData.paidSize (params c s.val.point) *
        ((preparationResult solver a c s).2 : ℝ) :=
  (certifiedPreparation_owner_paid c s (preparationResult solver a c s) (prepare_certificate solver a c s)).2

private theorem certifiedPreparation_time (c : Config N d) (s : Certified c)
    (y : Owner N × ℕ)
    (hc : RectangularRidgePreparationRun.Certificate (params c s.val.point) s.val.owner
      (RectangularRidgePreparationRun.budget (params c s.val.point)) y) :
    (certifiedPreparation c s y hc).val.time = s.val.time := rfl

@[simp] theorem prepare_time (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (s : Certified c) : (prepare solver a c s).val.time = s.val.time :=
  certifiedPreparation_time c s (preparationResult solver a c s) (prepare_certificate solver a c s)

/-- The live trace estimate proves that the actual retained eigenvector draw list is nonempty. -/
theorem short_trace (c : Config N d) (s : Certified c) (hnt : ¬Stopped c s.val) :
    (live c : ℝ) / 16 ≤ realTrace (Q s.val) ∧ 0 < realTrace (Q s.val) :=
  RectangularRidgeLiveEpochLedger.short_trace_lower (by norm_num [floor]) s.property.1
    (live_large c) (duration_le_third c) (not_or.mp hnt).1

def moveValue (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2 * floor)) (hnt : ¬Stopped c s.val) (z : Draws s.val) : Certified c :=
  ⟨afterMove (margin N) s.val (mesh c) z,
    RectangularRidgeLiveEpochLedger.afterMove_invariant (margin_pos c).le (by norm_num [floor])
      s.property.1 hfloor (mesh_pos c).le (mesh_cube c) (mesh_square c) (short_trace c s hnt).1 z,
    MSManuscriptNumericalEpochLedger.centered_afterMove (margin N) s.property.2.1 _ _,
    le_of_not_gt (not_or.mp hnt).2⟩

def movement (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2 * floor)) (hnt : ¬Stopped c s.val) : Sampler (Certified c) where
  Draws := Draws s.val
  fintypeDraws := inferInstance
  weight := SimpleMS.UniformSampler.weight (samplingSpace s.val)
  value := moveValue c s hfloor hnt
  weight_nonneg z := (SimpleMS.UniformSampler.weight_positive (samplingSpace s.val)
    (SimpleMS.Movement.rank_positive _ _ _ (short_trace c s hnt).2) z).le
  weight_sum := SimpleMS.UniformSampler.weights_sum (samplingSpace s.val)
    (SimpleMS.Movement.rank_positive _ _ _ (short_trace c s hnt).2)

def next (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (s : Certified c) : Sampler (Certified c) := by
  classical
  exact if ht : Stopped c s.val then Sampler.pure s else
    let p := prepare solver a c s
    if hp : Stopped c p.val then Sampler.pure p else movement c p (prepare_floor solver a c s) hp

def run (solver : RectangularRidgeConvexValue.Solver) (a : Fin d) (c : Config N d) :
    ℕ → Certified c → Sampler (Certified c)
  | 0, s => Sampler.pure s
  | k + 1, s => (next solver a c s).bind (run solver a c k)

/-- A positive-clock guard followed by a literal natural polynomial cap.
No real floor or logarithm is evaluated. -/
def count (c : Config N d) : ℕ :=
  if 0 < duration c then 2 ^ 1080 * (d + N + 2) ^ 208 + 1 else 0

theorem count_eq (c : Config N d) : count c = 2 ^ 1080 * (d + N + 2) ^ 208 + 1 :=
  if_pos (duration_pos c)

def output (solver : RectangularRidgeConvexValue.Solver) (a : Fin d) (c : Config N d) :=
  run solver a c (count c) (initial c)

theorem next_stopped (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (s : Certified c) (hs : Stopped c s.val) :
    next solver a c s = Sampler.pure s := by simp only [next, dif_pos hs]

theorem next_nonstopped_time (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (s : Certified c) :
    ∀ z : (next solver a c s).Draws, ¬Stopped c ((next solver a c s).value z).val →
      ((next solver a c s).value z).val.time = s.val.time + mesh c ^ 2 := by
  classical
  by_cases hs : Stopped c s.val
  · rw [next_stopped solver a c s hs]
    intro z hz
    exact (hz hs).elim
  · rw [next, dif_neg hs]
    dsimp only
    by_cases hp : Stopped c (prepare solver a c s).val
    · rw [dif_pos hp]
      intro z hz
      exact (hz hp).elim
    · rw [dif_neg hp]
      intro z _
      exact congrArg (fun t => t + mesh c ^ 2) (prepare_time solver a c s)

theorem run_stopped (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (k : ℕ) (s : Certified c) (hs : Stopped c s.val) :
    ∀ z : (run solver a c k s).Draws, (run solver a c k s).value z = s := by
  induction k with
  | zero => intro z; rfl
  | succ k ih =>
    rw [run, next_stopped solver a c s hs]
    intro z
    exact ih z.2

theorem run_nonstopped_time (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (k : ℕ) (s : Certified c) :
    ∀ z : (run solver a c k s).Draws, ¬Stopped c ((run solver a c k s).value z).val →
      ((run solver a c k s).value z).val.time = s.val.time + (k : ℝ) * mesh c ^ 2 := by
  induction k generalizing s with
  | zero => intro z _; simp [run, Sampler.pure]
  | succ k ih =>
    intro z hz
    let mid := (next solver a c s).value z.1
    have hm : ¬Stopped c mid.val := by
      intro hmid
      have he := run_stopped solver a c k mid hmid z.2
      exact hz (he.symm ▸ hmid)
    have htime := next_nonstopped_time solver a c s z.1 hm
    have htail := ih mid z.2 hz
    change ((run solver a c k mid).value z.2).val.time = _
    rw [htail]
    change mid.val.time = _ at htime
    rw [htime]
    push_cast
    ring

theorem count_time_gt (c : Config N d) : duration c < (count c : ℝ) * mesh c ^ 2 := by
  have hS : 0 < RectangularRidgeNumericalOptimizerFloor.size d N := by linarith [size_one_le c]
  let S := RectangularRidgeNumericalOptimizerFloor.size d N
  have hcast : ((2 ^ 1080 * (d + N + 2) ^ 208 : ℕ) : ℝ) =
      RectangularRidgeNumericalParameters.big S 1080 208 := by
    simp only [RectangularRidgeNumericalParameters.big, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_add, S, RectangularRidgeNumericalOptimizerFloor.size]
  have he : ((2 ^ 1080 * (d + N + 2) ^ 208 : ℕ) : ℝ) * mesh c ^ 2 = 1 := by
    rw [hcast, mesh, RectangularRidgeNumericalParameters.mesh_squared]
    exact mul_inv_cancel₀ (RectangularRidgeNumericalParameters.big_pos hS 1080 208).ne'
  have hp := sq_pos_of_pos (mesh_pos c)
  rw [count_eq]
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, he]
  linarith [duration_le_third c]

attribute [local irreducible] run

/-- A generic fuel comparison avoids normalizing the enormous polynomial cap. -/
theorem run_stopped_of_clock_gt (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (k : ℕ) (s : Certified c)
    (hk : duration c < (k : ℝ) * mesh c ^ 2) (z : (run solver a c k s).Draws) :
    Stopped c ((run solver a c k s).value z).val := by
  by_contra hn
  have ht := run_nonstopped_time solver a c k s z hn
  have hb := ((run solver a c k s).value z).property.2.2
  have hzero := s.property.1.time_nonneg
  linarith

/-- Every sampled path stops at the explicit polynomial cap. -/
theorem output_stopped (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (z : (output solver a c).Draws) :
    Stopped c ((output solver a c).value z).val :=
  run_stopped_of_clock_gt solver a c (count c) (initial c) (count_time_gt c) z

/-- Cube and original-label source support are certified on every draw. -/
theorem output_invariant (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (c : Config N d) (z : (output solver a c).Draws) :
    RectangularRidgeLiveEpochLedger.Invariant (margin N) floor (‖c.start‖ ^ 2) (live c) (oldFrozen c)
      ((output solver a c).value z).val := ((output solver a c).value z).property.1

end MatrixSpencer.RectangularRidgeEpochRun
