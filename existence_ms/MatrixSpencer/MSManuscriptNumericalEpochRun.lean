import MatrixSpencer.MSManuscriptNumericalEpochLedger
import MatrixSpencer.MSManuscriptEpochClock
import MatrixSpencer.MSManuscriptEpochInput
import MatrixSpencer.MSManuscriptSamplerTools

/-! Actual finite numerical epoch: stored-support preparation, finite short,
guarded LDL sampling, matched covariance withdrawal and threshold rounding.
Certificates are proof-only; none selects a favorable draw. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalEpochRun
open MSManuscriptNumericalEpochLedger MSManuscriptAdaptive
variable {N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1200000

structure Config (N d : ℕ) where
  offset : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)
  atoms : Fin N→Matrix (Fin d) (Fin d) ℂ
  hermitian : ∀i,(atoms i).IsHermitian
  contractions : ∀i,‖atoms i‖≤1
  regularizer : ℝ
  floor : ℝ
  threshold : ℝ
  margin : ℝ
  driftError : ℝ
  regularizer_pos : 0<regularizer
  floor_pos : 0<floor
  floor_le_one : floor≤1
  threshold_pos : 0<threshold
  margin_pos : 0 < margin
  driftError_pos : 0<driftError
  dimension_pos : 0<d
  count_large : 32≤N
  start : EuclideanSpace ℝ (Fin N)
  start_regular : CubeRegular margin start

abbrev Certified (c : Config N d) := {s : State N //
  Invariant c.margin c.floor (‖c.start‖^2) s ∧ CenteredInvariant c.start s ∧ s.time≤timeLimit}

def params (c : Config N d) (s : State N) := MSManuscriptEpochInput.params c.offset c.atoms c.hermitian
  c.regularizer c.floor c.threshold c.dimension_pos s.point

def baseMesh (c : Config N d) := MSManuscriptEpochInput.mesh c.offset c.atoms c.hermitian
  c.regularizer c.floor c.threshold c.dimension_pos c.margin c.driftError

def mesh (c : Config N d) := min (baseMesh c) (Real.sqrt (timeLimit/2))

theorem params_valid (c : Config N d) (s : Certified c) : (params c s.val).Valid :=
  MSManuscriptEpochInput.params_valid c.offset c.atoms c.hermitian c.regularizer c.floor c.threshold
    c.dimension_pos c.contractions c.regularizer_pos c.floor_pos c.floor_le_one c.threshold_pos
    s.val.point s.property.1.regular.1

theorem baseMesh_pos (c : Config N d) : 0<baseMesh c :=
  MSManuscriptEpochInput.mesh_pos c.offset c.atoms c.hermitian c.regularizer c.floor c.threshold
    c.dimension_pos c.contractions c.regularizer_pos c.floor_pos c.floor_le_one c.threshold_pos
    c.margin_pos c.driftError_pos

theorem baseMesh_cube (c : Config N d) : baseMesh c*Real.sqrt (N:ℝ)≤c.margin :=
  MSManuscriptEpochInput.mesh_cube c.offset c.atoms c.hermitian c.regularizer c.floor c.threshold
    c.dimension_pos c.contractions c.regularizer_pos c.floor_pos c.floor_le_one c.threshold_pos
    c.margin_pos c.driftError_pos

theorem baseMesh_square (c : Config N d) : (baseMesh c)^2≤1/2 :=
  MSManuscriptEpochInput.mesh_sq_le_half c.offset c.atoms c.hermitian c.regularizer c.floor c.threshold
    c.dimension_pos c.contractions c.regularizer_pos c.floor_pos c.floor_le_one c.threshold_pos
    c.margin_pos c.driftError_pos

theorem mesh_pos (c : Config N d) : 0 < mesh c :=
  lt_min (baseMesh_pos c) (Real.sqrt_pos.mpr (by norm_num [timeLimit]))

theorem mesh_le_base (c : Config N d) : mesh c≤baseMesh c := min_le_left _ _

theorem mesh_cube (c : Config N d) : mesh c*Real.sqrt (N:ℝ)≤c.margin :=
  (mul_le_mul_of_nonneg_right (mesh_le_base c) (Real.sqrt_nonneg _)).trans (baseMesh_cube c)

theorem mesh_square (c : Config N d) : (mesh c)^2≤1/2 :=
  ((sq_le_sq₀ (mesh_pos c).le (baseMesh_pos c).le).mpr (mesh_le_base c)).trans (baseMesh_square c)

theorem mesh_time (c : Config N d) : (mesh c)^2≤timeLimit/2 := by
  have hh: (mesh c)^2≤(Real.sqrt (timeLimit/2))^2 :=
    (sq_le_sq₀ (mesh_pos c).le (Real.sqrt_nonneg _)).mpr (min_le_right _ _)
  simpa only [Real.sq_sqrt (by norm_num [timeLimit] : 0≤timeLimit/2)] using hh

def Stopped (c : Config N d) (s : State N) : Prop := Terminal s ∨ timeLimit<s.time+(mesh c)^2

def initial (c : Config N d) : Certified c :=
  ⟨MSManuscriptNumericalEpochLedger.initial c.start,
    initial_invariant c.margin_pos.le c.floor_le_one c.start c.start_regular,
    initial_centered c.start,by norm_num [MSManuscriptNumericalEpochLedger.initial,timeLimit]⟩

def preparationResult (c : Config N d) (s : Certified c) : MSManuscriptSupportedOwner.Owner N×ℕ :=
  (MSManuscriptSupportedPreparation.output (params c s.val) s.val.owner).get
    (MSManuscriptSupportedPreparation.output_isSome _ (params_valid c s) _
      ⟨s.property.1.owner_valid,s.property.1.owner_le_one,s.property.1.dim_le⟩)

theorem preparationResult_eq (c : Config N d) (s : Certified c) :
    MSManuscriptSupportedPreparation.output (params c s.val) s.val.owner=some (preparationResult c s) :=
  (Option.some_get _).symm

def prepare (c : Config N d) (s : Certified c) : Certified c :=
  ⟨afterPrepare (params c s.val) s.val (preparationResult c s),
    afterPrepare_invariant _ (params_valid c s) s.property.1 (preparationResult_eq c s),
    centered_afterPrepare _ s.property.2.1 _,s.property.2.2⟩

theorem prepare_floor (c : Config N d) (s : Certified c) : (prepare c s).val.owner.Valid (2*c.floor) :=
  (MSManuscriptSupportedPreparation.output_sound _ (params_valid c s) _
    ⟨s.property.1.owner_valid,s.property.1.owner_le_one,s.property.1.dim_le⟩
    (preparationResult_eq c s)).valid

def moveValue (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2*c.floor)) (hnt : ¬Stopped c s.val) (z : Draws s.val) : Certified c := by
  have hh:=mesh_pos c
  have hsmall := mesh_cube c
  have hh2 := mesh_square c
  have hq := short_trace_lower c.floor_pos.le s.property.1 c.count_large (not_or.mp hnt).1
  exact ⟨afterMove c.margin s.val (mesh c) z,
    afterMove_invariant c.margin_pos.le c.floor_pos.le s.property.1 hfloor hh.le hsmall hh2 hq.1 z,
    centered_afterMove c.margin s.property.2.1 _ _,
    le_of_not_gt (not_or.mp hnt).2⟩

def movement (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2*c.floor)) (hnt : ¬Stopped c s.val) : Sampler (Certified c) where
  Draws := Draws s.val
  fintypeDraws := inferInstance
  weight := MSManuscriptNumericalMovement.weight s.val.owner.physical (frozenCoordinates s.val.point) s.val.point
  value := moveValue c s hfloor hnt
  weight_nonneg z := (MSManuscriptNumericalMovement.weight_positive _ _ _
    (short_trace_lower c.floor_pos.le s.property.1 c.count_large (not_or.mp hnt).1).2 z).le
  weight_sum := MSManuscriptNumericalMovement.weights_sum _
    (s.property.1.owner_valid.physical_posSemidef _ c.floor_pos.le) _ _
    (short_trace_lower c.floor_pos.le s.property.1 c.count_large (not_or.mp hnt).1).2

def next (c : Config N d) (s : Certified c) : Sampler (Certified c) := by
  classical
  exact if ht : Stopped c s.val then Sampler.pure s else
    let p := prepare c s
    if hp : Stopped c p.val then Sampler.pure p else movement c p (prepare_floor c s) hp

/-- All product weights are formed along the actual previously sampled state. -/
def run (c : Config N d) : ℕ → Certified c → Sampler (Certified c)
  | 0,s => Sampler.pure s
  | k+1,s => (next c s).bind (run c k)

def count (c : Config N d) : ℕ := ⌊timeLimit/(mesh c)^2⌋₊+1
def output (c : Config N d) := run c (count c) (initial c)

theorem output_invariant (c : Config N d) (z : (output c).Draws) :
    Invariant c.margin c.floor (‖c.start‖^2) ((output c).value z).val := ((output c).value z).property.1

theorem output_centered (c : Config N d) (z : (output c).Draws) :
    CenteredInvariant c.start ((output c).value z).val := ((output c).value z).property.2.1


theorem next_stopped (c : Config N d) (s : Certified c) (hs : Stopped c s.val) :
    next c s=Sampler.pure s := by simp only [next,dif_pos hs]

theorem next_nonstopped_time (c : Config N d) (s : Certified c) :
    ∀z : (next c s).Draws, ¬Stopped c ((next c s).value z).val →
      ((next c s).value z).val.time=s.val.time+(mesh c)^2 := by
  classical
  by_cases hs : Stopped c s.val
  · rw [next_stopped c s hs]
    intro z hz
    exact (hz hs).elim
  · rw [next,dif_neg hs]
    dsimp only
    by_cases hp : Stopped c (prepare c s).val
    · rw [dif_pos hp]
      intro z hz
      exact (hz hp).elim
    · rw [dif_neg hp]
      intro z hz
      rfl

theorem run_stopped (c : Config N d) (k : ℕ) (s : Certified c) (hs : Stopped c s.val) :
    ∀z : (run c k s).Draws, (run c k s).value z=s := by
  induction k with
  | zero => intro z; rfl
  | succ k ih =>
    rw [run,next_stopped c s hs]
    intro z
    exact ih z.2

theorem run_nonstopped_time (c : Config N d) (k : ℕ) (s : Certified c) :
    ∀z : (run c k s).Draws, ¬Stopped c ((run c k s).value z).val →
      ((run c k s).value z).val.time=s.val.time+(k:ℝ)*(mesh c)^2 := by
  induction k generalizing s with
  | zero => intro z hz; simp [run,Sampler.pure]
  | succ k ih =>
    intro z hz
    let mid := (next c s).value z.1
    have hm : ¬Stopped c mid.val := by
      intro hmid
      have he := run_stopped c k mid hmid z.2
      exact hz (he.symm ▸ hmid)
    have htime := next_nonstopped_time c s z.1 hm
    have htail := ih mid z.2 hz
    change ((run c k mid).value z.2).val.time=_
    rw [htail]
    change mid.val.time=_ at htime
    rw [htime]
    push_cast
    ring

theorem count_time_gt (c : Config N d) : timeLimit<(count c:ℝ)*(mesh c)^2 := by
  have hb : 0<(mesh c)^2 := sq_pos_of_pos (mesh_pos c)
  have hh := Nat.lt_floor_add_one (timeLimit/(mesh c)^2)
  have hh' : timeLimit/(mesh c)^2<(count c:ℝ) := by
    simpa only [count,Nat.cast_add,Nat.cast_one] using hh
  exact (div_lt_iff₀ hb).mp hh'

theorem output_stopped (c : Config N d) (z : (output c).Draws) :
    Stopped c ((output c).value z).val := by
  by_contra hn
  have ht := run_nonstopped_time c (count c) (initial c) z hn
  have htime := ((output c).value z).property.2.2
  change ((output c).value z).val.time=0+(count c:ℝ)*(mesh c)^2 at ht
  have hb := count_time_gt c
  linarith

/-- If neither cleanup loss nor freezing ended the epoch, the finite output
has run for at least half the prescribed time. -/
theorem output_time_or_freezing (c : Config N d) (z : (output c).Draws)
    (hpaid : ((output c).value z).val.paid+((output c).value z).val.dust≤(N:ℝ)/64) :
    (N:ℝ)/64≤(frozenCoordinates ((output c).value z).val.point).card ∨
      timeLimit/2≤((output c).value z).val.time := by
  have hs := output_stopped c z
  rcases hs with (ht|hf|hp)|ht
  · apply Or.inr
    have hh : 0≤timeLimit := by norm_num [timeLimit]
    linarith
  · exact Or.inl hf
  · exact (not_lt_of_ge hpaid hp).elim
  · exact Or.inr (by have hh := mesh_time c; linarith)


theorem next_frozen_subset (c : Config N d) (s : Certified c) :
    ∀z : (next c s).Draws, frozenCoordinates s.val.point⊆frozenCoordinates ((next c s).value z).val.point := by
  classical
  by_cases hs : Stopped c s.val
  · rw [next_stopped c s hs]
    intro z
    exact Finset.Subset.refl _
  · rw [next,dif_neg hs]
    dsimp only
    by_cases hp : Stopped c (prepare c s).val
    · rw [dif_pos hp]
      intro z
      exact Finset.Subset.refl _
    · rw [dif_neg hp]
      intro z
      exact MSManuscriptNumericalCoordinateStep.frozen_subset
        ((prepare c s).property.1.owner_valid.physical_posSemidef _ c.floor_pos.le) _ _ _ _

theorem run_frozen_subset (c : Config N d) (k : ℕ) (s : Certified c) :
    ∀z : (run c k s).Draws, frozenCoordinates s.val.point⊆frozenCoordinates ((run c k s).value z).val.point := by
  induction k generalizing s with
  | zero => intro z; exact Finset.Subset.refl _
  | succ k ih =>
    intro z
    exact (next_frozen_subset c s z.1).trans (ih ((next c s).value z.1) z.2)

theorem output_frozen_subset (c : Config N d) (z : (output c).Draws) :
    frozenCoordinates c.start⊆frozenCoordinates ((output c).value z).val.point :=
  run_frozen_subset c (count c) (initial c) z

theorem output_norm_progress (c : Config N d) (z : (output c).Draws) :
    ‖c.start‖^2+(N:ℝ)/16*((output c).value z).val.time≤‖((output c).value z).val.point‖^2 := by
  have h:=output_invariant c z
  linarith [h.norm_progress,h.variance_ge]


theorem next_frozen_value (c : Config N d) (s : Certified c) {i : Fin N}
    (hi : i∈frozenCoordinates s.val.point) :
    ∀z : (next c s).Draws, ((next c s).value z).val.point i=s.val.point i := by
  classical
  by_cases hs : Stopped c s.val
  · rw [next_stopped c s hs]
    intro z
    rfl
  · rw [next,dif_neg hs]
    dsimp only
    by_cases hp : Stopped c (prepare c s).val
    · rw [dif_pos hp]
      intro z
      rfl
    · rw [dif_neg hp]
      intro z
      exact MSManuscriptNumericalCoordinateStep.rounded_preserves_frozen
        ((prepare c s).property.1.owner_valid.physical_posSemidef _ c.floor_pos.le) _ _ _ _ hi

theorem run_frozen_value (c : Config N d) (k : ℕ) (s : Certified c) {i : Fin N}
    (hi : i∈frozenCoordinates s.val.point) :
    ∀z : (run c k s).Draws, ((run c k s).value z).val.point i=s.val.point i := by
  induction k generalizing s with
  | zero => intro z; rfl
  | succ k ih =>
    intro z
    exact (ih ((next c s).value z.1) (next_frozen_subset c s z.1 hi) z.2).trans (next_frozen_value c s hi z.1)

theorem output_frozen_value (c : Config N d) {i : Fin N} (hi : i∈frozenCoordinates c.start)
    (z : (output c).Draws) : ((output c).value z).val.point i=c.start i :=
  run_frozen_value c (count c) (initial c) hi z

end MatrixSpencer.MSManuscriptNumericalEpochRun


