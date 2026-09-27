import MatrixSpencer.MSManuscriptNumericalEpochRun
import FaithfulMS.SquareDirectEpochLedger

/-! The direct-density square walk. Optimizing densities give the covariance
response and supporting plane; all walk invariants are proved for this concrete update. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
open MatrixSpencer
namespace FaithfulMS.SquareDirectEpochRun
open MSManuscriptNumericalEpochRun MSManuscriptNumericalEpochLedger MSManuscriptAdaptive
variable [SquareDirectOracle.Oracle]
variable {N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
attribute [local irreducible] ownerPotential
export MSManuscriptNumericalEpochRun (Config Certified params baseMesh mesh params_valid baseMesh_pos baseMesh_cube baseMesh_square mesh_pos mesh_le_base mesh_cube mesh_square mesh_time Stopped initial moveValue movement count count_time_gt)

def preparationResult (c : Config N d) (s : Certified c) : MSManuscriptSupportedOwner.Owner N×ℕ :=
  (SquareDirectPreparation.output (params c s.val) s.val.owner).get
    (SquareDirectPreparation.output_isSome _ (params_valid c s) _
      ⟨s.property.1.owner_valid,s.property.1.owner_le_one,s.property.1.dim_le⟩)

theorem preparationResult_eq (c : Config N d) (s : Certified c) :
    SquareDirectPreparation.output (params c s.val) s.val.owner=some (preparationResult c s) :=
  (Option.some_get _).symm

def prepare (c : Config N d) (s : Certified c) : Certified c :=
  ⟨afterPrepare (params c s.val) s.val (preparationResult c s),
    SquareDirectEpochLedger.afterPrepare_invariant _ (params_valid c s) s.property.1 (preparationResult_eq c s),
    centered_afterPrepare _ s.property.2.1 _,s.property.2.2⟩

theorem prepare_floor (c : Config N d) (s : Certified c) : (prepare c s).val.owner.Valid (2*c.floor) :=
  (SquareDirectPreparation.output_sound _ (params_valid c s) _
    ⟨s.property.1.owner_valid,s.property.1.owner_le_one,s.property.1.dim_le⟩
    (preparationResult_eq c s)).valid

def next (c : Config N d) (s : Certified c) : Sampler (Certified c) := by
  classical
  exact if ht : Stopped c s.val then Sampler.pure s else
    let p := prepare c s
    if hp : Stopped c p.val then Sampler.pure p else movement c p (prepare_floor c s) hp

/-- All product weights are formed along the actual previously sampled state. -/

def run (c : Config N d) : ℕ → Certified c → Sampler (Certified c)
  | 0,s => Sampler.pure s
  | k+1,s => (next c s).bind (run c k)

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

end FaithfulMS.SquareDirectEpochRun
