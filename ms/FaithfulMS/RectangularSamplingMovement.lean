import MatrixSpencer.MSCountedUniformMovement
import MatrixSpencer.RectangularRidgeMovementWork

/-! The rectangular movement takes one actual uniform input through the finite
selector. Its selected label, point update and counted execution use the same
input; the measured fiber of each label is exactly its finite sampler mass. -/
open Matrix Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace FaithfulMS.RectangularSamplingMovement
open MatrixSpencer MatrixSpencer.RealRAM
open MSCountedSampler
open RectangularRidgeEpochRun RectangularRidgeEpochInput
open MSManuscriptNumericalEpochLedger (Q short_trace_lower samplingSpace)
variable {N d : ℕ} [Nonempty (Fin d)]
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4096

theorem covariance_posSemidef (c : Config N d) (s : Certified c) : (Q s.val).PosSemidef :=
  SimpleMS.Movement.covariance_posSemidef s.val.owner.physical (frozenCoordinates s.val.point) s.val.point

theorem trace_pos (c : Config N d) (s : Certified c) (hnt : ¬Stopped c s.val) :
    0 < realTrace (Q s.val) := (short_trace c s hnt).2

def pick (s : MSManuscriptNumericalEpochLedger.State N) (u : ℝ) :=
  (SimpleMS.CountedSpectralSampler.pick (samplingSpace s) u).value

theorem pick_total (c : Config N d) (s : Certified c) (hnt : ¬Stopped c s.val)
    (u : ℝ) (hu : u∈Ico (0:ℝ) 1) : ∃z,pick s.val u=some z := by
  have ht:=trace_pos c s hnt
  exact CategoricalLabels.total (SimpleMS.CountedSpectralSampler.table (samplingSpace s.val))
    (SimpleMS.CountedSpectralSampler.weights (samplingSpace s.val)).value
    (fun z=>by rw [SimpleMS.CountedSpectralSampler.weights_value];exact (SimpleMS.UniformSampler.weight_positive (samplingSpace s.val) (SimpleMS.Movement.rank_positive _ _ _ ht) z).le)
    (by simp only [SimpleMS.CountedSpectralSampler.weights_value];exact SimpleMS.UniformSampler.weights_sum (samplingSpace s.val) (SimpleMS.Movement.rank_positive _ _ _ ht))
    u hu

theorem pick_probability (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2*RectangularRidgePreparationData.floor)) (hnt : ¬Stopped c s.val)
    (z : (movement c s hfloor hnt).Draws) :
    (volume.restrict (Ico (0:ℝ) 1)) {u | pick s.val u=some z}=
      ENNReal.ofReal ((movement c s hfloor hnt).weight z) :=
  SimpleMS.CountedSpectralSampler.pick_probability (samplingSpace s.val) (SimpleMS.Movement.rank_positive _ _ _ (trace_pos c s hnt)) z

/-- A uniform-input trace records its selected finite label and the exact
already-counted numerical update. No existential inverse choice is executed. -/
def run (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2*RectangularRidgePreparationData.floor)) (hnt : ¬Stopped c s.val) (u : ℝ) :
    Option ((movement c s hfloor hnt).Draws × Certified c × ℕ × ℕ) :=
  (pick s.val u).map (fun z=>(z,(RectangularRidgeMovementWork.value c s hfloor hnt z).value,
    RectangularRidgeMovementWork.cost c s hfloor hnt u z,1))

theorem selected_execution (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2*RectangularRidgePreparationData.floor)) (hnt : ¬Stopped c s.val)
    (u : ℝ) (hu : u∈Ico (0:ℝ) 1) (z : (movement c s hfloor hnt).Draws)
    (hz : pick s.val u=some z) :
    (RectangularRidgeMovementWork.implementation c s hfloor hnt).Executes z
      ((movement c s hfloor hnt).value z) (RectangularRidgeMovementWork.cost c s hfloor hnt u z) 1 := by
  exact ⟨u,hu,hz,(RectangularRidgeMovementWork.value_eq c s hfloor hnt z).symm,rfl,rfl⟩

theorem run_execution (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2*RectangularRidgePreparationData.floor)) (hnt : ¬Stopped c s.val)
    (u : ℝ) (hu : u∈Ico (0:ℝ) 1) :
    ∃z k,run c s hfloor hnt u=some (z,(movement c s hfloor hnt).value z,k,1) ∧
      (RectangularRidgeMovementWork.implementation c s hfloor hnt).Executes z
        ((movement c s hfloor hnt).value z) k 1 ∧ k ≤ 200000*(N+1)^5 := by
  obtain ⟨z,hz⟩:=pick_total c s hnt u hu
  refine ⟨z,RectangularRidgeMovementWork.cost c s hfloor hnt u z,?_,
    selected_execution c s hfloor hnt u hu z hz,RectangularRidgeMovementWork.cost_le c s hfloor hnt u z⟩
  simp only [run,hz,Option.map_some,RectangularRidgeMovementWork.value_eq]
  rfl

end FaithfulMS.RectangularSamplingMovement
