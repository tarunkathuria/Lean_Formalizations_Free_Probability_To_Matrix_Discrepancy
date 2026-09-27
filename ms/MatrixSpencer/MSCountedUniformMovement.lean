import MatrixSpencer.MSCountedEpochMovement

/-! Actual uniform-input execution of the counted numerical movement. Every
u in [0,1) is sent through the literal cumulative-weight scan. The selected
label, output and operation count use that same u, and each label fiber has
exactly its original sampler mass. -/
open Matrix Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.CategoricalLabels
open MSPoint (Table)
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem total (L : Table α) (w : α → ℝ) (hw : ∀a,0 ≤ w a) (hs : ∑a,w a=1)
    (u : ℝ) (hu : u∈Ico (0:ℝ) 1) : ∃a,(pick L w u).value=some a := by
  have hnon:=weights_nonneg L w hw
  have hsum:=weights_sum L w hs
  obtain ⟨j,hj⟩:=Categorical.selected_exists (weights L w) hnon hu.1 (hsum.symm ▸ hu.2)
  have hlen:=Categorical.selected_index_lt (weights L w) u hj
  have hlen' : j<L.labels.length := by simpa only [weights,List.length_map] using hlen
  refine ⟨L.labels[j],?_⟩
  simp only [pick,Categorical.scan_value,hj,MSLabelTable.lookup_value]
  exact List.getElem?_eq_getElem hlen'

end MatrixSpencer.RealRAM.CategoricalLabels

namespace MatrixSpencer.MSCountedUniformMovement
open RealRAM
open MSCountedSampler
open MSManuscriptNumericalEpochRun
open MSManuscriptNumericalEpochLedger (Q short_trace_lower samplingSpace)
variable {N d : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4096

theorem covariance_posSemidef (c : Config N d) (s : Certified c) : (Q s.val).PosSemidef :=
  SimpleMS.Movement.covariance_posSemidef s.val.owner.physical (frozenCoordinates s.val.point) s.val.point

theorem trace_pos (c : Config N d) (s : Certified c) (hnt : ¬Stopped c s.val) :
    0<realTrace (Q s.val) :=
  (short_trace_lower c.floor_pos.le s.property.1 c.count_large (not_or.mp hnt).1).2

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
    (hfloor : s.val.owner.Valid (2*c.floor)) (hnt : ¬Stopped c s.val)
    (z : (movement c s hfloor hnt).Draws) :
    (volume.restrict (Ico (0:ℝ) 1)) {u | pick s.val u=some z}=
      ENNReal.ofReal ((movement c s hfloor hnt).weight z) :=
  SimpleMS.CountedSpectralSampler.pick_probability (samplingSpace s.val) (SimpleMS.Movement.rank_positive _ _ _ (trace_pos c s hnt)) z

/-- A uniform-input trace records its selected finite label and the exact
already-counted numerical update. No existential inverse choice is executed. -/
def run (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2*c.floor)) (hnt : ¬Stopped c s.val) (u : ℝ) :
    Option ((movement c s hfloor hnt).Draws × Certified c × ℕ × ℕ) :=
  (pick s.val u).map (fun z=>(z,(MSCountedEpochMovement.value c s hfloor hnt z).value,
    MSCountedEpochMovement.cost c s hfloor hnt u z,1))

theorem selected_execution (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2*c.floor)) (hnt : ¬Stopped c s.val)
    (u : ℝ) (hu : u∈Ico (0:ℝ) 1) (z : (movement c s hfloor hnt).Draws)
    (hz : pick s.val u=some z) :
    (MSCountedEpochMovement.implementation c s hfloor hnt).Executes z
      ((movement c s hfloor hnt).value z) (MSCountedEpochMovement.cost c s hfloor hnt u z) 1 := by
  exact ⟨u,hu,hz,(MSCountedEpochMovement.value_eq c s hfloor hnt z).symm,rfl,rfl⟩

theorem run_execution (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2*c.floor)) (hnt : ¬Stopped c s.val)
    (u : ℝ) (hu : u∈Ico (0:ℝ) 1) :
    ∃z k,run c s hfloor hnt u=some (z,(movement c s hfloor hnt).value z,k,1) ∧
      (MSCountedEpochMovement.implementation c s hfloor hnt).Executes z
        ((movement c s hfloor hnt).value z) k 1 ∧ k ≤ 200000*(N+1)^5 := by
  obtain ⟨z,hz⟩:=pick_total c s hnt u hu
  refine ⟨z,MSCountedEpochMovement.cost c s hfloor hnt u z,?_,
    selected_execution c s hfloor hnt u hu z hz,MSCountedEpochMovement.cost_le c s hfloor hnt u z⟩
  simp only [run,hz,Option.map_some,MSCountedEpochMovement.value_eq]
  rfl

end MatrixSpencer.MSCountedUniformMovement
