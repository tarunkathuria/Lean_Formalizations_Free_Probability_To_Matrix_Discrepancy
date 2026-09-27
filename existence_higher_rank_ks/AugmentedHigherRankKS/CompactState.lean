import AugmentedHigherRankKS.State
import Mathlib.Topology.Order.Compact

open Set
open scoped BigOperators

noncomputable section
namespace AugmentedHigherRankKS

variable {ι : Type*}

theorem continuous_position : Continuous (position : EpochState ι → ι → ℝ) :=
  continuous_fst

theorem continuous_spent : Continuous (spent : EpochState ι → ι → ℝ) :=
  continuous_fst.comp continuous_snd

theorem continuous_reserve : Continuous (reserve : EpochState ι → ι → ℝ) :=
  continuous_snd.comp continuous_snd

theorem isClosed_epochDomain (a R : ℝ) : IsClosed (epochDomain (ι := ι) a R) := by
  have hpos (i : ι) : Continuous (fun z : EpochState ι => position z i) :=
    (continuous_apply i).comp continuous_position
  have hspent (i : ι) : Continuous (fun z : EpochState ι => spent z i) :=
    (continuous_apply i).comp continuous_spent
  have hreserve (i : ι) : Continuous (fun z : EpochState ι => reserve z i) :=
    (continuous_apply i).comp continuous_reserve
  simp only [epochDomain, Set.setOf_forall]
  apply isClosed_iInter
  intro i
  exact (isClosed_le continuous_const (hpos i)).inter
    ((isClosed_le (hpos i) continuous_const).inter
    ((isClosed_le continuous_const (hspent i)).inter
    ((isClosed_le (hspent i) continuous_const).inter
    ((isClosed_le continuous_const (hreserve i)).inter
    ((isClosed_le (hreserve i) continuous_const).inter
    ((isClosed_le ((hreserve i).add (continuous_const.mul (hspent i)))
      continuous_const).inter
    (isClosed_eq ((continuous_const.sub ((hpos i).pow 2)).mul
      (((hreserve i).add (continuous_const.mul (hspent i))).sub continuous_const))
      continuous_const)))))))

theorem isCompact_epochDomain [Finite ι] (a R : ℝ) :
    IsCompact (epochDomain (ι := ι) a R) := by
  let low : EpochState ι := (fun _ => -1, fun _ => 0, fun _ => 0)
  let high : EpochState ι := (fun _ => 1, fun _ => R, fun _ => a * R)
  apply (isCompact_Icc : IsCompact (Icc low high)).of_isClosed_subset
    (isClosed_epochDomain a R)
  intro z hz
  constructor
  · exact ⟨fun i => (hz i).1,
      ⟨fun i => (hz i).2.2.1, fun i => (hz i).2.2.2.2.1⟩⟩
  · exact ⟨fun i => (hz i).2.1,
      ⟨fun i => (hz i).2.2.2.1, fun i => (hz i).2.2.2.2.2.1⟩⟩

def totalReserve [Fintype ι] (z : EpochState ι) : ℝ := ∑ i, reserve z i

theorem continuous_totalReserve [Fintype ι] :
    Continuous (totalReserve : EpochState ι → ℝ) := by
  unfold totalReserve
  exact continuous_finset_sum _ fun i _ =>
    (continuous_apply i).comp continuous_reserve

/-- A genuine compact minimizer, with the reserve tie-break attained as well. -/
theorem exists_lexicographic_minimum [Fintype ι] {a R : ℝ}
    (ha : 0 ≤ a) (hR : 0 ≤ R) (x₀ : ι → ℝ)
    (hx : ∀ i, -1 ≤ x₀ i ∧ x₀ i ≤ 1)
    (F : EpochState ι → ℝ) (hF : ContinuousOn F (epochDomain a R)) :
    ∃ z ∈ epochDomain a R, IsMinOn F (epochDomain a R) z ∧
      ∀ y ∈ epochDomain a R, F y = F z → totalReserve z ≤ totalReserve y := by
  let K := epochDomain (ι := ι) a R
  have hK : IsCompact K := isCompact_epochDomain a R
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn
    ⟨initialState a R x₀, initialState_mem ha hR x₀ hx⟩ hF
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hFr : Continuous (fun y : K => F y) :=
    continuousOn_iff_continuous_restrict.mp hF
  have hlevel : IsCompact {y : K | F y = F z} :=
    (isClosed_eq hFr continuous_const).isCompact
  have hres : Continuous (fun y : K => totalReserve (y : EpochState ι)) :=
    continuous_totalReserve.comp continuous_subtype_val
  obtain ⟨w, hw, hwm⟩ := hlevel.exists_isMinOn
    ⟨⟨z, hz⟩, rfl⟩ hres.continuousOn
  refine ⟨w, w.property, ?_, ?_⟩
  · intro y hy
    change F w ≤ F y
    rw [hw]
    exact hmin hy
  · intro y hy heq
    exact hwm (a := ⟨y, hy⟩) (heq.trans hw)

end AugmentedHigherRankKS
