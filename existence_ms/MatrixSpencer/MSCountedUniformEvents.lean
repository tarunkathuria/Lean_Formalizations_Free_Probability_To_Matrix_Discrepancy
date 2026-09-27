import MatrixSpencer.MSCountedUniformMovement

/-! Measurable pushforward events for the actual uniform-real selector.
Restricted selector fibers are explicit half-open intervals, and every
finite output event has the sum of its original categorical probabilities. -/
open Matrix Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.CategoricalLabels
open MSPoint (Table)
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

def fiber (L : Table α) (w : α → ℝ) (a : α) : Set ℝ :=
  {u | (pick L w u).value=some a}∩Ico 0 1

theorem fiber_eq (L : Table α) (w : α → ℝ) (hw : ∀a,0 ≤ w a)
    (hs : ∑a,w a=1) (a : α) :
    fiber L w a=Ico (Categorical.lower (weights L w) (L.labels.idxOf a))
      (Categorical.lower (weights L w) (L.labels.idxOf a)+w a) := by
  let ws:=weights L w
  let j:=L.labels.idxOf a
  have hj : j<ws.length := by
    simp only [ws,weights,List.length_map,j]
    exact List.idxOf_lt_length_iff.mpr (L.complete a)
  have he : ws[j]=w a := by simp only [ws,weights,j,List.getElem_map,List.getElem_idxOf]
  have hnon:=weights_nonneg L w hw
  have hsum:=weights_sum L w hs
  change fiber L w a=Ico (Categorical.lower ws j) (Categorical.lower ws j+w a)
  rw [←he]
  ext u
  simp only [fiber,mem_inter_iff,mem_setOf_eq,mem_Ico,pick_iff,Categorical.scan_value]
  constructor
  · intro h
    exact (Categorical.selected_iff ws hnon j hj u).mp ⟨h.2.1,h.1⟩
  · intro h
    have ht:=(Categorical.selected_iff ws hnon j hj u).mpr h
    exact ⟨ht.2,ht.1,hsum ▸ Categorical.selected_lt_sum ws hnon ht.1 ht.2⟩

theorem fiber_measurable (L : Table α) (w : α → ℝ) (hw : ∀a,0 ≤ w a)
    (hs : ∑a,w a=1) (a : α) : MeasurableSet (fiber L w a) := by
  rw [fiber_eq L w hw hs a]
  exact measurableSet_Ico

theorem fiber_measure (L : Table α) (w : α → ℝ) (hw : ∀a,0 ≤ w a)
    (hs : ∑a,w a=1) (a : α) : volume (fiber L w a)=ENNReal.ofReal (w a) := by
  change volume ({u | (pick L w u).value=some a}∩Ico (0:ℝ) 1)=_
  rw [←Measure.restrict_apply' measurableSet_Ico]
  exact probability L w hw hs a

theorem event_probability (L : Table α) (w : α → ℝ) (hw : ∀a,0 ≤ w a)
    (hs : ∑a,w a=1) (q : α → Prop) :
    (volume.restrict (Ico (0:ℝ) 1)) {u | ∃a,(pick L w u).value=some a ∧ q a}=
      ENNReal.ofReal (∑a,w a*(if q a then 1 else 0)) := by
  let I:=Finset.univ.filter q
  have he : {u | ∃a,(pick L w u).value=some a ∧ q a}∩Ico (0:ℝ) 1=
      ⋃a∈I,fiber L w a := by
    ext u
    simp only [mem_inter_iff,mem_setOf_eq,mem_iUnion,Finset.mem_filter,Finset.mem_univ,true_and,I,fiber]
    aesop
  have hd : (↑I:Set α).PairwiseDisjoint (fiber L w) := by
    intro a ha b hb hab
    apply Set.disjoint_left.mpr
    intro u hua hub
    exact hab (Option.some.inj (hua.1.symm.trans hub.1))
  rw [Measure.restrict_apply' measurableSet_Ico,he,
    measure_biUnion_finset hd (fun a _=>fiber_measurable L w hw hs a)]
  simp only [fiber_measure L w hw hs]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun a _=>hw a)]
  congr 1
  simp [I,Finset.sum_filter,mul_ite]

end MatrixSpencer.RealRAM.CategoricalLabels

namespace MatrixSpencer.MSCountedUniformMovement
open RealRAM
open MSManuscriptNumericalEpochRun
open MSManuscriptNumericalEpochLedger (Q)
variable {N d : ℕ}
attribute [local instance] Classical.propDecidable

theorem output_event_probability (c : Config N d) (s : Certified c)
    (hf : s.val.owner.Valid (2*c.floor)) (hn : ¬Stopped c s.val) (q : Certified c → Prop) :
    (volume.restrict (Ico (0:ℝ) 1))
      {u | ∃z,pick s.val u=some z ∧ q ((MSCountedEpochMovement.value c s hf hn z).value)}=
      ENNReal.ofReal ((movement c s hf hn).expectation (fun y=>if q y then 1 else 0)) := by
  have ht:=trace_pos c s hn
  have h:=CategoricalLabels.event_probability (MSCountedCategorical.table (Q s.val))
    (MSSampling.weights (Q s.val)).value
    (fun z=>by rw [MSSampling.weights_value];exact (MSManuscriptNumericalSamplerData.weight_pos _ ht z).le)
    (by simp only [MSSampling.weights_value];exact MSManuscriptNumericalSamplerData.weight_sum _ (covariance_posSemidef c s) ht)
    (fun z=>q ((MSCountedEpochMovement.value c s hf hn z).value))
  simpa only [MSCountedEpochMovement.value_eq,MSSampling.weights_value,
    MSManuscriptAdaptive.Sampler.expectation] using h

/-- The event is stated directly on the uniform-input executor, and
includes its polynomial operation bound and one random draw. -/
theorem bounded_run_event_probability (c : Config N d) (s : Certified c)
    (hf : s.val.owner.Valid (2*c.floor)) (hn : ¬Stopped c s.val) (q : Certified c → Prop) :
    (volume.restrict (Ico (0:ℝ) 1))
      {u | ∃z out k,run c s hf hn u=some (z,out,k,1) ∧
        k ≤ 200000*(N+1)^5 ∧ q out}=
      ENNReal.ofReal ((movement c s hf hn).expectation (fun y=>if q y then 1 else 0)) := by
  have he : {u | ∃z out k,run c s hf hn u=some (z,out,k,1) ∧
      k ≤ 200000*(N+1)^5 ∧ q out}=
      {u | ∃z,pick s.val u=some z ∧ q ((MSCountedEpochMovement.value c s hf hn z).value)} := by
    ext u
    cases hz : pick s.val u with
    | none=>simp [run,hz]
    | some z=>
      simp only [mem_setOf_eq,run,hz,Option.map_some,Option.some.injEq,Prod.mk.injEq]
      constructor
      · rintro ⟨j,out,k,⟨hzj,hout,hk,_⟩,hbound,hq⟩
        subst j
        exact ⟨z,rfl,hout.symm ▸ hq⟩
      · rintro ⟨j,hzj,hq⟩
        subst j
        exact ⟨z,_,_,⟨rfl,rfl,rfl,True.intro⟩,
          MSCountedEpochMovement.cost_le c s hf hn u z,hq⟩
  rw [he]
  exact output_event_probability c s hf hn q

end MatrixSpencer.MSCountedUniformMovement
