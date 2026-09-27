import MatrixSpencer.RealRAMCategorical
import MatrixSpencer.RealRAMMSLabelTable

/-! Exact realization of a finite weighted sampler using its stored label
array and one uniform real input. The label lookup is a literal bounded scan. -/
open MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.CategoricalLabels
open JacobiIteration (Counted)
open MSPoint (Table)
variable {α : Type*} [Fintype α] [DecidableEq α]

def weights (L : Table α) (w : α→ℝ) := L.labels.map w

theorem weights_nonneg (L : Table α) (w : α→ℝ) (hw : ∀a,0≤w a) :
    ∀v∈weights L w,0≤v := by
  intro v hv
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hv
  exact hw a

theorem weights_sum (L : Table α) (w : α→ℝ) (hw : ∑a,w a=1) :
    (weights L w).sum=1 := by
  have he : L.labels.toFinset=Finset.univ := by ext a; simp [L.complete]
  rw [weights,←List.sum_toFinset w L.nodup,he]
  exact hw

def pick (L : Table α) (w : α→ℝ) (u : ℝ) : Counted (Option α) :=
  let c := Categorical.scan (weights L w) u
  match c.value with
  | none => ⟨none,c.cost+2⟩
  | some j => let a := MSLabelTable.lookup L.labels j; ⟨a.value,c.cost+a.cost+2⟩

theorem pick_cost (L : Table α) (w : α→ℝ) (u : ℝ) :
    (pick L w u).cost≤13*L.labels.length+4 := by
  have hc := Categorical.scan_cost (weights L w) u
  rw [show (weights L w).length=L.labels.length from List.length_map w] at hc
  unfold pick
  dsimp only
  split
  · dsimp; omega
  · rename_i j _
    dsimp
    have hl := MSLabelTable.lookup_cost L.labels j
    omega

theorem lookup_iff (L : Table α) (j : ℕ) (a : α) :
    (MSLabelTable.lookup L.labels j).value=some a ↔ j=L.labels.idxOf a := by
  rw [MSLabelTable.lookup_value]
  constructor
  · intro h
    obtain ⟨hj,he⟩ := List.getElem?_eq_some_iff.mp h
    have hi := List.idxOf_getElem L.nodup j hj
    rw [he] at hi
    exact hi.symm
  · rintro rfl
    exact List.getElem?_idxOf (L.complete a)

theorem pick_iff (L : Table α) (w : α→ℝ) (u : ℝ) (a : α) :
    (pick L w u).value=some a ↔
      (Categorical.scan (weights L w) u).value=some (L.labels.idxOf a) := by
  unfold pick
  dsimp only
  split
  · simp_all
  · rename_i j hj
    dsimp
    rw [lookup_iff]
    simp only [hj,Option.some.injEq]

theorem probability (L : Table α) (w : α→ℝ) (hw : ∀a,0≤w a) (hs : ∑a,w a=1) (a : α) :
    (volume.restrict (Ico (0:ℝ) 1)) {u | (pick L w u).value=some a}=ENNReal.ofReal (w a) := by
  have hj : L.labels.idxOf a<(weights L w).length := by
    simp only [weights,List.length_map]
    exact List.idxOf_lt_length_iff.mpr (L.complete a)
  have he : {u | (pick L w u).value=some a}=
      {u | (Categorical.scan (weights L w) u).value=some (L.labels.idxOf a)} := by
    ext u
    exact pick_iff L w u a
  rw [he,Categorical.sampling_probability (weights L w) (weights_nonneg L w hw)
    (weights_sum L w hs) _ hj]
  simp only [weights,List.getElem_map,List.getElem_idxOf]

theorem complete (L : Table α) (w : α→ℝ) (hw : ∀a,0<w a) (hs : ∑a,w a=1) (a : α) :
    ∃u, u∈Ico (0:ℝ) 1 ∧ (pick L w u).value=some a := by
  let j := L.labels.idxOf a
  have hj : j<(weights L w).length := by
    simp only [weights,List.length_map]
    exact List.idxOf_lt_length_iff.mpr (L.complete a)
  have hv : (weights L w)[j]=w a := by simp only [weights,List.getElem_map,List.getElem_idxOf,j]
  let u := Categorical.lower (weights L w) j+w a/2
  have hnon := weights_nonneg L w (fun a => (hw a).le)
  have ht := (Categorical.selected_iff (weights L w) hnon j hj u).mpr (by rw [hv]; constructor <;> dsimp [u] <;> linarith [hw a])
  have hlt : u<1 := (Categorical.selected_lt_sum (weights L w) hnon ht.1 ht.2).trans_eq (weights_sum L w hs)
  refine ⟨u,⟨ht.1,hlt⟩,?_⟩
  rw [pick_iff,Categorical.scan_value]
  exact ht.2

end MatrixSpencer.RealRAM.CategoricalLabels
