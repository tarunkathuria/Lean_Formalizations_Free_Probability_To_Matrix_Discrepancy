import MatrixSpencer.RealRAMJacobiIteration
import MatrixSpencer.MSManuscriptNumericalHalfPhase

/-! Finite label-table scans and nearest-sign completion for the outer MS
algorithm. Tables contain already stored labels; restricting a table filters
those labels and does not enumerate an abstract subtype by an oracle. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.MSPoint
open JacobiIteration (Counted)
open PhaseRestriction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] Classical.propDecidable

structure Table (ι : Type*) [Fintype ι] where
  labels : List ι
  nodup : labels.Nodup
  complete : ∀ i, i ∈ labels

theorem table_length (L : Table ι) : L.labels.length=Fintype.card ι := by
  have he : L.labels.toFinset=Finset.univ := by ext i; simp [L.complete]
  rw [←List.toFinset_card_of_nodup L.nodup,he,Finset.card_univ]

def finTable (N : ℕ) : Table (Fin N) :=
  ⟨List.finRange N,List.nodup_finRange N,by simp⟩

def frozenScan (x : EuclideanSpace ℝ ι) : List ι → Counted ℕ
  | [] => ⟨0,1⟩
  | i::is =>
      let tail := frozenScan x is
      ⟨if x i=1 ∨ x i = -1 then tail.value+1 else tail.value,tail.cost+10⟩

theorem frozenScan_value (x : EuclideanSpace ℝ ι) (is : List ι) :
    (frozenScan x is).value=(is.filter (fun i => decide (IsSign (x i)))).length := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [frozenScan,ih,IsSign]; split_ifs <;> simp_all

theorem frozenScan_cost (x : EuclideanSpace ℝ ι) (is : List ι) :
    (frozenScan x is).cost=10*is.length+1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [frozenScan,ih]; omega

theorem frozenScan_card (L : Table ι) (x : EuclideanSpace ℝ ι) :
    (frozenScan x L.labels).value=(frozenCoordinates x).card := by
  rw [frozenScan_value,←List.toFinset_card_of_nodup (L.nodup.filter _)]
  congr 1
  ext i
  simp [L.complete,mem_frozenCoordinates]

def liveCount (L : Table ι) (x : EuclideanSpace ℝ ι) : Counted ℕ :=
  let f := frozenScan x L.labels
  ⟨L.labels.length-f.value,f.cost+L.labels.length+3⟩

theorem liveCount_value (L : Table ι) (x : EuclideanSpace ℝ ι) :
    (liveCount L x).value=Fintype.card (Live x) := by
  simp only [liveCount,frozenScan_card,table_length,live_card,FiniteHalfPhase.liveCount]

theorem liveCount_cost (L : Table ι) (x : EuclideanSpace ℝ ι) :
    (liveCount L x).cost=11*Fintype.card ι+4 := by
  simp [liveCount,frozenScan_cost,table_length]; omega

def emptyTest (L : Table ι) (x : EuclideanSpace ℝ ι) : Counted Bool :=
  let k := liveCount L x
  ⟨decide (k.value=0),k.cost+2⟩

theorem emptyTest_value (L : Table ι) (x : EuclideanSpace ℝ ι) :
    (emptyTest L x).value=decide (Fintype.card (Live x)=0) := by
  simp [emptyTest,liveCount_value]

theorem emptyTest_cost (L : Table ι) (x : EuclideanSpace ℝ ι) :
    (emptyTest L x).cost=11*Fintype.card ι+6 := by
  simp [emptyTest,liveCount_cost]

def terminalTest (L : Table ι) (x : EuclideanSpace ℝ ι) : Counted Bool :=
  let f := frozenScan x L.labels
  ⟨decide (L.labels.length≤2*f.value ∨ L.labels.length-f.value<32),f.cost+2*L.labels.length+8⟩

theorem terminalTest_value (L : Table ι) (x : EuclideanSpace ℝ ι) :
    (terminalTest L x).value=decide (FiniteHalfPhase.Terminal x) := by
  simp [terminalTest,table_length,frozenScan_card,FiniteHalfPhase.Terminal,FiniteHalfPhase.liveCount]

theorem terminalTest_cost (L : Table ι) (x : EuclideanSpace ℝ ι) :
    (terminalTest L x).cost=12*Fintype.card ι+9 := by
  simp [terminalTest,frozenScan_cost,table_length]; omega

/-- One scalar comparison and the chosen constant store per label. -/
def complete (L : Table ι) (x : EuclideanSpace ℝ ι) : Counted (EuclideanSpace ℝ ι) :=
  ⟨WithLp.toLp 2 (fun i => if 0≤x i then 1 else -1),6*L.labels.length+1⟩

theorem complete_value (L : Table ι) (x : EuclideanSpace ℝ ι) :
    (complete L x).value=SmallLiveRounding.complete x := by
  ext i
  rfl

theorem complete_cost (L : Table ι) (x : EuclideanSpace ℝ ι) :
    (complete L x).cost=6*Fintype.card ι+1 := by simp [complete,table_length]

def finish (L : Table ι) (ε : ℝ) (x : MSManuscriptPhase.Point (ι:=ι) ε) :
    Counted (MSManuscriptPhase.Point (ι:=ι) ε) :=
  let k := liveCount L x.val
  if h : k.value<32 then
    let y := complete L x.val
    ⟨⟨y.value,by rw [complete_value]; exact SmallLiveRounding.complete_regular x.val ε⟩,
      k.cost+y.cost+3⟩
  else ⟨x,k.cost+2⟩

theorem finish_value (L : Table ι) (ε : ℝ) (x : MSManuscriptPhase.Point (ι:=ι) ε) :
    (finish L ε x).value=MSManuscriptNumericalHalfPhase.finish ε x := by
  simp only [finish,liveCount_value,MSManuscriptNumericalHalfPhase.finish]
  split_ifs
  · apply Subtype.ext
    exact complete_value L x.val
  · rfl

theorem finish_cost (L : Table ι) (ε : ℝ) (x : MSManuscriptPhase.Point (ι:=ι) ε) :
    (finish L ε x).cost≤17*Fintype.card ι+8 := by
  simp only [finish]
  split_ifs <;> dsimp only
  · rw [liveCount_cost,complete_cost]; omega
  · rw [liveCount_cost]; omega

def restrictScan (x : EuclideanSpace ℝ ι) : List ι → Counted (List (Live x))
  | [] => ⟨[],1⟩
  | i::is =>
      let tail := restrictScan x is
      if h : ¬(x i=1 ∨ x i = -1) then
        ⟨⟨i,by simpa only [mem_frozenCoordinates,IsSign] using h⟩::tail.value,tail.cost+10⟩
      else ⟨tail.value,tail.cost+10⟩

theorem restrictScan_value (x : EuclideanSpace ℝ ι) (is : List ι) :
    ((restrictScan x is).value.map Subtype.val)=
      is.filter (fun i => decide (¬IsSign (x i))) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [restrictScan,List.filter_cons]
    split_ifs <;> simp_all [IsSign]

theorem restrictScan_cost (x : EuclideanSpace ℝ ι) (is : List ι) :
    (restrictScan x is).cost=10*is.length+1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [restrictScan,List.length_cons]; split_ifs <;> dsimp <;> omega

def restricted (L : Table ι) (x : EuclideanSpace ℝ ι) : Counted (Table (Live x)) :=
  let s := restrictScan x L.labels
  ⟨{
    labels := s.value
    nodup := by
      have h : (s.value.map Subtype.val).Nodup := by
        rw [restrictScan_value]
        exact L.nodup.filter _
      exact List.Nodup.of_map _ h
    complete := by
      intro i
      have h : (i:ι) ∈ s.value.map Subtype.val := by
        rw [restrictScan_value]
        simp only [List.mem_filter,decide_eq_true_eq]
        exact ⟨L.complete i,by simpa only [mem_frozenCoordinates] using i.property⟩
      obtain ⟨j,hj,he⟩ := List.mem_map.mp h
      have hji : j=i := Subtype.ext he
      simpa only [hji] using hj },s.cost+2⟩

theorem restricted_cost (L : Table ι) (x : EuclideanSpace ℝ ι) :
    (restricted L x).cost=10*Fintype.card ι+3 := by
  simp [restricted,restrictScan_cost,table_length]

end MatrixSpencer.RealRAM.MSPoint
