import MatrixSpencer.RealRAMMSRestriction
import MatrixSpencer.RealRAMMSLabelTransport
import MatrixSpencer.MSCountedEpochFactory

/-! Concrete epoch configuration and output restoration from stored ordered
labels. Frozen-offset accumulation, live data copies, ordered gathers, and
inverse restoration are each charged; proof fields never select data. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RealRAM.MSEpochFactorySetup
open JacobiIteration (Counted)
open MSPoint MSLabelTable PhaseRestriction MSManuscriptPhase
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

/-- Repackage the computed labels under the caller's native finite-type
instance; no enumeration or data permutation is performed. -/
def liveTable (L : Table ι) (x : EuclideanSpace ℝ ι) : Counted (Table (Live x)) :=
  let t:=restricted L x
  ⟨⟨t.value.labels,t.value.nodup,t.value.complete⟩,t.cost+1⟩
theorem restrictScan_ordered (x : EuclideanSpace ℝ ι) (is : List ι)
    (his : is.Pairwise (·≤·)) : ((restrictScan x is).value).Pairwise (·≤·) := by
  induction is with
  | nil => simp [restrictScan]
  | cons i is ih =>
    rcases List.pairwise_cons.mp his with ⟨hhead,htail⟩
    simp only [restrictScan]
    split_ifs
    · exact ih htail
    · apply List.pairwise_cons.mpr
      constructor
      · intro j hj
        have hm : j.val∈(restrictScan x is).value.map Subtype.val := List.mem_map.mpr ⟨j,hj,rfl⟩
        rw [restrictScan_value] at hm
        exact hhead j.val (List.mem_of_mem_filter hm)
      · exact ih htail
theorem liveTable_ordered (L : Table ι) (hL : Ordered L) (x : EuclideanSpace ℝ ι) :
    Ordered (liveTable L x).value := by
  change ((restrictScan x L.labels).value).Pairwise (·≤·)
  exact restrictScan_ordered x L.labels hL

theorem liveTable_cost (L : Table ι) (x : EuclideanSpace ℝ ι) :
    (liveTable L x).cost=10*Fintype.card ι+4 := by
  simp [liveTable,restricted_cost]

/-- Stored data fields are populated from the computed arrays. -/
def withData {κ : Type*} [Fintype κ] (c : EpochConfig κ (Fin d))
    (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) (A : κ→Matrix (Fin d) (Fin d) ℂ)
    (x : EuclideanSpace ℝ κ) (hH : H=c.offset) (hA : A=c.matrices) (hx : x=c.start) :
    EpochConfig κ (Fin d) where
  matrices:=A
  hermitian:=by rw [hA]; exact c.hermitian
  contractions:=by rw [hA]; exact c.contractions
  offset:=H
  start:=x
  epsilon:=c.epsilon
  epsilon_pos:=c.epsilon_pos
  epsilon_small:=c.epsilon_small
  start_regular:=by rw [hx]; exact c.start_regular
  start_unfrozen:=by rw [hx]; exact c.start_unfrozen
  count_large:=c.count_large

theorem withData_value {κ : Type*} [Fintype κ] (c : EpochConfig κ (Fin d))
    (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) (A : κ→Matrix (Fin d) (Fin d) ℂ)
    (x : EuclideanSpace ℝ κ) (hH : H=c.offset) (hA : A=c.matrices) (hx : x=c.start) :
    withData c H A x hH hA hx=c := by
  subst H A x
  cases c
  rfl

variable (L : Table ι) (hL : Ordered L)
  (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) (A : ι→Matrix (Fin d) (Fin d) ℂ)
  (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1)
  (ε : ℝ) (hε : 0<ε) (hsmall : (Fintype.card ι:ℝ)*ε≤1/1000) (hd : 0<d)

def configWork (x : EuclideanSpace ℝ ι) : ℕ :=
  (liveTable L x).cost+(MSRestriction.offset L H A hA x).cost+(MSRestriction.point L x).cost+
    (MSRestriction.family L A x).cost+
    (MSLabelTransport.family (liveTable L x).value (MSRestriction.family L A x).value).cost+
    (MSLabelTransport.point (liveTable L x).value (MSRestriction.point L x).value).cost+20

def config (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) :
    Counted (EpochConfig (Fin (Fintype.card (Live x.val))) (Fin d)) :=
  let t:=liveTable L x.val
  let o:=MSRestriction.offset L H A hA x.val
  let p:=MSRestriction.point L x.val
  let f:=MSRestriction.family L A x.val
  let a:=MSLabelTransport.family t.value f.value
  let q:=MSLabelTransport.point t.value p.value
  let c:=MSCountedEpochFactory.configuration H A hA hN ε hε hsmall x hl
  let ho : o.value=c.offset := MSRestriction.offset_value L H A hA x.val
  let ha : a.value=c.matrices := by
    dsimp only [a]
    rw [MSLabelTransport.family_value t.value (liveTable_ordered L hL x.val),MSRestriction.family_value]
    rfl
  let hq : q.value=c.start := by
    dsimp only [q]
    rw [MSLabelTransport.point_value t.value (liveTable_ordered L hL x.val),MSRestriction.point_value]
    rfl
  ⟨withData c o.value a.value q.value ho ha hq,configWork L H A hA x.val⟩

attribute [local irreducible] config

theorem config_value (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) :
    (config L hL H A hA hN ε hε hsmall x hl).value=
      MSCountedEpochFactory.configuration H A hA hN ε hε hsmall x hl := by
  unfold config
  apply withData_value
  · exact MSRestriction.offset_value L H A hA x.val
  · rw [MSLabelTransport.family_value _ (liveTable_ordered L hL x.val),MSRestriction.family_value]
    rfl
  · rw [MSLabelTransport.point_value _ (liveTable_ordered L hL x.val),MSRestriction.point_value]
    rfl

def configCost (N d : ℕ) : ℕ := 1000*(N+1)^2*(d+1)^2

theorem config_cost_eq (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) :
    (config L hL H A hA hN ε hε hsmall x hl).cost=configWork L H A hA x.val := by
  unfold config
  rfl

private theorem config_arithmetic (N d : ℕ) :
    (10*N+4)+(30*(N+1)*(d+1)^2+1)+(12*N+4)+14*(N+1)*(d+1)^2+
      (N*d*d*(3*N+6)+1)+(N*(3*N+4)+1)+20≤configCost N d := by
  unfold configCost
  nlinarith [sq_nonneg (N*d),Nat.zero_le (N*d*d),Nat.zero_le (N*N*d)]

theorem config_cost (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) :
    (config L hL H A hA hN ε hε hsmall x hl).cost≤configCost (Fintype.card ι) d := by
  let N:=Fintype.card ι
  have hk : Fintype.card (Live x.val)≤N := Fintype.card_subtype_le _
  have ho:=MSRestriction.offset_cost L H A hA x.val
  have hp:=MSRestriction.point_cost L x.val
  have hf:=MSRestriction.family_cost L A x.val
  have ha : (MSLabelTransport.family (liveTable L x.val).value (MSRestriction.family L A x.val).value).cost≤
      N*d*d*(3*N+6)+1 := by
    rw [MSLabelTransport.family_cost]
    gcongr
  have hq : (MSLabelTransport.point (liveTable L x.val).value (MSRestriction.point L x.val).value).cost≤
      N*(3*N+4)+1 := by
    rw [MSLabelTransport.point_cost]
    gcongr
  have hb : configWork L H A hA x.val≤
      (10*N+4)+(30*(N+1)*(d+1)^2+1)+(12*N+4)+14*(N+1)*(d+1)^2+
      (N*d*d*(3*N+6)+1)+(N*(3*N+4)+1)+20 := by
    unfold configWork
    rw [liveTable_cost]
    dsimp only [N] at *
    omega
  rw [config_cost_eq]
  exact hb.trans (config_arithmetic N d)


def lift (L : Table ι) (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    Counted (EuclideanSpace ℝ ι) :=
  ⟨WithLp.toLp 2 (fun i => if h : x i=1 ∨ x i = -1 then x i
    else y ⟨i,by simpa only [mem_frozenCoordinates,IsSign] using h⟩),10*L.labels.length+1⟩
theorem lift_value (L : Table ι) (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    (lift L x y).value=liftPoint x y := by
  ext i
  simp only [lift,liftPoint,mem_frozenCoordinates,IsSign]
theorem lift_cost (L : Table ι) (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    (lift L x y).cost=10*Fintype.card ι+1 := by simp [lift,table_length]

def restore (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val))
    (s : MSCountedEpochFactory.Certificate H A hA hN ε hε hsmall hd x hl) :
    Counted (Point (ι:=ι) ε×ℝ) :=
  let t:=liveTable L x.val
  let p:=MSLabelTransport.restore t.value s.val.point
  let r:=lift L x.val p.value
  ⟨(⟨r.value,by
    rw [lift_value,MSLabelTransport.restore_value t.value (liveTable_ordered L hL x.val)]
    exact liftPoint_regular x.property
      (MSManuscriptCoefficientReindex.point_regular _ s.property.1.regular)⟩,s.val.time),
    t.cost+p.cost+r.cost+3⟩

theorem restore_value (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val))
    (s : MSCountedEpochFactory.Certificate H A hA hN ε hε hsmall hd x hl) :
    (restore L hL H A hA hN ε hε hsmall hd x hl s).value=
      MSCountedEpochFactory.outputValue H A hA hN ε hε hsmall hd x hl s := by
  apply Prod.ext
  · apply Subtype.ext
    change (lift L x.val (MSLabelTransport.restore (liveTable L x.val).value s.val.point).value).value=_
    rw [lift_value,MSLabelTransport.restore_value _ (liveTable_ordered L hL x.val)]
    rfl
  · rfl

theorem restore_cost (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val))
    (s : MSCountedEpochFactory.Certificate H A hA hN ε hε hsmall hd x hl) :
    (restore L hL H A hA hN ε hε hsmall hd x hl s).cost≤30*(Fintype.card ι+1)^2+3 := by
  have hk : Fintype.card (Live x.val)≤Fintype.card ι := Fintype.card_subtype_le _
  have hsq:=Nat.mul_self_le_mul_self hk
  simp only [restore,liveTable_cost,MSLabelTransport.restore_cost,lift_cost]
  nlinarith

def routines (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) :
    MSCountedEpochFactory.Routines H A hA hN ε hε hsmall hd x hl where
  config:=config L hL H A hA hN ε hε hsmall x hl
  config_value:=config_value L hL H A hA hN ε hε hsmall x hl
  restore:=restore L hL H A hA hN ε hε hsmall hd x hl
  restore_value:=restore_value L hL H A hA hN ε hε hsmall hd x hl

end MatrixSpencer.RealRAM.MSEpochFactorySetup
