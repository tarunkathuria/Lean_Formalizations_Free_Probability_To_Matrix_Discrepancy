import MatrixSpencer.KSCanonicalSDPIndex
import MatrixSpencer.RealRAMSDPIndexComparisons
import Mathlib.Data.List.Sort
import Mathlib.Data.List.ProdSigma

/-! Uniform construction of the SDP's finite address tables. Every source
list is built from `List.finRange`, tagged concatenation, and one decidable
omission; insertion sort is supplied with an explicit operation count. -/
namespace MatrixSpencer.RealRAM.SDPIndexTables
open JacobiIteration (Counted)
open KSFullManuscriptSDPCoordinates KSFullManuscriptSDPBlockPencil
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

local instance {α β : Type*} [LinearOrder α] [LinearOrder β] : LinearOrder (α ⊕ β) := KSCanonicalSDPIndex.sumOrder
local instance {α β : Type*} [LinearOrder α] [LinearOrder β] : LinearOrder (α × β) := KSCanonicalSDPIndex.pairOrder

/-- Concatenation after tagging is the literal enumeration of a sum. -/
def sumList {α β : Type*} (l : List α) (r : List β) : List (α ⊕ β) :=
  l.map Sum.inl ++ r.map Sum.inr

@[simp] theorem sumList_length {α β : Type*} (l : List α) (r : List β) :
    (sumList l r).length=l.length+r.length := by simp [sumList]

@[simp] theorem sumList_mem_left {α β : Type*} (l : List α) (r : List β) (a : α) :
    Sum.inl a ∈ sumList l r ↔ a ∈ l := by simp [sumList]
@[simp] theorem sumList_mem_right {α β : Type*} (l : List α) (r : List β) (b : β) :
    Sum.inr b ∈ sumList l r ↔ b ∈ r := by simp [sumList]

theorem sumList_nodup {α β : Type*} {l : List α} {r : List β}
    (hl : l.Nodup) (hr : r.Nodup) : (sumList l r).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨hl.map Sum.inl_injective,hr.map Sum.inr_injective,?_⟩
  intro x hx y hy hxy
  rcases List.mem_map.mp hx with ⟨a,ha,rfl⟩
  rcases List.mem_map.mp hy with ⟨b,hb,rfl⟩
  cases hxy

def pairs (d : ℕ) : List (Fin d × Fin d) :=
  (List.finRange d).product (List.finRange d)

@[simp] theorem pairs_mem {d : ℕ} (p : Fin d × Fin d) : p ∈ pairs d := by
  rcases p with ⟨i,j⟩
  exact List.mem_product.mpr ⟨List.mem_finRange i,List.mem_finRange j⟩
@[simp] theorem pairs_length (d : ℕ) : (pairs d).length=d*d := by
  exact (List.length_product (List.finRange d) (List.finRange d)).trans (by simp)
theorem pairs_nodup (d : ℕ) : (pairs d).Nodup :=
  (List.nodup_finRange d).product (List.nodup_finRange d)

def omitted {d : ℕ} (a : Fin d) : List (KSFullManuscriptTraceCoordinates.Index a) :=
  (pairs d).filterMap (fun p => if h : p≠(a,a) then some ⟨p,h⟩ else none)

theorem omitted_mem {d : ℕ} (a : Fin d) (p : KSFullManuscriptTraceCoordinates.Index a) :
    p ∈ omitted a := by
  apply List.mem_filterMap.mpr
  exact ⟨p.val,pairs_mem p.val,by simp [p.property]⟩

theorem omitted_nodup {d : ℕ} (a : Fin d) : (omitted a).Nodup := by
  apply List.Nodup.of_map (f:=Subtype.val)
  have he : (omitted a).map Subtype.val=(pairs d).filter (fun p=>decide (p≠(a,a))) := by
    unfold omitted
    generalize pairs d=l
    induction l with
    | nil => rfl
    | cons p l ih =>
      by_cases h:p≠(a,a)
      · simp only [List.filterMap_cons,dif_pos h,List.map_cons,ih,List.filter_cons,
          decide_eq_true h,ite_true]
      · simp only [List.filterMap_cons,dif_neg h,List.map_cons,ih,List.filter_cons,
          decide_eq_false h,Bool.false_eq_true,ite_false]
  rw [he]
  exact (pairs_nodup d).filter _

theorem omitted_length_le {d : ℕ} (a : Fin d) : (omitted a).length≤d*d :=
  (List.length_filterMap_le _ _).trans_eq (pairs_length d)

def chartRaw {d : ℕ} (a : Fin d) : List (Index a) :=
  sumList (sumList (omitted a) (pairs d)) (sumList (pairs d) (pairs d))

theorem chartRaw_mem {d : ℕ} (a : Fin d) (p : Index a) : p ∈ chartRaw a := by
  rcases p with (p|p)|(p|p) <;> simp [chartRaw,omitted_mem]
theorem chartRaw_nodup {d : ℕ} (a : Fin d) : (chartRaw a).Nodup :=
  sumList_nodup (sumList_nodup (omitted_nodup a) (pairs_nodup d))
    (sumList_nodup (pairs_nodup d) (pairs_nodup d))
theorem chartRaw_length_le {d : ℕ} (a : Fin d) : (chartRaw a).length≤4*d^2 := by
  have h:=omitted_length_le a
  simp only [chartRaw,sumList_length,pairs_length]
  nlinarith

def complexRowsRaw (d : ℕ) : List (ComplexIndex (Fin d)) :=
  sumList (List.finRange d)
    (sumList (sumList (List.finRange d) (List.finRange d))
      (sumList (List.finRange d) (List.finRange d)))
def rowsRaw (d : ℕ) : List (RealIndex (Fin d)) :=
  sumList (complexRowsRaw d) (complexRowsRaw d)

theorem complexRowsRaw_mem {d : ℕ} (p : ComplexIndex (Fin d)) : p ∈ complexRowsRaw d := by
  rcases p with p|((p|p)|(p|p)) <;> simp [complexRowsRaw,List.mem_finRange]
theorem rowsRaw_mem {d : ℕ} (p : RealIndex (Fin d)) : p ∈ rowsRaw d := by
  cases p <;> simp [rowsRaw,complexRowsRaw_mem]
theorem complexRowsRaw_nodup (d : ℕ) : (complexRowsRaw d).Nodup :=
  sumList_nodup (List.nodup_finRange d)
    (sumList_nodup (sumList_nodup (List.nodup_finRange d) (List.nodup_finRange d))
      (sumList_nodup (List.nodup_finRange d) (List.nodup_finRange d)))
theorem rowsRaw_nodup (d : ℕ) : (rowsRaw d).Nodup :=
  sumList_nodup (complexRowsRaw_nodup d) (complexRowsRaw_nodup d)
theorem rowsRaw_length (d : ℕ) : (rowsRaw d).length=10*d := by
  simp [rowsRaw,complexRowsRaw];omega

/-- One lexicographic index comparison and its list/control work are charged
at most sixteen elementary address operations. -/
def insert {α : Type*} [LinearOrder α] (a : α) : List α → Counted (List α)
  | [] => ⟨[a],1⟩
  | b::l => if a≤b then ⟨a::b::l,16⟩ else
      let q:=insert a l
      ⟨b::q.value,q.cost+16⟩

def sort {α : Type*} [LinearOrder α] : List α → Counted (List α)
  | [] => ⟨[],1⟩
  | a::l =>
      let q:=sort l
      let p:=insert a q.value
      ⟨p.value,q.cost+p.cost+2⟩

theorem insert_value {α : Type*} [LinearOrder α] (a : α) (l : List α) :
    (insert a l).value=List.orderedInsert (·≤·) a l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases h:a≤b <;> simp [insert,List.orderedInsert,h,ih]

theorem insert_cost {α : Type*} [LinearOrder α] (a : α) (l : List α) :
    (insert a l).cost≤16*l.length+1 := by
  induction l with
  | nil => simp [insert]
  | cons b l ih =>
    by_cases h:a≤b <;> simp [insert,h] <;> omega

theorem sort_value {α : Type*} [LinearOrder α] (l : List α) :
    (sort l).value=List.insertionSort (·≤·) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [sort,insert_value,ih,List.insertionSort]

theorem sort_cost {α : Type*} [LinearOrder α] (l : List α) :
    (sort l).cost≤20*(l.length+1)^2 := by
  induction l with
  | nil => simp [sort]
  | cons a l ih =>
    have hi:=insert_cost a (sort l).value
    have hlen : (sort l).value.length=l.length := by rw [sort_value,List.length_insertionSort]
    rw [hlen] at hi
    simp only [sort,List.length_cons]
    nlinarith

def orderedTable (α : Type*) [Fintype α] [LinearOrder α] : List α :=
  Finset.univ.sort (·≤·)

theorem sort_eq_univ {α : Type*} [Fintype α] [LinearOrder α] (l : List α)
    (hn : l.Nodup) (hm : ∀a,a∈l) :
    (sort l).value=orderedTable α := by
  unfold orderedTable
  rw [sort_value]
  apply List.eq_of_perm_of_sorted (r:=fun x y : α=>x≤y)
  · apply (List.perm_insertionSort _ _).trans
    apply List.perm_ext_iff_of_nodup hn (Finset.sort_nodup _ _)|>.mpr
    intro a
    simp [hm a]
  · exact List.sorted_insertionSort _ _
  · exact Finset.sort_sorted _ _

/-- Sorting consumes the computed comparison answer and its actual cost. -/
def insertWith {α : Type*} (cmp : α→α→Counted Bool) (a : α) : List α → Counted (List α)
  | [] => ⟨[a],1⟩
  | b::l =>
    let c:=cmp a b
    if c.value then ⟨a::b::l,c.cost+2⟩ else
      let q:=insertWith cmp a l
      ⟨b::q.value,q.cost+c.cost+2⟩

def sortWith {α : Type*} (cmp : α→α→Counted Bool) : List α → Counted (List α)
  | [] => ⟨[],1⟩
  | a::l =>
    let q:=sortWith cmp l
    let p:=insertWith cmp a q.value
    ⟨p.value,q.cost+p.cost+2⟩

theorem insertWith_value {α : Type*} [LinearOrder α] (cmp : α→α→Counted Bool)
    (hc : ∀a b,(cmp a b).value=decide (a≤b)) (a : α) (l : List α) :
    (insertWith cmp a l).value=List.orderedInsert (·≤·) a l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases h:a≤b <;> simp [insertWith,List.orderedInsert,h,hc,ih]

theorem insertWith_cost {α : Type*} (cmp : α→α→Counted Bool) {C : ℕ}
    (hc : ∀a b,(cmp a b).cost≤C) (a : α) (l : List α) :
    (insertWith cmp a l).cost≤(C+2)*l.length+1 := by
  induction l with
  | nil => simp [insertWith]
  | cons b l ih =>
    have h:=hc a b
    simp only [insertWith,List.length_cons]
    split <;> simp only [] <;> nlinarith

theorem sortWith_value {α : Type*} [LinearOrder α] (cmp : α→α→Counted Bool)
    (hc : ∀a b,(cmp a b).value=decide (a≤b)) (l : List α) :
    (sortWith cmp l).value=List.insertionSort (·≤·) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [sortWith,insertWith_value cmp hc,ih,List.insertionSort]

theorem sortWith_cost {α : Type*} [LinearOrder α] (cmp : α→α→Counted Bool) {C : ℕ}
    (hv : ∀a b,(cmp a b).value=decide (a≤b)) (hc : ∀a b,(cmp a b).cost≤C) (l : List α) :
    (sortWith cmp l).cost≤(C+4)*(l.length+1)^2 := by
  induction l with
  | nil => simp [sortWith]
  | cons a l ih =>
    have hi:=insertWith_cost cmp hc a (sortWith cmp l).value
    have hlen : (sortWith cmp l).value.length=l.length := by
      rw [sortWith_value cmp hv,List.length_insertionSort]
    rw [hlen] at hi
    simp only [sortWith,List.length_cons]
    nlinarith

/-- A reverse lookup evaluates equality by both ordered comparisons. -/
def lookupWith {α : Type*} (cmp : α→α→Counted Bool) (p : α) : List α → Counted ℕ
  | [] => ⟨0,1⟩
  | a::l =>
    let c:=cmp p a
    let e:=cmp a p
    if c.value && e.value then ⟨0,c.cost+e.cost+3⟩ else
      let q:=lookupWith cmp p l
      ⟨q.value+1,q.cost+c.cost+e.cost+3⟩

theorem lookupWith_value {α : Type*} [LinearOrder α] (cmp : α→α→Counted Bool)
    (hc : ∀a b,(cmp a b).value=decide (a≤b)) (p : α) (l : List α) :
    (lookupWith cmp p l).value=l.idxOf p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hiff : p≤a ∧ a≤p ↔ p=a := le_antisymm_iff.symm
    simp only [lookupWith,hc,Bool.and_eq_true,decide_eq_true_eq,List.idxOf_cons,
      Bool.cond_eq_ite,beq_iff_eq,ih]
    by_cases h:p=a
    · simp [h]
    · simp [h,hiff,Ne.symm h]

theorem lookupWith_cost {α : Type*} (cmp : α→α→Counted Bool) {C : ℕ}
    (hc : ∀a b,(cmp a b).cost≤C) (p : α) (l : List α) :
    (lookupWith cmp p l).cost≤(2*C+3)*l.length+1 := by
  induction l with
  | nil => simp [lookupWith]
  | cons a l ih =>
    have h:=hc p a
    have h':=hc a p
    simp only [lookupWith,List.length_cons]
    split <;> simp only [] <;> nlinarith

/-- A forward address is read by a literal bounded list traversal. -/
def readAt {α : Type*} : (l : List α) → Fin l.length → Counted α
  | [],i => Fin.elim0 i
  | a::l,i => if h:i.val=0 then ⟨a,2⟩ else
      let q:=readAt l ⟨i.val-1,by have:=i.isLt;simp only [List.length_cons] at this;omega⟩
      ⟨q.value,q.cost+2⟩

theorem readAt_value {α : Type*} (l : List α) (i : Fin l.length) :
    (readAt l i).value=l.get i := by
  induction l with
  | nil => exact Fin.elim0 i
  | cons a l ih =>
    rcases i with ⟨i,hi⟩
    cases i with
    | zero => rfl
    | succ k =>
      simp only [readAt,Fin.val_mk,Nat.succ_ne_zero,dif_neg,Nat.succ_sub_one,ih]
      rfl

theorem readAt_cost {α : Type*} (l : List α) (i : Fin l.length) :
    (readAt l i).cost≤2*l.length+1 := by
  induction l with
  | nil => exact Fin.elim0 i
  | cons a l ih =>
    simp only [readAt,List.length_cons]
    split
    · simp;omega
    · have hh:=ih ⟨i.val-1,by have:=i.isLt;simp only [List.length_cons] at this;omega⟩
      simp only []
      omega

/-- Both sorted lists are generated from explicit bounded loops. The raw
chart builds four pair blocks and omits one entry; the row list tags ten
finite ranges. The displayed extra costs include those list operations. -/
def chartTable {d : ℕ} (a : Fin d) : Counted (List (Index a)) :=
  let q:=sortWith (SDPIndexComparisons.chartLe a) (chartRaw a)
  ⟨q.value,q.cost+30*(d+1)^2⟩
def rowTable (d : ℕ) : Counted (List (RealIndex (Fin d))) :=
  let q:=sortWith SDPIndexComparisons.rowsLe (rowsRaw d)
  ⟨q.value,q.cost+50*(d+1)⟩

theorem chartTable_value {d : ℕ} (a : Fin d) :
    (chartTable a).value=orderedTable (Index a) := by
  change (sortWith _ _).value=_
  rw [sortWith_value _ (SDPIndexComparisons.chartLe_value a),←sort_value]
  exact sort_eq_univ _ (chartRaw_nodup a) (chartRaw_mem a)
theorem rowTable_value (d : ℕ) :
    (rowTable d).value=orderedTable (RealIndex (Fin d)) := by
  change (sortWith _ _).value=_
  rw [sortWith_value _ SDPIndexComparisons.rowsLe_value,←sort_value]
  exact sort_eq_univ _ (rowsRaw_nodup d) rowsRaw_mem

theorem chartTable_length {d : ℕ} (a : Fin d) :
    (chartTable a).value.length=Fintype.card (Index a) := by
  rw [chartTable_value,orderedTable,Finset.length_sort];rfl

theorem rowTable_length (d : ℕ) :
    (rowTable d).value.length=Fintype.card (RealIndex (Fin d)) := by
  rw [rowTable_value,orderedTable,Finset.length_sort];rfl

theorem chartTable_length_raw {d : ℕ} (a : Fin d) :
    (chartTable a).value.length=(chartRaw a).length := by
  change (sortWith _ _).value.length=_
  rw [sortWith_value _ (SDPIndexComparisons.chartLe_value a),List.length_insertionSort]

theorem rowTable_length_raw (d : ℕ) : (rowTable d).value.length=(rowsRaw d).length := by
  change (sortWith _ _).value.length=_
  rw [sortWith_value _ SDPIndexComparisons.rowsLe_value,List.length_insertionSort]

/-- The entire inverse-address array is materialized, with every individual
scan and store included. Its entries consume the computed sorted table. -/
def chartLookup {d : ℕ} (a : Fin d) : Counted (Index a → ℕ) :=
  let q:=chartTable a
  ⟨fun p=>(lookupWith (SDPIndexComparisons.chartLe a) p q.value).value,
    q.cost+((chartRaw a).map (fun p=>(lookupWith (SDPIndexComparisons.chartLe a) p q.value).cost+1)).sum+1⟩

/-- The row-address array is materialized by reading every finite address
from the computed row list. No canonical equivalence is evaluated here. -/
def rowLookup (d : ℕ) : Counted (Fin (Fintype.card (RealIndex (Fin d))) → RealIndex (Fin d)) :=
  let q:=rowTable d
  ⟨fun i=>(readAt q.value ⟨i.val,by rw [rowTable_length];exact i.isLt⟩).value,
    q.cost+((List.finRange q.value.length).map (fun i=>(readAt q.value i).cost+1)).sum+1⟩

def chartAddress {d : ℕ} (a : Fin d) (p : Index a) : ℕ :=
  (chartLookup a).value p

def rowAddress {d : ℕ} (i : Fin (Fintype.card (RealIndex (Fin d)))) : RealIndex (Fin d) :=
  (rowLookup d).value i

theorem chartAddress_eq {d : ℕ} (a : Fin d) (p : Index a) :
    chartAddress a p=(KSCanonicalSDPIndex.chart a p).val := by
  change (lookupWith _ _ _).value=_
  rw [lookupWith_value _ (SDPIndexComparisons.chartLe_value a),chartTable_value]
  exact (KSCanonicalSDPIndex.orderedEquiv_val (Index a) p).symm

theorem rowAddress_eq {d : ℕ} (i : Fin (Fintype.card (RealIndex (Fin d)))) :
    rowAddress i=(KSCanonicalSDPIndex.rows (Fin d)).symm i := by
  change (readAt _ _).value=_
  rw [readAt_value]
  have hh:=KSCanonicalSDPIndex.orderedEquiv_symm (RealIndex (Fin d)) i
  symm
  simpa only [KSCanonicalSDPIndex.rows,List.get_eq_getElem,rowTable_value,orderedTable] using hh

theorem map_sum_le {α : Type*} (l : List α) (f : α→ℕ) (b : ℕ)
    (hb : ∀p∈l,f p≤b) : (l.map f).sum≤l.length*b := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp:=hb p (by simp)
    have hh:=ih (by intro q hq;exact hb q (by simp [hq]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

theorem chartLookup_cost {d : ℕ} (a : Fin d) :
    (chartLookup a).cost≤60*(4*d^2+1)^2+30*(d+1)^2+1 := by
  have hs:=sortWith_cost _ (SDPIndexComparisons.chartLe_value a)
    (SDPIndexComparisons.chartLe_cost a) (chartRaw a)
  have hl:=chartRaw_length_le a
  have hsum:=map_sum_le (chartRaw a)
    (fun p=>(lookupWith (SDPIndexComparisons.chartLe a) p (chartTable a).value).cost+1)
    (35*(chartRaw a).length+2) (by
      intro p hp
      have hh:=lookupWith_cost _ (SDPIndexComparisons.chartLe_cost a) p (chartTable a).value
      rw [chartTable_length_raw] at hh
      dsimp only
      omega)
  have hsq : ((chartRaw a).length+1)^2≤(4*d^2+1)^2 := by gcongr
  change (sortWith _ _).cost+30*(d+1)^2+_+1≤_
  norm_num only at hs
  nlinarith

theorem rowLookup_cost (d : ℕ) :
    (rowLookup d).cost≤25*(10*d+1)^2+50*(d+1)+1 := by
  have hs:=sortWith_cost _ (SDPIndexComparisons.rowsLe_value (d:=d))
    (SDPIndexComparisons.rowsLe_cost (d:=d)) (rowsRaw d)
  have hlen : (rowTable d).value.length=10*d := by rw [rowTable_length_raw,rowsRaw_length]
  have hsum:=map_sum_le (List.finRange (rowTable d).value.length)
    (fun i=>(readAt (rowTable d).value i).cost+1) (2*(rowTable d).value.length+2)
    (by intro i hi;have hh:=readAt_cost (rowTable d).value i;dsimp only;omega)
  simp only [List.length_finRange,hlen] at hsum
  rw [rowsRaw_length] at hs
  change (sortWith _ _).cost+50*(d+1)+_+1≤_
  norm_num only at hs
  nlinarith

/-- This allowance covers generation, concrete comparison sorting, every
reverse lookup and forward traversal, and all table stores. -/
theorem routing_cost {d : ℕ} (a : Fin d) :
    (chartLookup a).cost+(rowLookup d).cost≤9000*(d+1)^4 := by
  apply (Nat.add_le_add (chartLookup_cost a) (rowLookup_cost d)).trans
  ring_nf
  omega

end MatrixSpencer.RealRAM.SDPIndexTables

