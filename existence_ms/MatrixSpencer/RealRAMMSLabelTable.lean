import MatrixSpencer.RealRAMMSPoint
import MatrixSpencer.MSManuscriptCoefficientReindex

/-! The canonical reindexing is realized by the stored increasing label table.
Restricting an increasing table preserves its order. Forward lookup and inverse
lookup below are literal finite scans, with linear costs; no abstract finite
bijection is supplied as a unit-cost oracle. -/
noncomputable section
namespace MatrixSpencer.RealRAM.MSLabelTable
open JacobiIteration (Counted)
open MSPoint PhaseRestriction
variable {ι : Type*} [Fintype ι] [LinearOrder ι]
attribute [local instance] Classical.propDecidable

def Ordered (L : Table ι) : Prop := L.labels.Pairwise (·≤·)

theorem fin_ordered (N : ℕ) : Ordered (finTable N) := List.pairwise_le_finRange N

theorem labels_eq_sort (L : Table ι) (hL : Ordered L) :
    L.labels=Finset.univ.sort (fun i j : ι => i≤j) := by
  apply List.eq_of_perm_of_sorted (r := (·≤·))
  · apply List.perm_of_nodup_nodup_toFinset_eq L.nodup (Finset.sort_nodup _ _)
    ext i
    simp [L.complete]
  · exact hL
  · exact Finset.sort_sorted _ _

theorem restricted_ordered (L : Table ι) (hL : Ordered L) (x : EuclideanSpace ℝ ι) :
    Ordered (restricted L x).value := by
  have h := hL.filter (fun i => decide (¬IsSign (x i)))
  rw [←restrictScan_value] at h
  simpa only [List.pairwise_map,Ordered,restricted] using h

def lookup : List ι → ℕ → Counted (Option ι)
  | [],_ => ⟨none,1⟩
  | i::_,0 => ⟨some i,3⟩
  | _::is,k+1 => let y := lookup is k; ⟨y.value,y.cost+3⟩

omit [Fintype ι] [LinearOrder ι] in
theorem lookup_value (is : List ι) (k : ℕ) : (lookup is k).value=is[k]? := by
  induction is generalizing k with
  | nil => rfl
  | cons i is ih => cases k <;> simp [lookup,ih]

omit [Fintype ι] [LinearOrder ι] in
theorem lookup_cost (is : List ι) (k : ℕ) : (lookup is k).cost≤3*is.length+1 := by
  induction is generalizing k with
  | nil => simp [lookup]
  | cons i is ih =>
    cases k with
    | zero => simp [lookup]; omega
    | succ k => simp only [lookup,List.length_cons]; have h := ih k; omega

theorem enumeration_lookup (L : Table ι) (hL : Ordered L) (k : Fin (Fintype.card ι)) :
    (lookup L.labels k.val).value=some (MSManuscriptCoefficientReindex.enumeration ι k) := by
  rw [lookup_value,labels_eq_sort L hL]
  rw [List.getElem?_eq_getElem (by simpa using k.isLt)]
  have he := Finset.orderEmbOfFin_unique (s:=Finset.univ) (Finset.card_univ : (Finset.univ : Finset ι).card=Fintype.card ι)
    (f:=MSManuscriptCoefficientReindex.enumeration ι)
    (fun j => Finset.mem_univ _)
    (Fintype.orderIsoFinOfCardEq ι rfl).strictMono
  rw [congrFun he k,Finset.orderEmbOfFin_apply]
  simp only [Fin.getElem_fin]
  congr 2
  congr

def index (i : ι) : List ι → Counted ℕ
  | [] => ⟨0,1⟩
  | j::js => if i=j then ⟨0,4⟩ else let y := index i js; ⟨y.value+1,y.cost+6⟩

theorem index_value (i : ι) (is : List ι) : (index i is).value=is.idxOf i := by
  induction is with
  | nil => rfl
  | cons j js ih =>
    by_cases h : i=j
    · subst j; simp [index]
    · rw [List.idxOf_cons_ne js (Ne.symm h)]
      simp only [index,if_neg h,ih,Nat.succ_eq_add_one]

theorem index_cost (i : ι) (is : List ι) : (index i is).cost≤6*is.length+1 := by
  induction is with
  | nil => simp [index]
  | cons j js ih => simp only [index,List.length_cons]; split_ifs <;> dsimp <;> omega

theorem enumeration_inverse (L : Table ι) (hL : Ordered L) (i : ι) :
    (index i L.labels).value=(MSManuscriptCoefficientReindex.enumeration ι).symm i := by
  let e := MSManuscriptCoefficientReindex.enumeration ι
  have he := enumeration_lookup L hL (e.symm i)
  rw [lookup_value,List.getElem?_eq_getElem (by rw [table_length]; exact (e.symm i).isLt)] at he
  have hb : (e.symm i).val<L.labels.length := by rw [table_length]; exact (e.symm i).isLt
  have hi : L.labels[(e.symm i).val] = i := by
    exact Option.some.inj (he.trans (congrArg some (e.apply_symm_apply i)))
  rw [index_value]
  calc
    L.labels.idxOf i=L.labels.idxOf L.labels[(e.symm i).val] := congrArg (fun a => L.labels.idxOf a) hi.symm
    _ = (e.symm i).val := List.idxOf_getElem L.nodup _ hb

end MatrixSpencer.RealRAM.MSLabelTable
