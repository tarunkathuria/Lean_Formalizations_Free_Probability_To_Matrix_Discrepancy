import MatrixSpencer.KSFullManuscriptSDPCoordinates
import MatrixSpencer.KSFullManuscriptSDPBlockPencil
import Mathlib.Data.Sum.Order
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Sort

/-! Canonical finite addresses for the SDP entry chart and block rows.
The order is explicitly lexicographic at each sum and product. Consequently
these maps are obtained by ordered finite enumeration, not by a choice of a
bijection. The real-arithmetic table implementation is certified separately. -/
namespace MatrixSpencer.KSCanonicalSDPIndex

def sumOrder {α β : Type*} [LinearOrder α] [LinearOrder β] : LinearOrder (α ⊕ β) :=
  Sum.Lex.linearOrder

def pairOrder {α β : Type*} [LinearOrder α] [LinearOrder β] : LinearOrder (α × β) :=
  Prod.Lex.instLinearOrder α β

local instance {α β : Type*} [LinearOrder α] [LinearOrder β] : LinearOrder (α ⊕ β) := sumOrder
local instance {α β : Type*} [LinearOrder α] [LinearOrder β] : LinearOrder (α × β) := pairOrder

def orderedEquiv (α : Type*) [Fintype α] [LinearOrder α] : α ≃ Fin (Fintype.card α) :=
  (Fintype.orderIsoFinOfCardEq α rfl).toEquiv.symm

theorem orderedEquiv_val (α : Type*) [Fintype α] [LinearOrder α] (a : α) :
    (orderedEquiv α a).val=(Finset.univ.sort (·≤·)).idxOf a := by
  unfold orderedEquiv Fintype.orderIsoFinOfCardEq
  exact Finset.orderIsoOfFin_symm_apply Finset.univ rfl ⟨a,Finset.mem_univ a⟩

theorem orderedEquiv_symm (α : Type*) [Fintype α] [LinearOrder α]
    (i : Fin (Fintype.card α)) :
    (orderedEquiv α).symm i=(Finset.univ.sort (·≤·))[i.val]'(by simpa using i.isLt) := by
  exact Finset.orderEmbOfFin_apply Finset.univ rfl i

def chart {n : Type*} [Fintype n] [LinearOrder n] (a : n) :
    KSFullManuscriptSDPCoordinates.Index a ≃
      Fin (Fintype.card (KSFullManuscriptSDPCoordinates.Index a)) :=
  orderedEquiv (KSFullManuscriptSDPCoordinates.Index a)

def rows (n : Type*) [Fintype n] [LinearOrder n] :
    KSFullManuscriptSDPBlockPencil.RealIndex n ≃
      Fin (Fintype.card (KSFullManuscriptSDPBlockPencil.RealIndex n)) :=
  orderedEquiv (KSFullManuscriptSDPBlockPencil.RealIndex n)

end MatrixSpencer.KSCanonicalSDPIndex
