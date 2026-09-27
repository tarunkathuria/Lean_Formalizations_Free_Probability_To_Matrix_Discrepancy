import MatrixSpencer.KSCanonicalSDPIndex
import MatrixSpencer.RealRAMJacobiIteration

/-! Concrete comparisons for the materialized SDP address tables.
Indices consist only of binary tags and natural addresses. A scalar
comparison loads its two addresses, compares them, and stores its Boolean
result (four operations). A pair comparison uses four loads, three scalar
comparisons, two Boolean operations, and one result store; twelve is an
upper allowance. A sum node reads its two tags before choosing a branch.
No comparison of an arbitrary finite type is used by these routines. -/
namespace MatrixSpencer.RealRAM.SDPIndexComparisons
open JacobiIteration (Counted)
open KSFullManuscriptSDPCoordinates KSFullManuscriptSDPBlockPencil

local instance {α β : Type*} [LinearOrder α] [LinearOrder β] : LinearOrder (α ⊕ β) :=
  KSCanonicalSDPIndex.sumOrder
local instance {α β : Type*} [LinearOrder α] [LinearOrder β] : LinearOrder (α × β) :=
  KSCanonicalSDPIndex.pairOrder
local instance {α β : Type*} [LinearOrder α] [LinearOrder β] : LE (α ⊕ β) :=
  (KSCanonicalSDPIndex.sumOrder (α:=α) (β:=β)).toLE
local instance {α β : Type*} [LinearOrder α] [LinearOrder β] : LT (α ⊕ β) :=
  (KSCanonicalSDPIndex.sumOrder (α:=α) (β:=β)).toLT
local instance {α β : Type*} [LinearOrder α] [LinearOrder β] : LE (α × β) :=
  (KSCanonicalSDPIndex.pairOrder (α:=α) (β:=β)).toLE
local instance {α β : Type*} [LinearOrder α] [LinearOrder β] : LT (α × β) :=
  (KSCanonicalSDPIndex.pairOrder (α:=α) (β:=β)).toLT

def finLe {d : ℕ} (p q : Fin d) : Counted Bool :=
  ⟨decide (p.val≤q.val),4⟩

theorem finLe_value {d : ℕ} (p q : Fin d) :
    (finLe p q).value=decide (p≤q) := rfl

def pairLe {d : ℕ} (p q : Fin d × Fin d) : Counted Bool :=
  ⟨decide (p.1.val<q.1.val) ||
    (decide (p.1.val=q.1.val) && decide (p.2.val≤q.2.val)),12⟩

theorem pairLe_value {d : ℕ} (p q : Fin d × Fin d) :
    (pairLe p q).value=decide (p≤q) := by
  change (decide (p.1.val<q.1.val) ||
    (decide (p.1.val=q.1.val) && decide (p.2.val≤q.2.val)))=
      decide (Prod.Lex (·<·) (·≤·) p q)
  simp only [Prod.lex_def,Bool.decide_or,Bool.decide_and,Fin.ext_iff]
  rfl

/-- Branch only on the two explicit tags and then call the selected
component routine. Each branch includes the two tag inspections. -/
def sumLe {α β : Type*} (f : α → α → Counted Bool) (g : β → β → Counted Bool) :
    α ⊕ β → α ⊕ β → Counted Bool
  | .inl p,.inl q => let c:=f p q; ⟨c.value,c.cost+2⟩
  | .inl _,.inr _ => ⟨true,2⟩
  | .inr _,.inl _ => ⟨false,2⟩
  | .inr p,.inr q => let c:=g p q; ⟨c.value,c.cost+2⟩

theorem sumLe_value {α β : Type*} [LinearOrder α] [LinearOrder β]
    (f : α → α → Counted Bool) (g : β → β → Counted Bool)
    (hf : ∀ p q,(f p q).value=decide (p≤q))
    (hg : ∀ p q,(g p q).value=decide (p≤q)) (p q : α ⊕ β) :
    (sumLe f g p q).value=decide (p≤q) := by
  change (sumLe f g p q).value=decide (Sum.Lex (·≤·) (·≤·) p q)
  cases p <;> cases q <;>
    simp [sumLe,hf,hg,Sum.lex_inl_inl,Sum.lex_inr_inr,Sum.Lex.sep,Sum.lex_inr_inl]

theorem sumLe_cost {α β : Type*} (f : α → α → Counted Bool)
    (g : β → β → Counted Bool) (b : ℕ)
    (hf : ∀ p q,(f p q).cost≤b) (hg : ∀ p q,(g p q).cost≤b)
    (p q : α ⊕ β) : (sumLe f g p q).cost≤b+2 := by
  cases p <;> cases q <;> simp only [sumLe]
  · exact Nat.add_le_add_right (hf _ _) 2
  · omega
  · omega
  · exact Nat.add_le_add_right (hg _ _) 2

def chartLe {d : ℕ} (a : Fin d) : Index a → Index a → Counted Bool :=
  sumLe (sumLe (fun p q=>pairLe p.val q.val) pairLe) (sumLe pairLe pairLe)

theorem chartLe_value {d : ℕ} (a : Fin d) (p q : Index a) :
    (chartLe a p q).value=decide (p≤q) := by
  apply sumLe_value
  · apply sumLe_value
    · intro p q; exact pairLe_value p.val q.val
    · exact pairLe_value
  · exact sumLe_value pairLe pairLe pairLe_value pairLe_value

theorem chartLe_cost {d : ℕ} (a : Fin d) (p q : Index a) :
    (chartLe a p q).cost≤16 := by
  apply sumLe_cost _ _ 14
  · intro p q
    exact sumLe_cost _ _ 12 (fun _ _=>le_rfl) (fun _ _=>le_rfl) p q
  · intro p q
    exact sumLe_cost _ _ 12 (fun _ _=>le_rfl) (fun _ _=>le_rfl) p q

def complexRowsLe {d : ℕ} : ComplexIndex (Fin d) → ComplexIndex (Fin d) → Counted Bool :=
  sumLe finLe (sumLe (sumLe finLe finLe) (sumLe finLe finLe))

theorem complexRowsLe_value {d : ℕ} (p q : ComplexIndex (Fin d)) :
    (complexRowsLe p q).value=decide (p≤q) := by
  apply sumLe_value _ _ finLe_value
  exact sumLe_value _ _ (sumLe_value _ _ finLe_value finLe_value)
    (sumLe_value _ _ finLe_value finLe_value)

theorem complexRowsLe_cost {d : ℕ} (p q : ComplexIndex (Fin d)) :
    (complexRowsLe p q).cost≤10 := by
  apply sumLe_cost _ _ 8
  · intro p q; norm_num [finLe]
  · intro p q
    apply sumLe_cost _ _ 6
    · exact sumLe_cost _ _ 4 (fun _ _=>le_rfl) (fun _ _=>le_rfl)
    · exact sumLe_cost _ _ 4 (fun _ _=>le_rfl) (fun _ _=>le_rfl)

def rowsLe {d : ℕ} : RealIndex (Fin d) → RealIndex (Fin d) → Counted Bool :=
  sumLe complexRowsLe complexRowsLe

theorem rowsLe_value {d : ℕ} (p q : RealIndex (Fin d)) :
    (rowsLe p q).value=decide (p≤q) :=
  sumLe_value _ _ complexRowsLe_value complexRowsLe_value p q

theorem rowsLe_cost {d : ℕ} (p q : RealIndex (Fin d)) :
    (rowsLe p q).cost≤16 :=
  (sumLe_cost _ _ 10 complexRowsLe_cost complexRowsLe_cost p q).trans (by norm_num)

def equalFromLe {α : Type*} (f : α → α → Counted Bool) (p q : α) : Counted Bool :=
  let left:=f p q
  let right:=f q p
  ⟨left.value && right.value,left.cost+right.cost+1⟩

theorem equalFromLe_value {α : Type*} [LinearOrder α]
    (f : α → α → Counted Bool) (hf : ∀ p q,(f p q).value=decide (p≤q)) (p q : α) :
    (equalFromLe f p q).value=decide (p=q) := by
  simp only [equalFromLe,hf,←Bool.decide_and,←le_antisymm_iff]

theorem equalFromLe_cost {α : Type*} (f : α → α → Counted Bool) (b : ℕ)
    (hf : ∀ p q,(f p q).cost≤b) (p q : α) :
    (equalFromLe f p q).cost≤2*b+1 := by
  have h1:=hf p q
  have h2:=hf q p
  simp only [equalFromLe]
  omega

def chartEq {d : ℕ} (a : Fin d) : Index a → Index a → Counted Bool := equalFromLe (chartLe a)
def rowsEq {d : ℕ} : RealIndex (Fin d) → RealIndex (Fin d) → Counted Bool := equalFromLe rowsLe

theorem chartEq_value {d : ℕ} (a : Fin d) (p q : Index a) :
    (chartEq a p q).value=decide (p=q) :=
  equalFromLe_value _ (chartLe_value a) p q
theorem rowsEq_value {d : ℕ} (p q : RealIndex (Fin d)) :
    (rowsEq p q).value=decide (p=q) :=
  equalFromLe_value _ rowsLe_value p q
theorem chartEq_cost {d : ℕ} (a : Fin d) (p q : Index a) :
    (chartEq a p q).cost≤33 := equalFromLe_cost _ 16 (chartLe_cost a) p q
theorem rowsEq_cost {d : ℕ} (p q : RealIndex (Fin d)) :
    (rowsEq p q).cost≤33 := equalFromLe_cost _ 16 rowsLe_cost p q

end MatrixSpencer.RealRAM.SDPIndexComparisons
