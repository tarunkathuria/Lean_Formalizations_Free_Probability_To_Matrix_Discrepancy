import MatrixSpencer.RealRAMCircuit
import Mathlib.Data.List.ProdSigma

/-! Explicit finite enumerations for uniform scalar-sum construction.
There is deliberately no arbitrary-`Fintype` fallback. Each runtime instance
is built by finite ranges, fixed Boolean/unit lists, tagged concatenation,
or a literal nested product loop. Proof fields certify coverage and are
irrelevant to construction of the actual list. -/
namespace MatrixSpencer.RealRAM

class FiniteEnumeration (α : Type*) where
  elems : List α
  nodup : elems.Nodup
  complete : ∀ a, a ∈ elems

namespace FiniteEnumeration
variable {α β : Type*}

instance (n : ℕ) : FiniteEnumeration (Fin n) where
  elems := List.finRange n
  nodup := List.nodup_finRange n
  complete := List.mem_finRange

instance : FiniteEnumeration Bool where
  elems := [false,true]
  nodup := by decide
  complete b := by cases b <;> simp

instance : FiniteEnumeration Unit where
  elems := [()]
  nodup := by simp
  complete a := by cases a; simp

instance [FiniteEnumeration α] [FiniteEnumeration β] : FiniteEnumeration (α × β) where
  elems := (elems (α:=α)).product (elems (α:=β))
  nodup := nodup.product nodup
  complete p := List.mem_product.mpr ⟨complete p.1,complete p.2⟩

instance [FiniteEnumeration α] [FiniteEnumeration β] : FiniteEnumeration (α ⊕ β) where
  elems := (elems (α:=α)).map Sum.inl ++ (elems (α:=β)).map Sum.inr
  nodup := by
    apply List.nodup_append.mpr
    refine ⟨nodup.map Sum.inl_injective,nodup.map Sum.inr_injective,?_⟩
    intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
    cases hxy
  complete p := by cases p <;> simp [complete]

variable [FiniteEnumeration α] [Fintype α]

theorem toFinset_eq_univ [DecidableEq α] : (elems (α:=α)).toFinset=Finset.univ := by
  ext a
  simp [complete]

@[simp] theorem length_eq_card : (elems (α:=α)).length=Fintype.card α := by
  classical
  rw [←List.toFinset_card_of_nodup nodup,toFinset_eq_univ]
  rfl

theorem sum_eq {M : Type*} [AddCommMonoid M] (f : α → M) :
    ((elems (α:=α)).map f).sum=∑ a,f a := by
  classical
  rw [←List.sum_toFinset f nodup,toFinset_eq_univ]

/-- Literal list descriptions expose the actual uniform loop order. -/
@[simp] theorem elems_fin (n : ℕ) : elems (α:=Fin n)=List.finRange n := rfl
@[simp] theorem elems_prod [FiniteEnumeration β] :
    elems (α:=α×β)=(elems (α:=α)).product (elems (α:=β)) := rfl
@[simp] theorem elems_sum [FiniteEnumeration β] :
    elems (α:=α⊕β)=(elems (α:=α)).map Sum.inl ++ (elems (α:=β)).map Sum.inr := rfl

end FiniteEnumeration
end MatrixSpencer.RealRAM
