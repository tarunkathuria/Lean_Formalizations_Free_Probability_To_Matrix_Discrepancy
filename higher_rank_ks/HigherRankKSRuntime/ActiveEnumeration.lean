import AugmentedHigherRankKS.EpochMovement
import Mathlib.Data.List.NodupEquivFin
import HigherRankKSRuntime.CleanupCount

/-! Original labels are scanned in order; positive reserves are indexed by a finite list.
The associated equivalence uses list lookup and index search, and only supplies proofs
about this explicit enumeration. -/
noncomputable section
open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.ActiveEnumeration
open AugmentedHigherRankKS
variable {N : ℕ}

def labels (z : EpochState (Fin N)) : List (Fin N) :=
  (List.finRange N).filter (fun i => decide (0 < reserve z i))
def count (z : EpochState (Fin N)) := (labels z).length

theorem labels_nodup (z : EpochState (Fin N)) : (labels z).Nodup :=
  (List.nodup_finRange N).filter _
@[simp] theorem mem_labels (z : EpochState (Fin N)) (i : Fin N) :
    i ∈ labels z ↔ 0 < reserve z i := by simp [labels]

def activeEquiv (z : EpochState (Fin N)) : Fin (count z) ≃ ActiveOwners z :=
  ((labels_nodup z).getEquiv (labels z)).trans
    { toFun := fun i => ⟨i.val,(mem_positiveReserves z i.val).mpr ((mem_labels z i.val).mp i.property)⟩
      invFun := fun i => ⟨i.val,(mem_labels z i.val).mpr ((mem_positiveReserves z i.val).mp i.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem count_le (z : EpochState (Fin N)) : count z ≤ N := by
  simpa [count,labels] using List.length_filter_le (fun i : Fin N => decide (0 < reserve z i)) (List.finRange N)

theorem count_eq_activeCount (z : EpochState (Fin N)) : count z = HigherRankKSRuntime.activeCount z := by
  have hh := Fintype.card_congr (activeEquiv z)
  simpa only [Fintype.card_fin,Fintype.card_coe,ActiveOwners,positiveReserves,
    HigherRankKSRuntime.activeCount,HigherRankKSRuntime.activeOwners] using hh

def restrictedPosition (z : EpochState (Fin N)) : EuclideanSpace ℝ (Fin (count z)) :=
  WithLp.toLp 2 (fun i => position z (activeEquiv z i))
def restrictedReserve (z : EpochState (Fin N)) (i : Fin (count z)) := reserve z (activeEquiv z i)
def restrictedAtoms {n : Type*} (A : Fin N → Matrix n n ℂ) (z : EpochState (Fin N))
    (i : Fin (count z)) := A (activeEquiv z i)

def extend (z : EpochState (Fin N)) (v : EuclideanSpace ℝ (Fin (count z))) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (liftActiveDirection z (fun i => v ((activeEquiv z).symm i)))

@[simp] theorem extend_active (z : EpochState (Fin N)) (v : EuclideanSpace ℝ (Fin (count z)))
    (i : ActiveOwners z) : extend z v i = v ((activeEquiv z).symm i) :=
  liftActiveDirection_active z (fun j : ActiveOwners z => v ((activeEquiv z).symm j)) i

theorem extend_inactive (z : EpochState (Fin N)) (v : EuclideanSpace ℝ (Fin (count z)))
    (i : Fin N) (hi : ¬ 0 < reserve z i) : extend z v i = 0 := by
  have hh : i ∉ positiveReserves z := by simpa only [mem_positiveReserves] using hi
  change liftActiveDirection z (fun j : ActiveOwners z => v ((activeEquiv z).symm j)) i = 0
  simp only [liftActiveDirection,dif_neg hh]

@[simp] theorem extend_index (z : EpochState (Fin N)) (v : EuclideanSpace ℝ (Fin (count z)))
    (i : Fin (count z)) : extend z v (activeEquiv z i) = v i := by
  rw [extend_active,Equiv.symm_apply_apply]

theorem sum_active {E : Type*} [AddCommMonoid E] (z : EpochState (Fin N))
    (f : Fin N → E) (hf : ∀ i, ¬ 0 < reserve z i → f i = 0) :
    ∑ i, f i = ∑ i : ActiveOwners z, f i := by
  rw [Finset.sum_coe_sort]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  apply hf
  simpa only [mem_positiveReserves] using hi

theorem extend_square_sum (z : EpochState (Fin N)) (v : EuclideanSpace ℝ (Fin (count z))) :
    ∑ i, (extend z v i)^2 = ∑ j, (v j)^2 := by
  rw [sum_active z _ (by intro i hi; rw [extend_inactive z v i hi]; norm_num)]
  simp only [extend_active]
  exact (activeEquiv z).symm.sum_comp (fun i => (v i)^2)

theorem extend_norm (z : EpochState (Fin N)) (v : EuclideanSpace ℝ (Fin (count z))) :
    ‖extend z v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
  exact extend_square_sum z v

theorem extend_dot (z : EpochState (Fin N)) (v : EuclideanSpace ℝ (Fin (count z))) :
    ∑ i, position z i*extend z v i = inner ℝ (restrictedPosition z) v := by
  rw [sum_active z _ (by intro i hi; rw [extend_inactive z v i hi,mul_zero])]
  simp only [extend_active]
  have he := (activeEquiv z).sum_comp (fun i : ActiveOwners z => position z i*v ((activeEquiv z).symm i))
  change (∑ i : ActiveOwners z, position z i*v ((activeEquiv z).symm i)) =
    ∑ j, v j*position z (activeEquiv z j)
  rw [← he]
  apply Finset.sum_congr rfl
  intro j _
  rw [Equiv.symm_apply_apply]
  ring

theorem extend_unit_square_sum (z : EpochState (Fin N)) (v : EuclideanSpace ℝ (Fin (count z)))
    (hv : ‖v‖ = 1) : ∑ i, (extend z v i)^2 = 1 := by
  rw [extend_square_sum]
  have hh := EuclideanSpace.norm_sq_eq v
  rw [hv,one_pow] at hh
  simpa only [Real.norm_eq_abs,sq_abs] using hh.symm

theorem extend_orthogonal (z : EpochState (Fin N)) (v : EuclideanSpace ℝ (Fin (count z)))
    (hv : inner ℝ (restrictedPosition z) v = 0) : ∑ i, position z i*extend z v i = 0 := by
  rw [extend_dot,hv]

theorem movement_inactive (z : EpochState (Fin N)) (v : EuclideanSpace ℝ (Fin (count z)))
    (a t : ℝ) (i : Fin N) (hi : ¬ 0 < reserve z i) :
    position (movement a z (extend z v) t) i = position z i ∧
    spent (movement a z (extend z v) t) i = spent z i ∧
    reserve (movement a z (extend z v) t) i = reserve z i := by
  simp only [movement,position,spent,reserve]
  rw [extend_inactive z v i hi]
  simp
end HigherRankKSRuntime.ActiveEnumeration
