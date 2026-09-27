import HigherRankKSRuntime.ActiveEnumeration
import SeamlessKS.RuntimeLiveCoordinates

/-! Counted ordered enumeration and zero extension of active original owners.
The extension uses scalar sums against the stored label table, with each list
lookup charged as a full traversal. It never executes an inverse equivalence. -/
noncomputable section
open scoped BigOperators
namespace HigherRankKSRuntime.ActiveEnumeration.Execution
open AugmentedHigherRankKS MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {N : ℕ}

def scan (z : EpochState (Fin N)) : List (Fin N) → Counted (List (Fin N))
  | [] => ⟨[],1⟩
  | i::is => let tail := scan z is
             ⟨if 0 < reserve z i then i::tail.value else tail.value,tail.cost+10⟩

theorem scan_value (z : EpochState (Fin N)) (is : List (Fin N)) :
    (scan z is).value = is.filter (fun i => decide (0 < reserve z i)) := by
  induction is with
  | nil => rfl
  | cons i is ih => by_cases h : 0 < reserve z i <;> simp [scan,ih,h]

theorem scan_cost (z : EpochState (Fin N)) (is : List (Fin N)) :
    (scan z is).cost = 10*is.length+1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [scan,ih]; omega

def table (z : EpochState (Fin N)) : Counted (List (Fin N)) :=
  let s := scan z (List.finRange N)
  ⟨s.value,s.cost+3*N+1⟩

theorem table_value (z : EpochState (Fin N)) : (table z).value=labels z := by
  simp [table,scan_value,labels]
theorem table_cost (z : EpochState (Fin N)) : (table z).cost=13*N+2 := by
  simp [table,scan_cost]; omega

def storedLabel (z : EpochState (Fin N)) (j : Fin (count z)) : Fin N :=
  (table z).value.get ⟨j.val,by rw [table_value]; exact j.isLt⟩

theorem storedLabel_value (z : EpochState (Fin N)) (j : Fin (count z)) :
    storedLabel z j=(activeEquiv z j).val := by
  have hj : j.val < (table z).value.length := by rw [table_value]; exact j.isLt
  have he := congrArg (fun l : List (Fin N) => l[j.val]?) (table_value z)
  dsimp only at he
  rw [List.getElem?_eq_getElem hj,List.getElem?_eq_getElem j.isLt] at he
  exact Option.some.inj he

def extension (z : EpochState (Fin N)) (v : EuclideanSpace ℝ (Fin (count z))) :
    Counted (EuclideanSpace ℝ (Fin N)) :=
  let labels := table z
  let stored : Fin (count z) → Fin N := fun j =>
    labels.value.get ⟨j.val,by rw [table_value]; exact j.isLt⟩
  ⟨WithLp.toLp 2 (fun i => (SeamlessKS.RuntimeLiveCoordinates.entryExpr stored i).eval v),
    labels.cost+N*(count z*(N+8)+5)+1⟩

theorem extension_value (z : EpochState (Fin N)) (v : EuclideanSpace ℝ (Fin (count z))) :
    (extension z v).value=extend z v := by
  ext i
  change (SeamlessKS.RuntimeLiveCoordinates.entryExpr (storedLabel z) i).eval v = _
  rw [SeamlessKS.RuntimeLiveCoordinates.entryExpr_eval]
  simp only [storedLabel_value]
  by_cases hi : 0 < reserve z i
  · let ai : ActiveOwners z := ⟨i,(mem_positiveReserves z i).mpr hi⟩
    rw [show extend z v i = v ((activeEquiv z).symm ai) from extend_active z v ai]
    rw [Finset.sum_eq_single ((activeEquiv z).symm ai)]
    · simp [ai]
    · intro j _ hj
      have hne : (activeEquiv z j).val ≠ i := by
        intro he
        have hh : activeEquiv z j=ai := Subtype.ext he
        exact hj ((Equiv.apply_eq_iff_eq_symm_apply _).mp hh)
      simp [hne]
    · simp
  · rw [extend_inactive z v i hi]
    apply Finset.sum_eq_zero
    intro j _
    have hne : (activeEquiv z j).val ≠ i := by
      intro he
      have hp := (mem_positiveReserves z (activeEquiv z j).val).mp (activeEquiv z j).property
      exact hi (he ▸ hp)
    simp [hne]

theorem extension_execution (z : EpochState (Fin N))
    (v : EuclideanSpace ℝ (Fin (count z))) (i : Fin N) :
    Expr.Executes v (SeamlessKS.RuntimeLiveCoordinates.entryExpr (storedLabel z) i)
      ((extension z v).value i) (2*count z+1) := by
  simpa only [SeamlessKS.RuntimeLiveCoordinates.entryExpr_cost] using
    Expr.executes_of_valid v (SeamlessKS.RuntimeLiveCoordinates.entryExpr (storedLabel z) i)
      (SeamlessKS.RuntimeLiveCoordinates.entryExpr_valid _ _ _)

theorem extension_cost (z : EpochState (Fin N)) (v : EuclideanSpace ℝ (Fin (count z))) :
    (extension z v).cost ≤ 50*(N+1)^3 := by
  have hm := count_le z
  have hh := Nat.mul_le_mul_right (N+8) hm
  have hh' := Nat.mul_le_mul_left N (Nat.add_le_add_right hh 5)
  change (table z).cost+N*(count z*(N+8)+5)+1 ≤ _
  rw [table_cost]
  nlinarith [Nat.zero_le (N^3),Nat.zero_le (N^2)]

def positions (z : EpochState (Fin N)) : Counted (EuclideanSpace ℝ (Fin (count z))) :=
  ⟨WithLp.toLp 2 (fun j => position z (storedLabel z j)),(table z).cost+count z*(N+3)+1⟩

theorem positions_value (z : EpochState (Fin N)) : (positions z).value=restrictedPosition z := by
  ext j
  change position z (storedLabel z j)=position z (activeEquiv z j)
  rw [storedLabel_value]

theorem positions_cost (z : EpochState (Fin N)) : (positions z).cost ≤ 20*(N+1)^2 := by
  have hm := count_le z
  have hh := Nat.mul_le_mul_right (N+3) hm
  change (table z).cost+count z*(N+3)+1 ≤ _
  rw [table_cost]
  nlinarith
end HigherRankKSRuntime.ActiveEnumeration.Execution
