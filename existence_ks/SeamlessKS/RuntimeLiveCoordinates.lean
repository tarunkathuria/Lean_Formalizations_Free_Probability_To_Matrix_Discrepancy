import MatrixSpencer.RealRAMKSLiveCoordinates

/-! Explicit extension through the actually computed live-label table.
Each forward lookup is charged conservatively as a linear list traversal.
Consequently the extension has a cubic bound; no inverse equivalence or
uncounted filtered-list evaluation is an execution primitive. -/
open scoped BigOperators
noncomputable section
namespace SeamlessKS.RuntimeLiveCoordinates
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {N m : ℕ}

/-- A finite scalar sum with index comparisons against stored labels. -/
def entryExpr (labels : Fin m → Fin N) (i : Fin N) : Expr (Fin m) :=
  Expr.sumList (List.ofFn (fun j => if labels j=i then .input j else .constant 0))

theorem entryExpr_eval (labels : Fin m → Fin N) (z : Fin m → ℝ) (i : Fin N) :
    (entryExpr labels i).eval z=∑ j,if labels j=i then z j else 0 := by
  simp [entryExpr,Expr.eval_sumList,List.map_ofFn,List.sum_ofFn,apply_ite,Expr.eval]

theorem entryExpr_valid (labels : Fin m → Fin N) (z : Fin m → ℝ) (i : Fin N) :
    (entryExpr labels i).Valid z := by
  apply Expr.valid_sumList
  intro e he
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
  split_ifs <;> trivial

theorem entryExpr_cost (labels : Fin m → Fin N) (i : Fin N) :
    (entryExpr labels i).cost=2*m+1 := by
  have hf (j : Fin m) : ((if labels j=i then Expr.input j else .constant 0) : Expr (Fin m)).cost=1 := by
    split_ifs <;> rfl
  simp [entryExpr,Expr.cost_sumList,List.map_ofFn,List.sum_ofFn,hf]
  omega

/-- `get` consumes the output of the counted table computation. The cast
certifies its length and carries no numerical information. -/
def storedLabel (x : Fin N → ℝ) (j : Fin (KSLiveEnumeration.count x)) : Fin N :=
  (KSLiveCoordinates.table x).value.get ⟨j.val,by
    rw [KSLiveCoordinates.table_value]
    exact j.isLt⟩

theorem storedLabel_value (x : Fin N → ℝ) (j : Fin (KSLiveEnumeration.count x)) :
    storedLabel x j=(KSLiveEnumeration.liveEquiv x j).val := by
  have hj : j.val < (KSLiveCoordinates.table x).value.length := by
    rw [KSLiveCoordinates.table_value]
    exact j.isLt
  have he := congrArg (fun l : List (Fin N) => l[j.val]?) (KSLiveCoordinates.table_value x)
  dsimp only at he
  rw [List.getElem?_eq_getElem hj,List.getElem?_eq_getElem j.isLt] at he
  exact Option.some.inj he

def extension (x : Fin N → ℝ) (z : KSNumericalHessian.Space (KSLiveEnumeration.count x)) :
    Counted (KSNumericalHessian.Space N) :=
  let labels := KSLiveCoordinates.table x
  let stored : Fin (KSLiveEnumeration.count x) → Fin N := fun j =>
    labels.value.get ⟨j.val,by rw [KSLiveCoordinates.table_value];exact j.isLt⟩
  ⟨WithLp.toLp 2 (fun i => (entryExpr stored i).eval z),
    labels.cost+N*(KSLiveEnumeration.count x*(N+8)+5)+1⟩

theorem extension_value (x : Fin N → ℝ) (z : KSNumericalHessian.Space (KSLiveEnumeration.count x)) :
    (extension x z).value=KSLiveEnumeration.extend x z := by
  rw [←KSLiveCoordinates.extension_value x z]
  ext i
  change (entryExpr (storedLabel x) i).eval z=(KSLiveCoordinates.extensionExpr x i).eval z
  rw [entryExpr_eval,KSLiveCoordinates.extensionExpr,KSLiveCoordinates.sumExpr_eval,
    ←List.ofFn_eq_map,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  rw [storedLabel_value]
  split_ifs <;> norm_num [Expr.eval]

theorem extension_execution (x : Fin N → ℝ)
    (z : KSNumericalHessian.Space (KSLiveEnumeration.count x)) (i : Fin N) :
    Expr.Executes z (entryExpr (storedLabel x) i) ((extension x z).value i)
      (2*KSLiveEnumeration.count x+1) := by
  simpa only [entryExpr_cost] using Expr.executes_of_valid z
    (entryExpr (storedLabel x) i) (entryExpr_valid _ _ _)

def extensionBound (N : ℕ) : ℕ := 50*(N+1)^3

theorem extension_cost (x : Fin N → ℝ)
    (z : KSNumericalHessian.Space (KSLiveEnumeration.count x)) :
    (extension x z).cost≤extensionBound N := by
  have hm := KSLiveCoordinates.count_le x
  have hh := Nat.mul_le_mul_right (N+8) hm
  have hh' := Nat.mul_le_mul_left N (Nat.add_le_add_right hh 5)
  change (KSLiveCoordinates.table x).cost+N*(KSLiveEnumeration.count x*(N+8)+5)+1≤_
  rw [KSLiveCoordinates.table_cost]
  unfold extensionBound
  nlinarith [Nat.zero_le (N^3),Nat.zero_le (N^2)]

def face (x : Fin N → ℝ) (z : KSNumericalHessian.Space (KSLiveEnumeration.count x)) :
    Counted (Fin N → ℝ) :=
  let e := extension x z
  ⟨fun i => (Expr.add (.input false) (.input true)).eval
      (fun b => if b then e.value i else x i),e.cost+5*N+1⟩

theorem face_value (x : Fin N → ℝ) (z : KSNumericalHessian.Space (KSLiveEnumeration.count x)) :
    (face x z).value=KSFullManuscriptLiveCoordinates.face x z := by
  change (face x z).value=fun i => x i+KSLiveEnumeration.extend x z i
  simp [face,Expr.eval,extension_value]

theorem face_execution (x : Fin N → ℝ) (z : KSNumericalHessian.Space (KSLiveEnumeration.count x))
    (i : Fin N) :
    Expr.Executes (fun b => if b then (extension x z).value i else x i)
      (.add (.input false) (.input true)) ((face x z).value i) 3 :=
  Expr.executes_of_valid _ _ ⟨trivial,trivial⟩

def faceBound (N : ℕ) : ℕ := 60*(N+1)^3

theorem face_cost (x : Fin N → ℝ) (z : KSNumericalHessian.Space (KSLiveEnumeration.count x)) :
    (face x z).cost≤faceBound N := by
  have he := extension_cost x z
  change (extension x z).cost+5*N+1≤_
  unfold extensionBound faceBound at *
  nlinarith [Nat.zero_le (N^3),Nat.zero_le (N^2)]

end SeamlessKS.RuntimeLiveCoordinates
