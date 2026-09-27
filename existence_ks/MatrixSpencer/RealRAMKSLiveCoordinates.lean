import MatrixSpencer.RealRAMFullHessian
import MatrixSpencer.KSFullManuscriptLiveCoordinates
import MatrixSpencer.KSDebitMovement

/-! Counted finite live-label scans, coordinate extension, and scalar movement.
The extension sums the finite label table, so no inverse-equivalence or linear
map operation is treated as a primitive. Each entry is a scalar circuit. -/
open Matrix Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.KSLiveCoordinates
open JacobiIteration (Counted)
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {σ : Type*}

def scan (x : Fin N → ℝ) : List (Fin N) → Counted (List (Fin N))
  | [] => ⟨[],1⟩
  | i::is =>
    let tail := scan x is
    ⟨if -1 < x i ∧ x i < 1 then i::tail.value else tail.value,tail.cost+10⟩

theorem scan_value (x : Fin N → ℝ) (is : List (Fin N)) :
    (scan x is).value = is.filter (fun i => decide (|x i|<1)) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [scan,ih,List.filter_cons]
    by_cases h : -1 < x i ∧ x i < 1
    · simp [h,abs_lt]
    · simp [h,abs_lt]

theorem scan_cost (x : Fin N → ℝ) (is : List (Fin N)) :
    (scan x is).cost = 10*is.length+1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [scan,ih]; omega

def table (x : Fin N → ℝ) : Counted (List (Fin N)) :=
  let s := scan x (List.finRange N)
  ⟨s.value,s.cost+3*N+1⟩

theorem table_value (x : Fin N → ℝ) : (table x).value=KSLiveEnumeration.labels x := by
  simp [table,scan_value,KSLiveEnumeration.labels]

theorem table_cost (x : Fin N → ℝ) : (table x).cost=13*N+2 := by
  simp [table,scan_cost]; omega

theorem count_le (x : Fin N → ℝ) : KSLiveEnumeration.count x ≤ N := by
  exact (List.length_filter_le _ _).trans_eq (List.length_finRange)

def sumExpr {ι : Type*} (f : ι → Expr σ) : List ι → Expr σ
  | [] => .constant 0
  | i::is => .add (f i) (sumExpr f is)

theorem sumExpr_eval {ι : Type*} (f : ι → Expr σ) (is : List ι) (v : σ → ℝ) :
    (sumExpr f is).eval v = (is.map (fun i => (f i).eval v)).sum := by
  induction is with
  | nil => simp [sumExpr,Expr.eval]
  | cons i is ih => simp [sumExpr,Expr.eval,ih]

theorem sumExpr_cost {ι : Type*} (f : ι → Expr σ) (is : List ι) {b : ℕ}
    (hb : ∀i∈is,(f i).cost≤b) : (sumExpr f is).cost ≤ is.length*(b+1)+1 := by
  induction is with
  | nil => simp [sumExpr,Expr.cost]
  | cons i is ih =>
    have hi := hb i (by simp)
    have ht := ih (by intro j hj; exact hb j (by simp [hj]))
    simp only [sumExpr,Expr.cost,List.length_cons]
    nlinarith

def extensionExpr (x : Fin N → ℝ) (i : Fin N) : Expr (Fin (KSLiveEnumeration.count x)) :=
  sumExpr (fun j => if (KSLiveEnumeration.liveEquiv x j).val=i then .input j else .constant 0)
    (List.finRange (KSLiveEnumeration.count x))

def extension (x : Fin N → ℝ) (z : KSNumericalHessian.Space (KSLiveEnumeration.count x)) :
    Counted (KSNumericalHessian.Space N) :=
  ⟨WithLp.toLp 2 (fun i => (extensionExpr x i).eval z),
    (table x).cost+N*(5*KSLiveEnumeration.count x+3)+1⟩

theorem extension_value (x : Fin N → ℝ) (z : KSNumericalHessian.Space (KSLiveEnumeration.count x)) :
    (extension x z).value=KSLiveEnumeration.extend x z := by
  ext i
  change (extensionExpr x i).eval z = _
  rw [extensionExpr,sumExpr_eval,← List.ofFn_eq_map,List.sum_ofFn]
  simp only [apply_ite,Expr.eval,Rat.cast_zero]
  by_cases hi : |x i|<1
  · rw [KSLiveEnumeration.extend_live x z ⟨i,hi⟩]
    rw [Finset.sum_eq_single ((KSLiveEnumeration.liveEquiv x).symm ⟨i,hi⟩)]
    · simp
    · intro j _ hj
      have hne : (KSLiveEnumeration.liveEquiv x j).val≠i := by
        intro he
        have hsub : KSLiveEnumeration.liveEquiv x j=⟨i,hi⟩ := Subtype.ext he
        exact hj ((Equiv.apply_eq_iff_eq_symm_apply _).mp hsub)
      simp [hne]
    · simp
  · rw [KSLiveEnumeration.extend_dead x z i hi]
    apply Finset.sum_eq_zero
    intro j _
    have hne : (KSLiveEnumeration.liveEquiv x j).val≠i := by
      intro he
      have hj := (KSLiveEnumeration.liveEquiv x j).property
      exact hi (he ▸ hj)
    simp [hne]

theorem extension_cost (x : Fin N → ℝ) (z : KSNumericalHessian.Space (KSLiveEnumeration.count x)) :
    (extension x z).cost≤20*(N+1)^2 := by
  have h := count_le x
  dsimp [extension]
  rw [table_cost]
  nlinarith

def face (x : Fin N → ℝ) (z : KSNumericalHessian.Space (KSLiveEnumeration.count x)) :
    Counted (Fin N → ℝ) :=
  let e := extension x z
  ⟨fun i => (Expr.add (.input false) (.input true)).eval (fun b => if b then e.value i else x i),
    e.cost+5*N+1⟩

theorem face_value (x : Fin N → ℝ) (z : KSNumericalHessian.Space (KSLiveEnumeration.count x)) :
    (face x z).value=KSFullManuscriptLiveCoordinates.face x z := by
  change (face x z).value = fun i => x i+KSLiveEnumeration.extend x z i
  simp [face,Expr.eval,extension_value]

theorem face_cost (x : Fin N → ℝ) (z : KSNumericalHessian.Space (KSLiveEnumeration.count x)) :
    (face x z).cost≤26*(N+1)^2 := by
  have h := extension_cost x z
  dsimp [face]
  nlinarith

def weightExpr : Expr Unit := .sqrt (.sub (.constant 1) (.mul (.input ()) (.input ())))

def weights (x : Fin N → ℝ) : Counted (Fin (KSLiveEnumeration.count x) → ℝ) :=
  ⟨fun j => weightExpr.eval (fun _ => x (KSLiveEnumeration.liveEquiv x j)),
    (table x).cost+10*KSLiveEnumeration.count x+1⟩

theorem weights_value (x : Fin N → ℝ) :
    (weights x).value=KSFullManuscriptLiveCoordinates.weight x := by
  funext j
  simp [weights,weightExpr,Expr.eval,KSFullManuscriptLiveCoordinates.weight,pow_two]

theorem weights_valid {x : Fin N → ℝ} (hx : x∈ksCube 1) (i : Fin N) :
    weightExpr.Valid (fun _ => x i) := by
  have hl := hx.1 i
  have hu := hx.2 i
  simp [weightExpr,Expr.Valid,Expr.eval]
  nlinarith

theorem weights_cost (x : Fin N → ℝ) : (weights x).cost≤23*N+3 := by
  have h := count_le x
  dsimp [weights]
  rw [table_cost]
  omega

def movementExpr : Expr (Fin 3) :=
  .add (.input 0) (.mul (.input 2)
    (.mul (.sqrt (.sub (.constant 1) (.mul (.input 0) (.input 0)))) (.input 1)))

def movement (x : Fin N → ℝ) (z : KSNumericalHessian.Space N) (t : ℝ) : Counted (Fin N → ℝ) :=
  ⟨fun i => movementExpr.eval ![x i,z i,t],N*(movementExpr.cost+4)+1⟩

theorem movement_value (x : Fin N → ℝ) (z : KSNumericalHessian.Space N) (t : ℝ) :
    (movement x z t).value=KSDebitMovement.proposal x z t := by
  funext i
  simp [movement,movementExpr,Expr.eval,KSDebitMovement.proposal_apply,pow_two]

theorem movement_valid {x : Fin N → ℝ} (hx : x∈ksCube 1)
    (z : KSNumericalHessian.Space N) (t : ℝ) (i : Fin N) :
    movementExpr.Valid ![x i,z i,t] := by
  have hl := hx.1 i
  have hu := hx.2 i
  simp [movementExpr,Expr.Valid,Expr.eval]
  nlinarith

theorem movement_cost (x : Fin N → ℝ) (z : KSNumericalHessian.Space N) (t : ℝ) :
    (movement x z t).cost=16*N+1 := by
  simp [movement,movementExpr,Expr.cost]
  ring

end MatrixSpencer.RealRAM.KSLiveCoordinates
