import SeamlessKS.RuntimeQueries
import SeamlessKS.Walk
import Mathlib.Data.List.MinMax

/-! Finite primitive implementation of the actual outward-label selection.
The old value is evaluated once. Original labels are scanned in their fixed
order; each live label is tested by an actual smooth-potential value query.
The least successful label is selected by explicit integer comparisons. -/
open Matrix Set
open scoped BigOperators
noncomputable section
namespace SeamlessKS.RuntimeSelection
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open MatrixSpencer.KSPolynomialConvexSolver
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable
variable {N d : ℕ}

def outwardInput (x : Fin N → ℝ) (a : ℝ) : Fin N ⊕ Unit → ℝ :=
  Sum.elim x (fun _ => a)

def outwardExpr (i j : Fin N) (positive : Bool) : Expr (Fin N ⊕ Unit) :=
  if j=i then
    if positive then .add (.input (.inl i)) (.input (.inr ()))
    else .sub (.input (.inl i)) (.input (.inr ()))
  else .input (.inl j)

@[simp] theorem outwardExpr_eval (x : Fin N → ℝ) (a : ℝ) (i j : Fin N) :
    (outwardExpr i j (decide (0≤x i))).eval (outwardInput x a)=
      Proposals.outwardVector x i a j := by
  by_cases hji : j=i <;> by_cases hp : 0≤x i <;>
    simp [outwardExpr,hji,hp,Expr.eval,outwardInput,Proposals.outwardVector,
      Progress.outward,Function.update_apply]

theorem outwardExpr_valid (u : Fin N ⊕ Unit → ℝ) (i j : Fin N) (b : Bool) :
    (outwardExpr i j b).Valid u := by
  unfold outwardExpr
  split_ifs <;> trivial

theorem outwardExpr_cost (i j : Fin N) (b : Bool) : (outwardExpr i j b).cost≤3 := by
  unfold outwardExpr
  split_ifs <;> norm_num [Expr.cost]

def outward (x : Fin N → ℝ) (i : Fin N) (a : ℝ) : Counted (Fin N → ℝ) :=
  let b := decide (0≤x i)
  ⟨fun j => (outwardExpr i j b).eval (outwardInput x a),
    (∑ j,((outwardExpr i j b).cost+1))+8⟩

@[simp] theorem outward_value (x : Fin N → ℝ) (i : Fin N) (a : ℝ) :
    (outward x i a).value=Proposals.outwardVector x i a := by
  funext j
  exact outwardExpr_eval x a i j

theorem outward_execution (x : Fin N → ℝ) (i j : Fin N) (a : ℝ) :
    Expr.Executes (outwardInput x a) (outwardExpr i j (decide (0≤x i)))
      ((outward x i a).value j) (outwardExpr i j (decide (0≤x i))).cost :=
  Expr.executes_of_valid _ _ (outwardExpr_valid _ _ _ _)

theorem outward_cost (x : Fin N → ℝ) (i : Fin N) (a : ℝ) :
    (outward x i a).cost≤4*N+8 := by
  have hh := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin N))) =>
    Nat.add_le_add_right (outwardExpr_cost i j (decide (0≤x i))) 1)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hh
  dsimp only [outward]
  omega

/-- Optional minimum computed with one original-label comparison. -/
def minimumStep (i : Fin N) : Option (Fin N) → Option (Fin N)
  | none => some i
  | some j => if j < i then some j else some i

/-- This generic finite scan is instantiated below by the literal local test. -/
def scan (E : Fin N → Counted Bool) : List (Fin N) → Counted (Option (Fin N))
  | [] => ⟨none,1⟩
  | i::is =>
    let e := E i
    let r := scan E is
    ⟨if e.value then minimumStep i r.value else r.value,e.cost+r.cost+12⟩

theorem scan_value (E : Fin N → Counted Bool) (is : List (Fin N)) :
    (scan E is).value=(is.filter (fun i => (E i).value)).argmin id := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [scan,ih,List.filter_cons]
    cases h : (E i).value <;> simp [List.argmin_cons,minimumStep]
    cases ((is.filter (fun i => (E i).value)).argmin id) <;> rfl

theorem scan_cost (E : Fin N → Counted Bool) {Q : ℕ}
    (hQ : ∀ i,(E i).cost≤Q) (is : List (Fin N)) :
    (scan E is).cost ≤ is.length*(Q+12)+1 := by
  induction is with
  | nil => simp [scan]
  | cons i is ih =>
    have hh := hQ i
    simp only [scan,List.length_cons]
    nlinarith

/-- The primitive scan is equal to the mathematical filtered-finset minimum. -/
theorem scan_value_min (E : Fin N → Counted Bool) :
    (scan E (List.finRange N)).value=
      if hn : (Finset.univ.filter (fun i => (E i).value=true)).Nonempty then
        some ((Finset.univ.filter (fun i => (E i).value=true)).min' hn) else none := by
  rw [scan_value]
  let l := (List.finRange N).filter (fun i => (E i).value)
  let f := Finset.univ.filter (fun i => (E i).value=true)
  have hmem (i : Fin N) : i∈l ↔ i∈f := by simp [l,f]
  change l.argmin id=(if hn : f.Nonempty then some (f.min' hn) else none)
  cases ha : l.argmin id with
  | none =>
    have hl := List.argmin_eq_none.mp ha
    have hf : ¬f.Nonempty := by
      rintro ⟨i,hi⟩
      have hm := (hmem i).mpr hi
      simp only [hl,List.not_mem_nil] at hm
    simp [hf]
  | some i =>
    have hi : i∈f := (hmem i).mp (List.argmin_mem ha)
    have hn : f.Nonempty := ⟨i,hi⟩
    simp only [dif_pos hn,Option.some.injEq]
    apply le_antisymm
    · exact List.le_of_mem_argmin ((hmem _).mpr (Finset.min'_mem f hn)) ha
    · exact Finset.min'_le f i hi

variable [Nonempty (Fin d)]

/-- The old report is a previously evaluated scalar, not a supplied oracle. -/
def localTest (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (x : Fin N → ℝ) (ζ θ ν a old : ℝ) (i : Fin N) : Counted Bool :=
  if -1<x i ∧ x i<1 then
    let y := outward x i a
    let r := RuntimeQueries.report P v y.value ζ θ ν
    ⟨decide (r.value-old≤2*ν),y.cost+r.cost+16⟩
  else ⟨false,10⟩

theorem localTest_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (x : Fin N → ℝ) (ζ θ ν a old : ℝ) (i : Fin N) :
    (localTest P v x ζ θ ν a old i).value=
      decide (|x i|<1 ∧
        Value.report P.solver v 0 θ ζ ν
          (Proposals.outwardVector x i a)-old≤2*ν) := by
  by_cases hi : -1<x i ∧ x i<1
  · simp only [localTest,if_pos hi,RuntimeQueries.report_value,outward_value]
    simp only [abs_lt,hi,true_and]
  · simp [localTest,hi,abs_lt]

theorem localTest_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (x : Fin N → ℝ) (ζ θ a old : ℝ) {ν : ℝ} (hν : 0<ν)
    {V : ℕ} (hV : ν⁻¹≤(V:ℝ)) (i : Fin N) :
    (localTest P v x ζ θ ν a old i).cost≤
      RuntimeQueries.queryBound P N d V+4*N+24 := by
  by_cases hi : -1<x i ∧ x i<1
  · have hy := outward_cost x i a
    have hr := RuntimeQueries.report_cost P v (outward x i a).value ζ θ hν hV
    simp only [localTest,if_pos hi]
    omega
  · simp only [localTest,if_neg hi]
    omega

def select (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    {ρ : ℝ} (s : State.PreparedState N ρ) (ζ θ ν a : ℝ) : Counted (Option (Fin N)) :=
  let old := RuntimeQueries.report P v s.coeff ζ θ ν
  let r := scan (localTest P v s.coeff ζ θ ν a old.value) (List.finRange N)
  ⟨r.value,old.cost+r.cost+3*N+2⟩

theorem select_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    {ρ : ℝ} (s : State.PreparedState N ρ) (ζ θ ν a : ℝ) :
    (select P v s ζ θ ν a).value=OutwardSelection.select P.solver v θ ζ ν a s := by
  simp only [select,scan_value_min,localTest_value,RuntimeQueries.report_value,decide_eq_true_eq]
  rfl

def selectionBound (P : PolynomialSolver) (N d V : ℕ) : ℕ :=
  (N+1)*RuntimeQueries.queryBound P N d V+4*N^2+39*N+3

theorem select_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    {ρ : ℝ} (s : State.PreparedState N ρ) (ζ θ a : ℝ) {ν : ℝ} (hν : 0<ν)
    {V : ℕ} (hV : ν⁻¹≤(V:ℝ)) :
    (select P v s ζ θ ν a).cost≤selectionBound P N d V := by
  have ho := RuntimeQueries.report_cost P v s.coeff ζ θ hν hV
  have hs := scan_cost (localTest P v s.coeff ζ θ ν a
    (RuntimeQueries.report P v s.coeff ζ θ ν).value)
    (fun i => localTest_cost P v s.coeff ζ θ a _ hν hV i) (List.finRange N)
  simp only [List.length_finRange] at hs
  dsimp only [select]
  unfold selectionBound
  nlinarith

def chosenLabel (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (s : Walk.WalkState N) :
    Counted (Option (Fin N)) :=
  select P v s (Parameters.zeta N) (Input.theta v) (Parameters.localAccuracy v)
    (Parameters.outwardStep N)

theorem chosenLabel_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (s : Walk.WalkState N) :
    (chosenLabel P v s).value=Walk.chosenLabel P.solver v s :=
  select_value P v s _ _ _ _

theorem chosenLabel_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑ i,KSRankOne.atom (v i))=1) (s : Walk.WalkState N) :
    (chosenLabel P v s).cost≤selectionBound P N d (RuntimeBudgets.localAccuracyInverseCap N d) := by
  apply select_cost P v s _ _ _ (Parameters.localAccuracy_pos v hd hp)
  simpa only [RuntimeBudgets.cast_localAccuracyInverseCap] using
    Parameters.localAccuracy_inverse_le v hd hp

end SeamlessKS.RuntimeSelection
