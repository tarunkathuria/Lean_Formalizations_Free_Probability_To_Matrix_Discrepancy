import RadialKS.WalkGeometry
import RadialKS.WalkDrift
import SeamlessKS.RuntimeWalk

/-! Counted execution of the concrete radial step. Scalar array updates,
live-label lookup, both candidate value queries, and the comparison are charged.
The frame is implemented by RuntimeDirection, rather than provided as a primitive. -/
open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace RadialKS.RuntimeMotion
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open MatrixSpencer.KSPolynomialConvexSolver
open SeamlessKS SeamlessKS.State SeamlessKS.Parameters RadialKS.Walk
open MatrixSpencer.KSLiveEnumeration (count liveEquiv)
attribute [local instance] Classical.propDecidable
variable {N d : ℕ} [Nonempty (Fin d)]

def positions (s : WalkState N) : Counted (EuclideanSpace ℝ (Fin (count s.coeff))) :=
  let labels := KSLiveCoordinates.table s.coeff
  ⟨WithLp.toLp 2 (fun i => match labels.value[i.val]? with
      | none => 0
      | some j => s.coeff j), labels.cost+count s.coeff*(N+4)+1⟩

theorem positions_value (s : WalkState N) : (positions s).value=Walk.position s := by
  ext i
  simp only [positions,KSLiveCoordinates.table_value]
  change (match (KSLiveEnumeration.labels s.coeff)[i.val]? with | none => 0 | some j => s.coeff j) = _
  rw [List.getElem?_eq_getElem i.isLt]
  rfl

theorem positions_cost (s : WalkState N) : (positions s).cost≤50*(N+1)^2 := by
  have hh := KSLiveCoordinates.count_le s.coeff
  change (KSLiveCoordinates.table s.coeff).cost+count s.coeff*(N+4)+1≤50*(N+1)^2
  rw [KSLiveCoordinates.table_cost]
  nlinarith

def movementExpr : Expr (Fin 3) := .add (.input 0) (.mul (.input 1) (.input 2))
def movementInput (x t g : ℝ) : Fin 3 → ℝ := ![x,t,g]

theorem movementExpr_eval (x t g : ℝ) : movementExpr.eval (movementInput x t g)=x+t*g := rfl

theorem movementExpr_valid (u : Fin 3 → ℝ) : movementExpr.Valid u := by trivial

def movement (x : Fin N → ℝ) (g : EuclideanSpace ℝ (Fin N)) (t : ℝ) : Counted (Fin N → ℝ) :=
  ⟨fun i => movementExpr.eval (movementInput (x i) t (g i)),8*N+1⟩

theorem movement_value (x : Fin N → ℝ) (g : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    (movement x g t).value=Progress.proposal x g t := rfl

theorem movement_execution (x : Fin N → ℝ) (g : EuclideanSpace ℝ (Fin N)) (t : ℝ) (i : Fin N) :
    Expr.Executes (movementInput (x i) t (g i)) movementExpr ((movement x g t).value i) 5 :=
  Expr.executes_of_valid _ _ (movementExpr_valid _)

def candidate (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (s : WalkState N)
    (g : EuclideanSpace ℝ (Fin (count s.coeff))) (b : Bool) : Counted ((Fin N → ℝ) × ℝ) :=
  let e := RuntimeLiveCoordinates.extension s.coeff g
  let y := movement s.coeff e.value (Walk.signedStep v b)
  let r := RuntimeQueries.report P v y.value (zeta N) (Input.theta v) (localAccuracy v)
  ⟨(y.value,r.value),e.cost+y.cost+r.cost+5⟩

theorem candidate_coeff (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (s : WalkState N)
    (g : EuclideanSpace ℝ (Fin (count s.coeff))) (b : Bool) :
    (candidate P v s g b).value.1=
      Progress.proposal s.coeff (KSLiveEnumeration.extend s.coeff g) (Walk.signedStep v b) := by
  simp only [candidate,movement_value,RuntimeLiveCoordinates.extension_value]

theorem candidate_report (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (s : WalkState N)
    (g : EuclideanSpace ℝ (Fin (count s.coeff))) (b : Bool) :
    (candidate P v s g b).value.2=Walk.endpointReport P.solver v s g b := by
  simp only [candidate,RuntimeQueries.report_value,movement_value,RuntimeLiveCoordinates.extension_value]
  rw [←WalkDrift.face_proposal]
  rfl

def candidateBound (P : PolynomialSolver) (N d : ℕ) : ℕ :=
  RuntimeLiveCoordinates.extensionBound N+8*N+1+
    RuntimeQueries.queryBound P N d (RuntimeBudgets.localAccuracyInverseCap N d)+5

theorem candidate_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N)
    (g : EuclideanSpace ℝ (Fin (count s.coeff))) (b : Bool) :
    (candidate P v s g b).cost≤candidateBound P N d := by
  have he := RuntimeLiveCoordinates.extension_cost s.coeff g
  have hr := RuntimeQueries.local_report_cost P v hd hp
    (movement s.coeff (RuntimeLiveCoordinates.extension s.coeff g).value (Walk.signedStep v b)).value
  dsimp only [candidate,movement,candidateBound] at hr ⊢
  omega

/-- A single real comparison implements the choice between the two reports. -/
def choiceProgram : Program (Fin 3) :=
  .branchLE (.input 0) (.input 1) (.assign 2 (.constant 1)) (.assign 2 (.constant 0))

def choiceInput (p m : ℝ) : Fin 3 → ℝ := ![p,m,0]

theorem choiceProgram_value (p m : ℝ) :
    choiceProgram.run (choiceInput p m) 2 =
      if DeterministicRun.choosePlus p m then 1 else 0 := by
  by_cases h : p≤m <;> simp [choiceProgram,Program.run,choiceInput,Expr.eval,DeterministicRun.choosePlus,h]

theorem choiceProgram_execution (p m : ℝ) :
    Program.Executes choiceProgram (choiceInput p m) (choiceProgram.run (choiceInput p m)) 5 := by
  have hs : choiceProgram.Safe (choiceInput p m) := by
    simp [choiceProgram,Program.Safe,Expr.Valid]
  have hc : choiceProgram.cost (choiceInput p m)=5 := by
    simp [choiceProgram,Program.cost,Expr.cost]
  simpa only [hc] using Program.executes_of_safe choiceProgram (choiceInput p m) hs

def choice (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (s : WalkState N)
    (g : EuclideanSpace ℝ (Fin (count s.coeff))) : Counted (Fin N → ℝ) :=
  let p := candidate P v s g true
  let m := candidate P v s g false
  let b := DeterministicRun.choosePlus p.value.2 m.value.2
  ⟨if b then p.value.1 else m.value.1,p.cost+m.cost+N+5⟩

theorem choice_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N)
    (hs : ¬Walk.terminal s) (hn : Walk.chosenLabel P.solver v s=none) :
    (choice P v s (Walk.liveOutput P.solver v hd hp s hs hn)).value=
      Progress.proposal s.coeff (Walk.direction P.solver v hd hp s hs hn)
        (Walk.signedStep v (Walk.chooseSign P.solver v hd hp s hs hn)) := by
  simp only [choice,candidate_report,candidate_coeff]
  change (if Walk.chooseSign P.solver v hd hp s hs hn then _ else _) = _
  cases hb : Walk.chooseSign P.solver v hd hp s hs hn <;> rfl

def choiceBound (P : PolynomialSolver) (N d : ℕ) : ℕ := 2*candidateBound P N d+N+5

theorem choice_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N)
    (g : EuclideanSpace ℝ (Fin (count s.coeff))) : (choice P v s g).cost≤choiceBound P N d := by
  have hp' := candidate_cost P v hd hp s g true
  have hm' := candidate_cost P v hd hp s g false
  dsimp only [choice,choiceBound]
  omega

end RadialKS.RuntimeMotion
