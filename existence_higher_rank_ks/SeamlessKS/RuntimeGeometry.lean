import SeamlessKS.SourceEvaluation
import SeamlessKS.Walk
import MatrixSpencer.RealRAMKSLiveCoordinates
import MatrixSpencer.RealRAMKSNormReport
import MatrixSpencer.RealRAMProgram

/-! Primitive source weighting, local motion, and boundary preparation.
Boundary rounding is an explicit branching real-RAM program that updates
only the coefficient array. -/
open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.RuntimeGeometry
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open SeamlessKS.State SeamlessKS.Parameters SeamlessKS.Walk
open MatrixSpencer.KSLiveEnumeration (count liveEquiv)
attribute [local instance] Classical.propDecidable
variable {N d : ℕ} {ρ : ℝ}

def weights (s : WalkState N) : Counted (Fin (count s.coeff) → ℝ) :=
  let labels := KSLiveCoordinates.table s.coeff
  ⟨fun i => match labels.value[i.val]? with
      | none => 0
      | some j => SourceEvaluation.diagonalExpr.eval
        (SourceEvaluation.registers (s.coeff j) (zeta N)),
    labels.cost+count s.coeff*(N+30)+1⟩

theorem weights_value (s : WalkState N) : (weights s).value=liveWeights s := by
  funext i
  simp only [weights,KSLiveCoordinates.table_value]
  rw [List.getElem?_eq_getElem i.isLt]
  simp only [SourceEvaluation.diagonalExpr_eval]
  rfl

theorem weights_execution (s : WalkState N) (i : Fin (count s.coeff)) :
    Expr.Executes (SourceEvaluation.registers (s.coeff (liveEquiv s.coeff i)) (zeta N))
      SourceEvaluation.diagonalExpr (liveWeights s i) 26 :=
  SourceEvaluation.diagonal_executes (coeff_abs_le s.toCubeState _)

theorem weights_cost (s : WalkState N) : (weights s).cost≤50*(N+1)^2 := by
  have hh := KSLiveCoordinates.count_le s.coeff
  change (KSLiveCoordinates.table s.coeff).cost+count s.coeff*(N+30)+1≤50*(N+1)^2
  rw [KSLiveCoordinates.table_cost]
  nlinarith

def sourceRegisters : Fin 2 → Fin 4 := fun i => ⟨i.val,by omega⟩
def movementExpr : Expr (Fin 4) := .add (.input 0) (.mul (.input 3)
  (.mul (SourceEvaluation.relabel sourceRegisters SourceEvaluation.diagonalExpr) (.input 2)))
def movementInput (x ζ v t : ℝ) : Fin 4 → ℝ := ![x,ζ,v,t]

theorem movementInput_source (x ζ v t : ℝ) :
    movementInput x ζ v t ∘ sourceRegisters=SourceEvaluation.registers x ζ := by
  funext i
  fin_cases i <;> rfl

theorem movementExpr_eval (x ζ v t : ℝ) :
    movementExpr.eval (movementInput x ζ v t)=x+t*(Real.sqrt (Source.weight 64 ζ x/64)*v) := by
  simp only [movementExpr,Expr.eval,SourceEvaluation.relabel_eval,movementInput_source,
    SourceEvaluation.diagonalExpr_eval]
  rfl

theorem movementExpr_valid {x : ℝ} (hx : |x|≤1) (ζ v t : ℝ) :
    movementExpr.Valid (movementInput x ζ v t) := by
  refine ⟨trivial,trivial,?_,trivial⟩
  rw [SourceEvaluation.relabel_valid,movementInput_source]
  exact SourceEvaluation.diagonalExpr_valid hx

theorem movementExpr_cost : movementExpr.cost=32 := by decide

def movement (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin N)) (ζ t : ℝ) : Counted (Fin N → ℝ) :=
  ⟨fun i => movementExpr.eval (movementInput (x i) ζ (v i) t),N*(movementExpr.cost+8)+1⟩

theorem movement_value (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin N)) (ζ t : ℝ) :
    (movement x v ζ t).value=Progress.proposal x (State.weights ζ x) v t := by
  funext i
  exact movementExpr_eval _ _ _ _

theorem movement_execution {x : Fin N → ℝ} (hx : x∈ksCube 1)
    (v : EuclideanSpace ℝ (Fin N)) (ζ t : ℝ) (i : Fin N) :
    Expr.Executes (movementInput (x i) ζ (v i) t) movementExpr
      (Progress.proposal x (State.weights ζ x) v t i) 32 := by
  have he := Expr.executes_of_valid _ movementExpr
    (movementExpr_valid (abs_le.mpr ⟨hx.1 i,hx.2 i⟩) ζ (v i) t)
  rw [movementExpr_eval,movementExpr_cost] at he
  exact he

theorem movement_cost (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin N)) (ζ t : ℝ) :
    (movement x v ζ t).cost=40*N+1 := by
  simp only [movement,movementExpr_cost]
  omega

def terminalTest (s : CubeState N ρ) : Counted Bool :=
  let q := KSNormReport.signScan s.coeff (List.finRange N)
  ⟨q.value,q.cost+3*N+1⟩

theorem terminalTest_value (s : CubeState N ρ) :
    (terminalTest s).value=decide (State.terminal s) := by
  apply Bool.eq_iff_iff.mpr
  simp only [terminalTest,KSNormReport.signScan_value,List.all_eq_true,Bool.or_eq_true,
    decide_eq_true_eq]
  change (∀ i∈List.finRange N, s.coeff i=1 ∨ s.coeff i= -1) ↔ State.terminal s
  simpa only [List.mem_finRange,true_implies] using (State.terminal_iff_signing s).symm

theorem terminalTest_cost (s : CubeState N ρ) : (terminalTest s).cost=12*N+2 := by
  simp only [terminalTest,KSNormReport.signScan_cost,List.length_finRange]
  omega

def marginExpr : Expr (Fin 4) :=
  .sub (.constant 1) (SourceEvaluation.relabel (fun _ : Unit => (0:Fin 4)) KSNormReport.absExpr)

theorem marginExpr_eval (r : Fin 4 → ℝ) : marginExpr.eval r=1-|r 0| := by
  simp only [marginExpr,Expr.eval,Rat.cast_one,SourceEvaluation.relabel_eval]
  exact congrArg (fun z : ℝ => 1-z) (KSNormReport.absExpr_eval (r 0))

def snapProgram : Program (Fin 4) :=
  .branchLE marginExpr (.input 1)
    (.branchLE (.constant 0) (.input 0) (.assign 2 (.constant 1)) (.assign 2 (.constant (-1))))
    (.assign 2 (.input 0))

def snapInput (x ρ : ℝ) : Fin 4 → ℝ := ![x,ρ,0,0]

theorem marginExpr_valid (r : Fin 4 → ℝ) : marginExpr.Valid r := by
  refine ⟨trivial,?_⟩
  rw [SourceEvaluation.relabel_valid]
  exact ⟨⟨trivial,trivial⟩,mul_self_nonneg _⟩

theorem snapProgram_safe (r : Fin 4 → ℝ) : snapProgram.Safe r := by
  refine ⟨marginExpr_valid r,trivial,?_⟩
  split_ifs
  · exact ⟨trivial,trivial,by split_ifs <;> trivial⟩
  · trivial

theorem snapProgram_output (x ρ : ℝ) :
    (snapProgram.run (snapInput x ρ)) 2=
      if 1-|x|≤ρ then KSCubePreparation.endpoint 1 x else x := by
  simp [snapProgram,Program.run,marginExpr_eval,snapInput,Expr.eval,KSCubePreparation.endpoint]
  split_ifs <;> simp

theorem snapProgram_bound : snapProgram.bound≤30 := by decide

/-- Preparation materializes a single new coefficient array. -/
def prepareArrays (s : CubeState N ρ) : Counted (Fin N → ℝ) :=
  let runs := fun i => snapProgram.run (snapInput (s.coeff i) ρ)
  ⟨fun i => runs i 2,
    (∑ i,snapProgram.cost (snapInput (s.coeff i) ρ))+8*N+1⟩

theorem prepareArrays_coeff (hρ : 0≤ρ) (s : CubeState N ρ) :
    (prepareArrays s).value=(State.prepare hρ s).coeff := by
  funext i
  exact snapProgram_output _ _

theorem prepareArrays_execution (s : CubeState N ρ) (i : Fin N) :
    ∃ q k, Program.Executes snapProgram (snapInput (s.coeff i) ρ) q k ∧
      q 2=(prepareArrays s).value i ∧ k≤30 := by
  let r := snapInput (s.coeff i) ρ
  exact ⟨snapProgram.run r,snapProgram.cost r,
    Program.executes_of_safe snapProgram r (snapProgram_safe r),rfl,
    (Program.cost_le_bound snapProgram r).trans snapProgram_bound⟩

theorem prepareArrays_cost (s : CubeState N ρ) : (prepareArrays s).cost≤38*N+1 := by
  have hs : (∑ i,snapProgram.cost (snapInput (s.coeff i) ρ))≤30*N := by
    calc
      _ ≤ ∑ _i : Fin N,30 := Finset.sum_le_sum (fun i _ =>
        (Program.cost_le_bound snapProgram _).trans snapProgram_bound)
      _ = _ := by simp; omega
  change (∑ i,snapProgram.cost (snapInput (s.coeff i) ρ))+8*N+1≤38*N+1
  omega

def prepareCounted (hρ : 0≤ρ) (s : CubeState N ρ) : Counted (PreparedState N ρ) :=
  let a := prepareArrays s
  let canonical := State.prepare hρ s
  let hc := prepareArrays_coeff hρ s
  let result : PreparedState N ρ := {
    coeff := a.value
    cube := hc.symm ▸ canonical.cube
    rho_nonneg := hρ
    margin := by rw [hc]; exact canonical.margin }
  ⟨result,a.cost+1⟩

theorem prepareCounted_value (hρ : 0≤ρ) (s : CubeState N ρ) :
    (prepareCounted hρ s).value=State.prepare hρ s := by
  have hc := prepareArrays_coeff hρ s
  have hext (a b : PreparedState N ρ) (hx : a.coeff=b.coeff) : a=b := by
    cases a with
    | mk ac am =>
      cases b with
      | mk bc bm =>
        suffices he : ac=bc by cases he; rfl
        cases ac
        cases bc
        simp_all only
  exact hext _ _ hc

theorem prepareCounted_cost (hρ : 0≤ρ) (s : CubeState N ρ) :
    (prepareCounted hρ s).cost≤38*N+2 := by
  have hh := prepareArrays_cost s
  change (prepareArrays s).cost+1≤_
  omega

def initialCube (hρ : 0≤ρ) : Counted (CubeState N ρ) :=
  let z : Fin N → ℝ := fun _ => (Expr.constant 0 : Expr Unit).eval (fun _ => 0)
  ⟨{ coeff := z
     cube := by simpa only [z,Expr.eval,Rat.cast_zero] using (State.initial (N:=N) hρ).cube
     rho_nonneg := hρ },6*N+1⟩

theorem initialCube_value (hρ : 0≤ρ) : (initialCube (N:=N) hρ).value=State.initial hρ := by
  simp [initialCube,Expr.eval,State.initial]
  rfl

theorem initialCube_execution (hρ : 0≤ρ) (i : Fin N) :
    Expr.Executes (fun _ : Unit => (0:ℝ)) (.constant 0) ((initialCube hρ).value.coeff i) 1 := by
  exact Expr.executes_of_valid _ _ trivial

def initialCounted (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) : Counted (WalkState N) :=
  let hr := (rho_pos (Input.labels_pos v hd hp)).le
  let z := initialCube (N:=N) hr
  let p := prepareCounted hr z.value
  ⟨p.value,z.cost+p.cost+1⟩

theorem initialCounted_value (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) :
    (initialCounted v hd hp).value=Walk.initial v hd hp := by
  simp only [initialCounted,prepareCounted_value,initialCube_value]
  rfl

theorem initialCounted_cost (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) : (initialCounted v hd hp).cost≤44*N+4 := by
  have hh := prepareCounted_cost (rho_pos (Input.labels_pos v hd hp)).le
    (initialCube (N:=N) (rho_pos (Input.labels_pos v hd hp)).le).value
  change (6*N+1)+(prepareCounted (rho_pos (Input.labels_pos v hd hp)).le
    (initialCube (N:=N) (rho_pos (Input.labels_pos v hd hp)).le).value).cost+1≤44*N+4
  omega

end SeamlessKS.RuntimeGeometry
