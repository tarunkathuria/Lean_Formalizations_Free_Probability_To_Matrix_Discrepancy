import MatrixSpencer.KSConvexQueryBudgets
import MatrixSpencer.RealRAMKSNormReport

/-! Exact construction of the five natural loop caps. Powers here expand
into literal finite chains of multiplication; they are not machine
primitives. Natural arithmetic uses the real-RAM integer registers, and the
same instruction tree is also lowered to the existing real scalar language.
The operation count is independent of the magnitudes of the resulting caps. -/
open scoped BigOperators
namespace MatrixSpencer.RealRAM

inductive NatExpr (ι : Type*) where
  | input : ι→NatExpr ι
  | constant : ℕ→NatExpr ι
  | add : NatExpr ι→NatExpr ι→NatExpr ι
  | mul : NatExpr ι→NatExpr ι→NatExpr ι

namespace NatExpr
variable {ι : Type*}
def eval (v : ι→ℕ) : NatExpr ι→ℕ
  | .input i=>v i
  | .constant c=>c
  | .add a b=>a.eval v+b.eval v
  | .mul a b=>a.eval v*b.eval v

def cost : NatExpr ι→ℕ
  | .input _ | .constant _=>1
  | .add a b | .mul a b=>a.cost+b.cost+1

def toRealExpr : NatExpr ι→Expr ι
  | .input i=>.input i
  | .constant c=>.constant c
  | .add a b=>.add a.toRealExpr b.toRealExpr
  | .mul a b=>.mul a.toRealExpr b.toRealExpr

@[simp] theorem toRealExpr_eval (e : NatExpr ι) (v : ι→ℕ) :
    e.toRealExpr.eval (fun i=>(v i : ℝ))=(e.eval v : ℝ) := by
  induction e <;> simp_all [toRealExpr,Expr.eval,eval]
@[simp] theorem toRealExpr_cost (e : NatExpr ι) : e.toRealExpr.cost=e.cost := by
  induction e <;> simp_all [toRealExpr,Expr.cost,cost]
theorem toRealExpr_valid (e : NatExpr ι) (v : ι→ℝ) : e.toRealExpr.Valid v := by
  induction e <;> simp_all [toRealExpr,Expr.Valid]

inductive Executes (v : ι→ℕ) : NatExpr ι→ℕ→ℕ→Prop where
  | input (i : ι) : Executes v (.input i) (v i) 1
  | constant (c : ℕ) : Executes v (.constant c) c 1
  | add {a b : NatExpr ι} {x y ka kb : ℕ} : Executes v a x ka→Executes v b y kb→
      Executes v (.add a b) (x+y) (ka+kb+1)
  | mul {a b : NatExpr ι} {x y ka kb : ℕ} : Executes v a x ka→Executes v b y kb→
      Executes v (.mul a b) (x*y) (ka+kb+1)

theorem executes (e : NatExpr ι) (v : ι→ℕ) : Executes v e (e.eval v) e.cost := by
  induction e with
  | input i=>exact Executes.input i
  | constant c=>exact Executes.constant c
  | add a b ha hb=>exact Executes.add ha hb
  | mul a b ha hb=>exact Executes.mul ha hb

theorem real_executes (e : NatExpr ι) (v : ι→ℕ) :
    Expr.Executes (fun i=>(v i:ℝ)) e.toRealExpr (e.eval v:ℝ) e.cost := by
  simpa using Expr.executes_of_valid (fun i=>(v i:ℝ)) e.toRealExpr (toRealExpr_valid _ _)

/-- Repeated multiplication is expanded as a finite instruction tree. -/
def power (e : NatExpr ι) : ℕ→NatExpr ι
  | 0=>.constant 1
  | k+1=>.mul (power e k) e
@[simp] theorem power_eval (e : NatExpr ι) (k : ℕ) (v : ι→ℕ) :
    (power e k).eval v=(e.eval v)^k := by induction k <;> simp_all [power,eval,pow_succ]
@[simp] theorem power_cost (e : NatExpr ι) (k : ℕ) : (power e k).cost=1+k*(e.cost+1) := by
  induction k <;> simp_all [power,cost] <;> ring
end NatExpr

namespace KSLoopCapSetup
open NatExpr
open JacobiIteration (Counted)
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def n : NatExpr (Fin 2) := .input 0
def d : NatExpr (Fin 2) := .input 1
def base : NatExpr (Fin 2) := .mul (.constant 100000) (.add (.add n d) (.constant 1))
def taylor : NatExpr (Fin 2) := power base 275
def fullQuery : NatExpr (Fin 2) := .add (.mul (.constant 32) (power n 2))
  (.mul (.mul (.constant 800) (power n 3)) taylor)
def fullEntry : NatExpr (Fin 2) := .mul (.mul (.constant 4) (.add base (.constant 1))) fullQuery
def fullKappa : NatExpr (Fin 2) := .mul (.constant 100) (power n 2)
def eighthQuery : NatExpr (Fin 2) := .add (.constant 1024)
  (.mul (.mul (.constant 1000000) taylor) (power n 5))
def eighthEntry : NatExpr (Fin 2) := .mul (.add base (.constant 1)) eighthQuery
def eighthScaledEntry : NatExpr (Fin 2) := .mul (.mul (.constant 10000) (power n 3)) eighthEntry
def eighthBeta : NatExpr (Fin 2) := .mul (.mul (.constant 1000000) (power n 4)) (.add taylor (.constant 1))
def jacobi (n v k : NatExpr (Fin 2)) : NatExpr (Fin 2) :=
  .add (.mul (.mul (.mul (.add (power n 2) (.constant 1)) (power n 2)) (power v 2)) (power k 2)) (.constant 1)
def fullJacobi : NatExpr (Fin 2) := jacobi n fullEntry fullKappa
def eighthJacobi : NatExpr (Fin 2) := jacobi n eighthScaledEntry eighthBeta
def normCap : NatExpr (Fin 2) := jacobi (.add d d) n (.mul (.constant 4) n)
def fullHorizon : NatExpr (Fin 2) := .add (.add (.mul (.constant 256) (power n 3))
  (.mul (.mul (.constant 100) (power n 3)) taylor)) (.constant 1)
def eighthHorizon : NatExpr (Fin 2) := .add
  (.mul (.mul (.constant 4000000) n) (.add (.add (power n 5) (.mul taylor (power n 4))) (.constant 1)))
  (.constant 1)

def input (N D : ℕ) : Fin 2→ℕ := ![N,D]
@[simp] theorem n_eval (N D : ℕ) : n.eval (input N D)=N := rfl
@[simp] theorem d_eval (N D : ℕ) : d.eval (input N D)=D := rfl

@[simp] theorem base_eval (N D : ℕ) : base.eval (input N D)=KSJacobiPolynomialBounds.base N D := rfl
@[simp] theorem taylor_eval (N D : ℕ) : taylor.eval (input N D)=KSJacobiPolynomialBounds.taylor N D := by
  simp [taylor,KSJacobiPolynomialBounds.taylor]
@[simp] theorem fullQuery_eval (N D : ℕ) : fullQuery.eval (input N D)=KSJacobiPolynomialBounds.fullQuery N D := by
  simp [fullQuery,eval,KSJacobiPolynomialBounds.fullQuery]
@[simp] theorem fullEntry_eval (N D : ℕ) : fullEntry.eval (input N D)=KSJacobiPolynomialBounds.fullEntry N D := by
  simp [fullEntry,eval,KSJacobiPolynomialBounds.fullEntry]
@[simp] theorem fullKappa_eval (N D : ℕ) : fullKappa.eval (input N D)=KSJacobiPolynomialBounds.fullKappa N := by
  simp [fullKappa,eval,KSJacobiPolynomialBounds.fullKappa]
@[simp] theorem eighthQuery_eval (N D : ℕ) : eighthQuery.eval (input N D)=KSJacobiPolynomialBounds.eighthQuery N D := by
  simp [eighthQuery,eval,KSJacobiPolynomialBounds.eighthQuery]
@[simp] theorem eighthEntry_eval (N D : ℕ) : eighthEntry.eval (input N D)=KSJacobiPolynomialBounds.eighthEntry N D := by
  simp [eighthEntry,eval,KSJacobiPolynomialBounds.eighthEntry]
@[simp] theorem eighthScaledEntry_eval (N D : ℕ) : eighthScaledEntry.eval (input N D)=KSJacobiPolynomialBounds.eighthScaledEntry N D := by
  simp [eighthScaledEntry,eval,KSJacobiPolynomialBounds.eighthScaledEntry]
@[simp] theorem eighthBeta_eval (N D : ℕ) : eighthBeta.eval (input N D)=KSJacobiPolynomialBounds.eighthBeta N D := by
  simp [eighthBeta,eval,KSJacobiPolynomialBounds.eighthBeta]
@[simp] theorem jacobi_eval (n v k : NatExpr (Fin 2)) (x : Fin 2→ℕ) :
    (jacobi n v k).eval x = KSJacobiPolynomialBounds.jacobi (n.eval x) (v.eval x) (k.eval x) := by
  simp [jacobi,eval,KSJacobiPolynomialBounds.jacobi]
@[simp] theorem fullJacobi_eval (N D : ℕ) : fullJacobi.eval (input N D)=KSJacobiPolynomialBounds.fullJacobi N D := by
  simp [fullJacobi,KSJacobiPolynomialBounds.fullJacobi,eval]
@[simp] theorem eighthJacobi_eval (N D : ℕ) : eighthJacobi.eval (input N D)=KSJacobiPolynomialBounds.eighthJacobi N D := by
  simp [eighthJacobi,KSJacobiPolynomialBounds.eighthJacobi,eval]
@[simp] theorem normCap_eval (N D : ℕ) : normCap.eval (input N D)=KSNormReport.normCap N D := by
  simp [normCap,KSNormReport.normCap,eval]
@[simp] theorem fullHorizon_eval (N D : ℕ) : fullHorizon.eval (input N D)=KSConvexQueryBudgets.fullHorizon N D := by
  simp [fullHorizon,KSConvexQueryBudgets.fullHorizon,eval]
@[simp] theorem eighthHorizon_eval (N D : ℕ) : eighthHorizon.eval (input N D)=KSConvexQueryBudgets.eighthHorizon N D := by
  simp [eighthHorizon,KSConvexQueryBudgets.eighthHorizon,eval]

def outputs : Fin 5→NatExpr (Fin 2) := ![fullJacobi,eighthJacobi,normCap,fullHorizon,eighthHorizon]
def originalOutputs (N D : ℕ) : Fin 5→ℕ := ![KSJacobiPolynomialBounds.fullJacobi N D,
  KSJacobiPolynomialBounds.eighthJacobi N D,KSNormReport.normCap N D,
  KSConvexQueryBudgets.fullHorizon N D,KSConvexQueryBudgets.eighthHorizon N D]

theorem outputs_eval (N D : ℕ) (i : Fin 5) : (outputs i).eval (input N D)=originalOutputs N D i := by
  fin_cases i <;> simp [outputs,originalOutputs]

def circuit : Circuit (Fin 2) (Fin 5) := ⟨fun i=>(outputs i).toRealExpr⟩
theorem circuit_value (N D : ℕ) (i : Fin 5) :
    circuit.eval (fun i=>(input N D i:ℝ)) i=(originalOutputs N D i:ℝ) := by
  simp [Circuit.eval,circuit,outputs_eval]
theorem circuit_execution (N D : ℕ) (i : Fin 5) :
    Expr.Executes (fun i=>(input N D i:ℝ)) (circuit.output i)
      (originalOutputs N D i:ℝ) (circuit.output i).cost := by
  simpa [circuit,outputs_eval] using NatExpr.real_executes (outputs i) (input N D)

def compute (N D : ℕ) : Counted (Fin 5→ℕ) :=
  ⟨fun i=>(outputs i).eval (input N D),circuit.cost⟩
theorem compute_value (N D : ℕ) : (compute N D).value=originalOutputs N D := funext (outputs_eval N D)
theorem compute_execution (N D : ℕ) (i : Fin 5) :
    NatExpr.Executes (input N D) (outputs i) ((compute N D).value i) (outputs i).cost := NatExpr.executes _ _

theorem circuit_cost : circuit.cost≤100000 := by decide
theorem compute_cost (N D : ℕ) : (compute N D).cost≤100000 := circuit_cost

end KSLoopCapSetup
end MatrixSpencer.RealRAM
