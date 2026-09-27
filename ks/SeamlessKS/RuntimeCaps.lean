import SeamlessKS.RuntimeBudgets
import MatrixSpencer.RealRAMKSLoopCapSetup

/-! Primitive arithmetic formation of every natural polynomial cap used by
the seamless implementation. Powers expand into fixed multiplication trees,
and the natural expressions also execute in the real arithmetic language. -/
namespace SeamlessKS.RuntimeCaps
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev Formula := NatExpr (Fin 2)
local instance : Add Formula := ⟨NatExpr.add⟩
local instance : Mul Formula := ⟨NatExpr.mul⟩
def c (n : ℕ) : Formula := .constant n
def n : Formula := .input 0
def dim : Formula := .input 1
def sq (a : Formula) := NatExpr.power a 2
def fourth (a : Formula) := NatExpr.power a 4
@[simp] theorem c_eval (k : ℕ) (x : Fin 2 → ℕ) : (c k).eval x=k := rfl
@[simp] theorem add_eval (a b : Formula) (x : Fin 2 → ℕ) : (a+b).eval x=a.eval x+b.eval x := rfl
@[simp] theorem mul_eval (a b : Formula) (x : Fin 2 → ℕ) : (a*b).eval x=a.eval x*b.eval x := rfl
@[simp] theorem sq_eval (a : Formula) (x : Fin 2 → ℕ) : (sq a).eval x=(a.eval x)^2 := NatExpr.power_eval _ _ _
@[simp] theorem fourth_eval (a : Formula) (x : Fin 2 → ℕ) : (fourth a).eval x=(a.eval x)^4 := NatExpr.power_eval _ _ _

def radiusInverse := c 10000*(c 1+c 22500*sq n)
def jointDerivative := c 10000*sq (c 2*dim+c 1)*fourth (c 10*radiusInverse)
def derivative := c 1+(jointDerivative+c 3*sq jointDerivative*(c 4*n))*
  fourth (c 1+jointDerivative*(c 4*n))
def queryInverseSquare := c 256*sq (c 100*sq n)+c 128*n*derivative*(c 100*sq n)
def movementInverseSquare := c 256*sq (c 100*sq n)+c 4*derivative*(c 100*sq n)
def hessianAccuracyInverse := c 128*n*(c 100*sq n)*queryInverseSquare
def localAccuracyInverse := c 8*(c 100*sq n)*movementInverseSquare
def horizon := c 16*n*movementInverseSquare+c 1
def entry := c 148*queryInverseSquare

def input (N d : ℕ) : Fin 2 → ℕ := ![N,d]
@[simp] theorem n_eval (N d : ℕ) : n.eval (input N d)=N := rfl
@[simp] theorem dim_eval (N d : ℕ) : dim.eval (input N d)=d := rfl
@[simp] theorem radiusInverse_eval (N d : ℕ) : radiusInverse.eval (input N d)=RuntimeBudgets.radiusInverseCap N := by simp [radiusInverse,RuntimeBudgets.radiusInverseCap]
@[simp] theorem jointDerivative_eval (N d : ℕ) : jointDerivative.eval (input N d)=RuntimeBudgets.jointDerivativeCap N d := by simp [jointDerivative,RuntimeBudgets.jointDerivativeCap]
@[simp] theorem derivative_eval (N d : ℕ) : derivative.eval (input N d)=RuntimeBudgets.derivativeCap N d := by simp [derivative,RuntimeBudgets.derivativeCap]
@[simp] theorem queryInverseSquare_eval (N d : ℕ) : queryInverseSquare.eval (input N d)=RuntimeBudgets.queryInverseSquareCap N d := by simp [queryInverseSquare,RuntimeBudgets.queryInverseSquareCap]
@[simp] theorem movementInverseSquare_eval (N d : ℕ) : movementInverseSquare.eval (input N d)=RuntimeBudgets.movementInverseSquareCap N d := by simp [movementInverseSquare,RuntimeBudgets.movementInverseSquareCap]
@[simp] theorem hessianAccuracyInverse_eval (N d : ℕ) : hessianAccuracyInverse.eval (input N d)=RuntimeBudgets.hessianAccuracyInverseCap N d := by simp [hessianAccuracyInverse,RuntimeBudgets.hessianAccuracyInverseCap]
@[simp] theorem localAccuracyInverse_eval (N d : ℕ) : localAccuracyInverse.eval (input N d)=RuntimeBudgets.localAccuracyInverseCap N d := by simp [localAccuracyInverse,RuntimeBudgets.localAccuracyInverseCap]
@[simp] theorem horizon_eval (N d : ℕ) : horizon.eval (input N d)=RuntimeBudgets.horizonCap N d := by simp [horizon,RuntimeBudgets.horizonCap]
@[simp] theorem entry_eval (N d : ℕ) : entry.eval (input N d)=RuntimeBudgets.entryCap N d := by simp [entry,RuntimeBudgets.entryCap]

def formulas : Fin 9 → Formula := ![radiusInverse,jointDerivative,derivative,
  queryInverseSquare,movementInverseSquare,hessianAccuracyInverse,localAccuracyInverse,
  horizon,entry]
def outputs (N d : ℕ) : Fin 9 → ℕ := ![RuntimeBudgets.radiusInverseCap N,
  RuntimeBudgets.jointDerivativeCap N d,RuntimeBudgets.derivativeCap N d,
  RuntimeBudgets.queryInverseSquareCap N d,RuntimeBudgets.movementInverseSquareCap N d,
  RuntimeBudgets.hessianAccuracyInverseCap N d,RuntimeBudgets.localAccuracyInverseCap N d,
  RuntimeBudgets.horizonCap N d,RuntimeBudgets.entryCap N d]

theorem formulas_eval (N d : ℕ) (i : Fin 9) : (formulas i).eval (input N d)=outputs N d i := by
  fin_cases i <;> simp [formulas,outputs]

def circuit : Circuit (Fin 2) (Fin 9) := ⟨fun i => (formulas i).toRealExpr⟩
theorem circuit_valid (x : Fin 2 → ℝ) : circuit.Valid x :=
  fun i => NatExpr.toRealExpr_valid (formulas i) x

theorem circuit_value (N d : ℕ) (i : Fin 9) :
    circuit.eval (fun i => (input N d i:ℝ)) i=(outputs N d i:ℝ) := by
  simp [circuit,Circuit.eval,formulas_eval]

theorem circuit_execution (N d : ℕ) (i : Fin 9) :
    Expr.Executes (fun i => (input N d i:ℝ)) (circuit.output i)
      (outputs N d i:ℝ) (circuit.output i).cost := by
  simpa [circuit,formulas_eval] using NatExpr.real_executes (formulas i) (input N d)

def compute (N d : ℕ) : Counted (Fin 9 → ℕ) :=
  ⟨fun i => (formulas i).eval (input N d),circuit.cost⟩
@[simp] theorem compute_value (N d : ℕ) : (compute N d).value=outputs N d :=
  funext (formulas_eval N d)
theorem compute_execution (N d : ℕ) (i : Fin 9) :
    NatExpr.Executes (input N d) (formulas i) ((compute N d).value i) (formulas i).cost :=
  NatExpr.executes _ _
theorem circuit_cost : circuit.cost≤1000000 := by decide
theorem compute_cost (N d : ℕ) : (compute N d).cost≤1000000 := circuit_cost

end SeamlessKS.RuntimeCaps
