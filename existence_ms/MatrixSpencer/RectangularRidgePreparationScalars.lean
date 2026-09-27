import MatrixSpencer.RectangularRidgeResponseMagnitude
import MatrixSpencer.RectangularRidgeNumericalSetup
import MatrixSpencer.RealRAMMSLoopCapSetup

/-! Primitive setup of the literal natural cleanup, top-response and paid
iteration caps, together with the real paid step. Powers are expanded into
fixed multiplication chains; no ceiling or logarithm is an input operation. -/
noncomputable section
namespace MatrixSpencer.RectangularRidgePreparationScalars
open RealRAM
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
open RealRAM.JacobiIteration (Counted)
open RectangularRidgeResponseMagnitude
abbrev E := NatExpr (Fin 2)
local instance ridgePreparationScalarsAdd : Add E := ⟨NatExpr.add⟩
local instance ridgePreparationScalarsMul : Mul E := ⟨NatExpr.mul⟩
def c (v : ℕ) : E := .constant v
def labels : E := .input 0
def dimension : E := .input 1
def power (x : E) (k : ℕ) := NatExpr.power x k
def sizeExpr : E := dimension+labels+c 2
def jacobiExpr (v z : E) : E := (power labels 2+c 1)*power labels 2*power v 2*power z 2+c 1
def cleanupExpr : E := jacobiExpr (c 1) (c 131072*(labels+c 1))
def topExpr : E := jacobiExpr (c (2^332)*power sizeExpr 63) (c 64*sizeExpr)
def fuelExpr : E := c (2^320)*power sizeExpr 63+c 1

def input (N d : ℕ) : Fin 2→ℕ := ![N,d]

@[simp] theorem add_eval (a b : E) (v : Fin 2→ℕ) : (a+b).eval v=a.eval v+b.eval v := rfl
@[simp] theorem mul_eval (a b : E) (v : Fin 2→ℕ) : (a*b).eval v=a.eval v*b.eval v := rfl
@[simp] theorem power_eval (a : E) (k : ℕ) (v : Fin 2→ℕ) : (power a k).eval v=(a.eval v)^k := NatExpr.power_eval _ _ _
@[simp] theorem c_eval (x : ℕ) (v : Fin 2→ℕ) : (c x).eval v=x := rfl
@[simp] theorem labels_eval (N d : ℕ) : labels.eval (input N d)=N := rfl
@[simp] theorem dimension_eval (N d : ℕ) : dimension.eval (input N d)=d := rfl

structure Values where
  cleanup : ℕ
  top : ℕ
  fuel : ℕ
  paid : ℝ

def compute (N d : ℕ) : Counted Values :=
  let paid:=RectangularRidgeNumericalSetup.smallExpr 320 62
  ⟨⟨cleanupExpr.eval (input N d),topExpr.eval (input N d),fuelExpr.eval (input N d),
    paid.eval ![(d:ℝ),N]⟩,cleanupExpr.cost+topExpr.cost+fuelExpr.cost+paid.cost+4⟩

theorem compute_value (N d : ℕ) : (compute N d).value=
    ⟨MSManuscriptPolynomialQueryCleanup.cleanupJacobi N,topBudget N d,
      2^320*(d+N+2)^63+1,RectangularRidgeNumericalParameters.paidStep
        (RectangularRidgeNumericalOptimizerFloor.size d N)⟩ := by
  simp only [compute,cleanupExpr,topExpr,fuelExpr,jacobiExpr,add_eval,mul_eval,c_eval,
    power_eval,labels_eval,dimension_eval,sizeExpr,RectangularRidgeNumericalSetup.smallExpr_eval,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  rfl

theorem natural_execution (N d : ℕ) (e : E) :
    NatExpr.Executes (input N d) e (e.eval (input N d)) e.cost := NatExpr.executes _ _

theorem real_execution (N d : ℕ) (e : E) :
    Expr.Executes (fun i=>(input N d i:ℝ)) e.toRealExpr
      (e.eval (input N d):ℝ) e.cost := NatExpr.real_executes e (input N d)

theorem paid_execution (N d : ℕ) :
    Expr.Executes ![(d:ℝ),N] (RectangularRidgeNumericalSetup.smallExpr 320 62)
      (compute N d).value.paid (RectangularRidgeNumericalSetup.smallExpr 320 62).cost :=
  Expr.executes_of_valid _ _ (RectangularRidgeNumericalSetup.smallExpr_valid 320 62 _
    (by simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one];positivity))

theorem compute_cost (N d : ℕ) : (compute N d).cost≤10000 := by
  change cleanupExpr.cost+topExpr.cost+fuelExpr.cost+(RectangularRidgeNumericalSetup.smallExpr 320 62).cost+4≤10000
  decide

end MatrixSpencer.RectangularRidgePreparationScalars
