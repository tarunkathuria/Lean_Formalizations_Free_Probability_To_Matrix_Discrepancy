import MatrixSpencer.RealRAMMSParameterTables
import MatrixSpencer.MSConvexPolynomialTangentParameters

/-! Fixed safe real scalar circuits after the entry-budget tables. Registers
hold epoch size, positive owner dimension, secondCap+1, curvature budget,
fourth budget, original label count+1, and physical dimension. -/
open Matrix
noncomputable section
namespace MatrixSpencer.RealRAM.MSScalarFormulas
open JacobiIteration (Counted)
abbrev Reg := Fin 7
abbrev Formula := PositiveFormula Reg
local instance : Add Formula := ⟨PositiveFormula.add⟩
local instance : Mul Formula := ⟨PositiveFormula.mul⟩
local instance : Div Formula := ⟨PositiveFormula.div⟩
def c (n : ℕ) (h : 0<n := by decide) : Formula := .constant n (by exact_mod_cast h)
def r (i : Reg) : Formula := .input i
def sq (a : Formula) := a*a
def root (a : Formula) := PositiveFormula.sqrt a
def least (a b : Formula) := PositiveFormula.minimum a b
@[simp] theorem c_eval (n : ℕ) (h : 0<n) (v : Reg→ℝ) : (c n h).eval v=n := by simp [c]
@[simp] theorem r_eval (i : Reg) (v : Reg→ℝ) : (r i).eval v=v i := rfl
@[simp] theorem add_eval (a b : Formula) (v : Reg→ℝ) : (a+b).eval v=a.eval v+b.eval v := rfl
@[simp] theorem mul_eval (a b : Formula) (v : Reg→ℝ) : (a*b).eval v=a.eval v*b.eval v := rfl
@[simp] theorem div_eval (a b : Formula) (v : Reg→ℝ) : (a/b).eval v=a.eval v/b.eval v := rfl
@[simp] theorem sq_eval (a : Formula) (v : Reg→ℝ) : (sq a).eval v=(a.eval v)^2 := by simp [sq,pow_two]
@[simp] theorem root_eval (a : Formula) (v : Reg→ℝ) : (root a).eval v=Real.sqrt (a.eval v) := rfl
@[simp] theorem least_eval (a b : Formula) (v : Reg→ℝ) : (least a b).eval v=min (a.eval v) (b.eval v) := PositiveFormula.eval_minimum _ _ _

def threshold := c 4096/root (r 0)
def margin := c 1/(c 1000*r 5)
def eta := threshold/(c 128*r 1)
def spacing := least (c 1/c 32768) (eta/r 2)
def precision := eta*spacing/c 4
def paid := least (c 1/c 32768) (threshold/(c 4*r 3))
def matchedRadius := least (c 1/c 2) (root (c 1/c 8192)/c 2)
def movement := least (margin/root (r 0+c 1))
  (least (c 1/c 2) (least (matchedRadius/c 2) (root (c 24/(c 10000*r 4)))))
def mesh := least movement (root (c 1/c 3078))
def preparationArgument := r 0/paid
def movementArgument := c 1/(c 1539*sq mesh)
def acceptanceTolerance := root (r 0)/c 100
def acceptanceRadius := root (r 6)*(c 2*r 0+margin*r 0)
def tangentSpacing := acceptanceTolerance/(c 6*(c 2*sq acceptanceRadius+c 1))
def tangentPrecision := acceptanceTolerance*tangentSpacing/c 6
def acceptancePrecision := acceptanceTolerance/c 3

def input (m k N d : ℕ) (L C F : ℝ) : Reg→ℝ := ![m,k,L+1,C,F,(N:ℝ)+1,d]

theorem input_pos (m k N d : ℕ) (L C F : ℝ) (hm : 0 < m) (hk : 0 < k) (hd : 0 < d)
    (hL : 0 ≤ L) (hC : 0 < C) (hF : 0 < F) : ∀i,0 < input m k N d L C F i := by
  intro i
  fin_cases i <;> simp [input] <;> positivity

def outputs : Fin 14→Formula := ![threshold,margin,eta,spacing,precision,paid,mesh,
  preparationArgument,movementArgument,acceptanceTolerance,acceptanceRadius,
  tangentSpacing,tangentPrecision,acceptancePrecision]
def circuit : Circuit Reg (Fin 14) := ⟨fun i => (outputs i).toExpr⟩
def compute (m k N d : ℕ) (L C F : ℝ) : Counted (Fin 14→ℝ) :=
  ⟨circuit.eval (input m k N d L C F),circuit.cost⟩

theorem execution (m k N d : ℕ) (L C F : ℝ) (hm : 0 < m) (hk : 0 < k) (hd : 0 < d)
    (hL : 0 ≤ L) (hC : 0 < C) (hF : 0 < F) (i : Fin 14) :
    Expr.Executes (input m k N d L C F) (circuit.output i)
      ((compute m k N d L C F).value i) (circuit.output i).cost :=
  PositiveFormula.executes _ _ (input_pos m k N d L C F hm hk hd hL hC hF)

theorem cost : circuit.cost≤100000 := by decide
theorem compute_cost (m k N d : ℕ) (L C F : ℝ) : (compute m k N d L C F).cost≤100000 := cost

theorem threshold_eval (m k N d : ℕ) (L C F : ℝ) :
    threshold.eval (input m k N d L C F)=4096/Real.sqrt (m:ℝ) := by simp [threshold,input]
theorem margin_eval (m k N d : ℕ) (L C F : ℝ) :
    margin.eval (input m k N d L C F)=1/(1000*((N:ℝ)+1)) := by simp [margin,input]
theorem eta_eval (m k N d : ℕ) (L C F : ℝ) :
    eta.eval (input m k N d L C F)=MSManuscriptGammaMatrix.topPrecision k (4096/Real.sqrt (m:ℝ)) := by
  simp [eta,threshold,input,MSManuscriptGammaMatrix.topPrecision]
theorem spacing_eval (m k N d : ℕ) (L C F : ℝ) :
    spacing.eval (input m k N d L C F)=MSManuscriptGammaDifference.stepSize (1/8192) L
      (MSManuscriptGammaMatrix.topPrecision k (4096/Real.sqrt (m:ℝ))) := by
  simp [spacing,eta,threshold,input,MSManuscriptGammaDifference.stepSize,MSManuscriptGammaMatrix.topPrecision]
  norm_num

theorem precision_eval (m k N d : ℕ) (L C F : ℝ) :
    precision.eval (input m k N d L C F)=MSManuscriptGammaDifference.valueTolerance (1/8192) L
      (MSManuscriptGammaMatrix.topPrecision k (4096/Real.sqrt (m:ℝ))) := by
  simp [precision,eta_eval,spacing_eval,MSManuscriptGammaDifference.valueTolerance]

theorem paid_eval (m k N d : ℕ) (L C F : ℝ) :
    paid.eval (input m k N d L C F)=min ((1/8192)/4) ((4096/Real.sqrt (m:ℝ))/(4*C)) := by
  simp [paid,threshold,input]
  norm_num

theorem mesh_eval (m k N d : ℕ) (L C F : ℝ) :
    mesh.eval (input m k N d L C F)=
    min (min ((1/(1000*((N:ℝ)+1)))/Real.sqrt ((m:ℝ)+1))
      (min (1/2) (min (MSManuscriptMatchedInterval.radius (1/8192)/2)
        (Real.sqrt (24*(1/10000)/F))))) (Real.sqrt (MSManuscriptNumericalEpochLedger.timeLimit/2)) := by
  simp only [mesh,movement,margin,matchedRadius,least_eval,div_eval,root_eval,mul_eval,
    add_eval,c_eval,r_eval,input,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.head_fin_const,MSManuscriptMatchedInterval.radius,
    MSManuscriptNumericalEpochLedger.timeLimit]
  norm_num only
  congr 2
  congr 1
  congr 1
  congr 1
  norm_num [Matrix.cons_val] <;> ring_nf <;> rfl

theorem acceptanceTolerance_eval (m k N d : ℕ) (L C F : ℝ) :
    acceptanceTolerance.eval (input m k N d L C F)=Real.sqrt (m:ℝ)/100 := by
  simp [acceptanceTolerance,input]
theorem acceptanceRadius_eval (m k N d : ℕ) (L C F : ℝ) :
    acceptanceRadius.eval (input m k N d L C F)=MSManuscriptInputRadius.radius m d
      ((1/(1000*((N:ℝ)+1)))*(m:ℝ)) := by
  simp [acceptanceRadius,margin,input,MSManuscriptInputRadius.radius]
theorem tangentSpacing_eval (v : Reg→ℝ) :
    tangentSpacing.eval v=MSConvexAnchorTangent.spacing 1 (acceptanceRadius.eval v) (acceptanceTolerance.eval v) := by
  simp [tangentSpacing,MSConvexAnchorTangent.spacing,MSConvexAnchorTangent.curvature]
theorem tangentPrecision_eval (v : Reg→ℝ) :
    tangentPrecision.eval v=MSConvexAnchorTangent.precision 1 (acceptanceRadius.eval v) (acceptanceTolerance.eval v) := by
  simp [tangentPrecision,tangentSpacing_eval,MSConvexAnchorTangent.precision]

end MatrixSpencer.RealRAM.MSScalarFormulas
