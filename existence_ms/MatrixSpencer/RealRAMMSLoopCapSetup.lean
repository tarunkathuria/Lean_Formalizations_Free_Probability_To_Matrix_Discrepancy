import MatrixSpencer.RealRAMKSLoopCapSetup
import MatrixSpencer.MSManuscriptPolynomialQueryMagnitude
import MatrixSpencer.MSConvexPolynomialTangentParameters

/-! Explicit natural-register arithmetic for the polynomial square-MS loop
and accuracy caps. All powers expand into fixed chains of multiplication. -/
open Matrix
noncomputable section
namespace MatrixSpencer.RealRAM.MSLoopCapSetup
open JacobiIteration (Counted)
open MSManuscriptPolynomialQueryCurvature MSManuscriptPolynomialQueryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def movementUniform (N d : ℕ) : ℕ :=
  1+(N+1)*(joint N d+6*(joint N d)^2)*(1+2*joint N d)^4
def movementCap (N d : ℕ) : ℕ := 1000000*(N+1)^3+1000*movementUniform N d+200001

theorem movementUniform_cast (N d : ℕ) : (movementUniform N d:ℝ)=
    MSManuscriptPolynomialMovementBounds.uniform N d (center N d) := by
  simp only [movementUniform,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,cast_joint]
  unfold MSManuscriptPolynomialMovementBounds.uniform MSManuscriptPolynomialMovementBounds.fourth
  ring

theorem movementCap_cast (N d : ℕ) : (movementCap N d:ℝ)=
    MSManuscriptPolynomialMovementBounds.meshCap N d N N+1 := by
  simp only [movementCap,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
    Nat.cast_one,movementUniform_cast,cast_center,MSManuscriptPolynomialMovementBounds.meshCap]
  ring

abbrev E := NatExpr (Fin 2)
local instance : Add E := ⟨NatExpr.add⟩
local instance : Mul E := ⟨NatExpr.mul⟩
def c (n : ℕ) : E := .constant n
def n : E := .input 0
def d : E := .input 1
def pw (a : E) (k : ℕ) := NatExpr.power a k
@[simp] theorem add_eval (a b : E) (v : Fin 2→ℕ) : (a+b).eval v=a.eval v+b.eval v := rfl
@[simp] theorem mul_eval (a b : E) (v : Fin 2→ℕ) : (a*b).eval v=a.eval v*b.eval v := rfl
@[simp] theorem c_eval (a : ℕ) (v : Fin 2→ℕ) : (c a).eval v=a := rfl
@[simp] theorem pw_eval (a : E) (k : ℕ) (v : Fin 2→ℕ) : (pw a k).eval v=(a.eval v)^k := NatExpr.power_eval _ _ _
def input (N D : ℕ) : Fin 2→ℕ := ![N,D]
@[simp] theorem n_eval (N D : ℕ) : n.eval (input N D)=N := rfl
@[simp] theorem d_eval (N D : ℕ) : d.eval (input N D)=D := rfl

def centerExpr := c 1+(d+c 1)*n+n
def denominatorExpr := c 2*(centerExpr+n*(n+c 1))+c 2*pw n 2+c 2*(d+c 1)
def valueExpr := c 2*d*(centerExpr+c 2*n*(n+c 1))+c 16*d*pw n 4+c 6*d
def jointExpr := valueExpr*pw (c 83886080*(c 1+pw denominatorExpr 2)) 4
def secondExpr := jointExpr*(c 1+c 2*jointExpr)
def curvatureExpr := c 1+(n+c 1)*secondExpr
def thresholdInvExpr := n+c 1
def precisionInvExpr := c 128*pw (n+c 1) 2
def slopeInvExpr := c 32768+(secondExpr+c 1)*precisionInvExpr
def valueInvExpr := c 4*precisionInvExpr*slopeInvExpr
def paidInvExpr := c 32768+c 4*curvatureExpr*thresholdInvExpr
def preparationExpr := n*paidInvExpr+c 2
def cleanupInvExpr := c 131072*(n+c 1)
def potentialExpr := centerExpr+c 2*pw n 2+c 2*(d+c 1)
def responseEntryExpr := c 4*(potentialExpr+c 1)*slopeInvExpr
def jacobiExpr (v k : E) := (pw n 2+c 1)*pw n 2*pw v 2*pw k 2+c 1
def cleanupExpr := jacobiExpr (c 1) cleanupInvExpr
def responseExpr := jacobiExpr responseEntryExpr (c 64*thresholdInvExpr)
def radiusExpr := (d+c 1)*(c 2*n+c 1)
def tangentSpacingExpr := c 600*(c 2*pw radiusExpr 2+c 1)
def tangentPrecisionExpr := c 360000*(c 2*pw radiusExpr 2+c 1)
def movementUniformExpr := c 1+(n+c 1)*(jointExpr+c 6*pw jointExpr 2)*pw (c 1+c 2*jointExpr) 4
def movementExpr := c 1000000*pw (n+c 1) 3+c 1000*movementUniformExpr+c 200001

@[simp] theorem centerExpr_eval (N D : ℕ) : centerExpr.eval (input N D)=center N D := by
  simp [centerExpr,center]

@[simp] theorem denominatorExpr_eval (N D : ℕ) : denominatorExpr.eval (input N D)=denominator N D := by
  simp [denominatorExpr,denominator]

@[simp] theorem valueExpr_eval (N D : ℕ) : valueExpr.eval (input N D)=value N D := by
  simp [valueExpr,value]

@[simp] theorem jointExpr_eval (N D : ℕ) : jointExpr.eval (input N D)=joint N D := by
  simp [jointExpr,joint]

@[simp] theorem secondExpr_eval (N D : ℕ) : secondExpr.eval (input N D)=second N D := by
  simp [secondExpr,second]

@[simp] theorem curvatureExpr_eval (N D : ℕ) : curvatureExpr.eval (input N D)=curvature N D := by
  simp [curvatureExpr,curvature]

@[simp] theorem thresholdInvExpr_eval (N D : ℕ) : thresholdInvExpr.eval (input N D)=thresholdInv N := by
  simp [thresholdInvExpr,thresholdInv]

@[simp] theorem precisionInvExpr_eval (N D : ℕ) : precisionInvExpr.eval (input N D)=MSManuscriptPolynomialQueryParameters.precisionInv N := by
  simp [precisionInvExpr,MSManuscriptPolynomialQueryParameters.precisionInv]

@[simp] theorem slopeInvExpr_eval (N D : ℕ) : slopeInvExpr.eval (input N D)=slopeStepInv N D := by
  simp [slopeInvExpr,slopeStepInv]

@[simp] theorem valueInvExpr_eval (N D : ℕ) : valueInvExpr.eval (input N D)=valueInv N D := by
  simp [valueInvExpr,valueInv]

@[simp] theorem paidInvExpr_eval (N D : ℕ) : paidInvExpr.eval (input N D)=paidInv N D := by
  simp [paidInvExpr,paidInv]

@[simp] theorem preparationExpr_eval (N D : ℕ) : preparationExpr.eval (input N D)=preparation N D := by
  simp [preparationExpr,preparation]

@[simp] theorem cleanupInvExpr_eval (N D : ℕ) : cleanupInvExpr.eval (input N D)=cleanupInv N := by
  simp [cleanupInvExpr,cleanupInv]

@[simp] theorem potentialExpr_eval (N D : ℕ) : potentialExpr.eval (input N D)=MSManuscriptPolynomialQueryMagnitude.potentialCap N D := by
  simp [potentialExpr,MSManuscriptPolynomialQueryMagnitude.potentialCap]

@[simp] theorem responseEntryExpr_eval (N D : ℕ) : responseEntryExpr.eval (input N D)=MSManuscriptPolynomialQueryMagnitude.responseEntry N D := by
  simp [responseEntryExpr,MSManuscriptPolynomialQueryMagnitude.responseEntry]

@[simp] theorem cleanupExpr_eval (N D : ℕ) : cleanupExpr.eval (input N D)=MSManuscriptPolynomialQueryCleanup.cleanupJacobi N := by
  simp [cleanupExpr,MSManuscriptPolynomialQueryCleanup.cleanupJacobi,jacobiExpr,KSJacobiPolynomialBounds.jacobi]

@[simp] theorem responseExpr_eval (N D : ℕ) : responseExpr.eval (input N D)=MSManuscriptPolynomialQueryMagnitude.responseJacobi N D := by
  simp [responseExpr,MSManuscriptPolynomialQueryMagnitude.responseJacobi,jacobiExpr,KSJacobiPolynomialBounds.jacobi]

@[simp] theorem radiusExpr_eval (N D : ℕ) : radiusExpr.eval (input N D)=acceptanceRadius N D := by
  simp [radiusExpr,acceptanceRadius]

@[simp] theorem tangentSpacingExpr_eval (N D : ℕ) : tangentSpacingExpr.eval (input N D)=MSConvexPolynomialTangentParameters.spacingInv N D := by
  simp [tangentSpacingExpr,MSConvexPolynomialTangentParameters.spacingInv]

@[simp] theorem tangentPrecisionExpr_eval (N D : ℕ) : tangentPrecisionExpr.eval (input N D)=MSConvexPolynomialTangentParameters.precisionInv N D := by
  simp [tangentPrecisionExpr,MSConvexPolynomialTangentParameters.precisionInv]

@[simp] theorem movementUniformExpr_eval (N D : ℕ) : movementUniformExpr.eval (input N D)=movementUniform N D := by
  simp [movementUniformExpr,movementUniform]

@[simp] theorem movementExpr_eval (N D : ℕ) : movementExpr.eval (input N D)=movementCap N D := by
  simp [movementExpr,movementCap]

inductive Index where
  | cleanup | response | preparation | movement | valuePrecision | tangentPrecision | tangentSpacing | radius | slopeInverse | paidInverse
  deriving DecidableEq, Fintype

def outputs : Index→E
  | .cleanup => cleanupExpr
  | .response => responseExpr
  | .preparation => preparationExpr
  | .movement => movementExpr
  | .valuePrecision => valueInvExpr
  | .tangentPrecision => tangentPrecisionExpr
  | .tangentSpacing => tangentSpacingExpr
  | .radius => radiusExpr
  | .slopeInverse => slopeInvExpr
  | .paidInverse => paidInvExpr

def originalOutputs (N D : ℕ) : Index→ℕ
  | .cleanup => MSManuscriptPolynomialQueryCleanup.cleanupJacobi N
  | .response => MSManuscriptPolynomialQueryMagnitude.responseJacobi N D
  | .preparation => preparation N D
  | .movement => movementCap N D
  | .valuePrecision => valueInv N D
  | .tangentPrecision => MSConvexPolynomialTangentParameters.precisionInv N D
  | .tangentSpacing => MSConvexPolynomialTangentParameters.spacingInv N D
  | .radius => acceptanceRadius N D
  | .slopeInverse => slopeStepInv N D
  | .paidInverse => paidInv N D

theorem outputs_eval (N D : ℕ) (i : Index) : (outputs i).eval (input N D)=originalOutputs N D i := by
  cases i
  · exact cleanupExpr_eval N D
  · exact responseExpr_eval N D
  · exact preparationExpr_eval N D
  · exact movementExpr_eval N D
  · exact valueInvExpr_eval N D
  · exact tangentPrecisionExpr_eval N D
  · exact tangentSpacingExpr_eval N D
  · exact radiusExpr_eval N D
  · exact slopeInvExpr_eval N D
  · exact paidInvExpr_eval N D

def circuit : Circuit (Fin 2) Index := ⟨fun i => (outputs i).toRealExpr⟩
def compute (N D : ℕ) : Counted (Index→ℕ) := ⟨fun i => (outputs i).eval (input N D),circuit.cost⟩
theorem compute_value (N D : ℕ) : (compute N D).value=originalOutputs N D := funext (outputs_eval N D)
theorem execution (N D : ℕ) (i : Index) :
    NatExpr.Executes (input N D) (outputs i) ((compute N D).value i) (outputs i).cost := NatExpr.executes _ _
theorem real_execution (N D : ℕ) (i : Index) :
    Expr.Executes (fun i => (input N D i:ℝ)) (circuit.output i)
      ((compute N D).value i:ℝ) (circuit.output i).cost := by
  simpa [circuit] using NatExpr.real_executes (outputs i) (input N D)
theorem cost : circuit.cost≤1000000 := by decide
theorem compute_cost (N D : ℕ) : (compute N D).cost≤1000000 := cost

end MatrixSpencer.RealRAM.MSLoopCapSetup
