import MatrixSpencer.RealRAMKSInputSetup
import MatrixSpencer.RealRAMPositiveFormula
import MatrixSpencer.KSFullManuscriptAlgorithm
import MatrixSpencer.KSEighthManuscriptAlgorithm



open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RealRAM.KSParameterSetup
open JacobiIteration (Counted)

abbrev Reg := Fin 8
abbrev Formula := PositiveFormula Reg

instance : Add Formula := ⟨PositiveFormula.add⟩
instance : Mul Formula := ⟨PositiveFormula.mul⟩
instance : Div Formula := ⟨PositiveFormula.div⟩

def c (n : ℕ) (h : 0<n := by decide) : Formula := .constant n (by exact_mod_cast h)
def r (i : Reg) : Formula := .input i
def sq (a : Formula) := a*a
def fourth (a : Formula) := sq (sq a)
def root (a : Formula) := PositiveFormula.sqrt a
def least (a b : Formula) := PositiveFormula.minimum a b
def greatest (a b : Formula) := PositiveFormula.maximum a b

@[simp] theorem c_eval (n : ℕ) (h : 0<n) (x : Reg → ℝ) : (c n h).eval x = n := by
  simp [c]
@[simp] theorem r_eval (i : Reg) (x : Reg → ℝ) : (r i).eval x = x i := rfl
@[simp] theorem add_eval (a b : Formula) (x : Reg → ℝ) : (a+b).eval x=a.eval x+b.eval x := rfl
@[simp] theorem mul_eval (a b : Formula) (x : Reg → ℝ) : (a*b).eval x=a.eval x*b.eval x := rfl
@[simp] theorem div_eval (a b : Formula) (x : Reg → ℝ) : (a/b).eval x=a.eval x/b.eval x := rfl
@[simp] theorem sq_eval (a : Formula) (x : Reg → ℝ) : (sq a).eval x=(a.eval x)^2 := by simp [sq,pow_two]
@[simp] theorem fourth_eval (a : Formula) (x : Reg → ℝ) : (fourth a).eval x=(a.eval x)^4 := by
  simp [fourth]; ring
@[simp] theorem root_eval (a : Formula) (x : Reg → ℝ) : (root a).eval x=Real.sqrt (a.eval x) := rfl
@[simp] theorem least_eval (a b : Formula) (x : Reg → ℝ) : (least a b).eval x=min (a.eval x) (b.eval x) :=
  PositiveFormula.eval_minimum _ _ _
@[simp] theorem greatest_eval (a b : Formula) (x : Reg → ℝ) :
    (greatest a b).eval x=max (a.eval x) (b.eval x) := PositiveFormula.eval_maximum _ _ _

def physicalDimension := r 1+r 1
def delta := root (r 2)
def theta := delta/root physicalDimension
def debit := delta/r 0
def curvature := delta/(c 100*r 0)
def fullCenter := c 1+r 3+(delta*r 3+r 0*debit)
def denominator (center source : Formula) := c 2*center+c 2*root source+c 2*theta*root physicalDimension
def densityFloor (center source : Formula) := sq (theta/denominator center source)
def radius (floor margin : Formula) := least (c 1) (least floor margin)/c 1000
def objectiveCap (center source : Formula) :=
  c 1+physicalDimension*center*c 2+c 2*physicalDimension*root (c 2*source)+
    c 2*theta*physicalDimension*root (c 2)
def joint (center source margin : Formula) :=
  objectiveCap center source * fourth (c 10/radius (densityFloor center source) margin)
def envelope (b : Formula) :=
  (b+c 3*sq b/(theta/c 2))*fourth (c 1+b/(theta/c 2))

-- Full-cube floor uses the debit center; the complex objective center also
-- includes the allowed time-direction excursion. They are deliberately distinct.
def fullFloor := densityFloor fullCenter (r 5)
def fullRadius := radius fullFloor (delta/c 2)
def fullObjective := objectiveCap (fullCenter+c 2*r 4) (r 6)
def fullJoint := fullObjective*fourth (c 10/fullRadius)
def fullM := greatest (envelope fullJoint) (c 6144*curvature/sq delta)+c 1
def fullQuery := least (delta/(c 4*root (c 2))) (root (curvature/(c 8*r 0*fullM)))
def fullValue := curvature*sq fullQuery/(c 16*r 0)
def fullMovement := least (delta/c 4) (root (c 24*curvature/fullM))

def eighthCenter := c 3*r 4
def eighthDirection := c 2*r 4
def eighthFloor := densityFloor eighthCenter (r 7)
def eighthRadius := radius eighthFloor (c 1/c 2)
def eighthJoint := objectiveCap (eighthCenter+eighthDirection) (r 7)*fourth (c 10/eighthRadius)
def eighthM := c 1+envelope eighthJoint
def eighthRho := delta/(c 100*r 0)
def eighthKappa := delta/(c 10000*sq (r 0))
def eighthPrecision := eighthKappa/(c 100*r 0)
def eighthBeta := eighthKappa/(c 100*r 0*(eighthM+c 1))
def eighthMovement := (c 1/c 2)*least (eighthRho/root (r 0))
  (least (root (delta/(c 10000*eighthM*(sq (r 0)*r 0)))) (c 1/c 100))

def formulas : Fin 14 → Formula :=
  ![delta,theta,debit,curvature,fullM,fullQuery,fullValue,fullMovement,
    eighthM,eighthRho,eighthKappa,eighthPrecision,eighthBeta,eighthMovement]
def circuit : Circuit Reg (Fin 14) := ⟨fun i => (formulas i).toExpr⟩

variable {N d : ℕ}

def originalInput (v : Fin N → Fin d → ℂ) (ε : ℝ) : Reg → ℝ :=
  ![(N:ℝ),(d:ℝ),ε,KSDebitUniformFloor.atomBudget v,KSComplexPolynomialBounds.slopeBudget v,
    KSDebitUniformFloor.spinBudget v,KSComplexPolynomialBounds.sourceBudget v,
    KSEighthInputTaylorBound.sourceCap v]

@[simp] theorem originalInput_0 (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    originalInput v ε 0 = (N:ℝ) := rfl

@[simp] theorem originalInput_1 (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    originalInput v ε 1 = (d:ℝ) := rfl

@[simp] theorem originalInput_2 (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    originalInput v ε 2 = ε := rfl

@[simp] theorem originalInput_3 (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    originalInput v ε 3 = KSDebitUniformFloor.atomBudget v := rfl

@[simp] theorem originalInput_4 (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    originalInput v ε 4 = KSComplexPolynomialBounds.slopeBudget v := rfl

@[simp] theorem originalInput_5 (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    originalInput v ε 5 = KSDebitUniformFloor.spinBudget v := rfl

@[simp] theorem originalInput_6 (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    originalInput v ε 6 = KSComplexPolynomialBounds.sourceBudget v := rfl

@[simp] theorem originalInput_7 (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    originalInput v ε 7 = KSEighthInputTaylorBound.sourceCap v := rfl

@[simp] theorem delta_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    delta.eval (originalInput v ε)=Real.sqrt ε := by simp [delta]

@[simp] theorem theta_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    theta.eval (originalInput v ε)=ksRegularizerScale ε (Fin d) := by
  simp [theta,physicalDimension,ksRegularizerScale]

@[simp] theorem debit_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    debit.eval (originalInput v ε)=KSFullManuscriptParameters.debitTolerance N (Real.sqrt ε) := by
  simp [debit,KSFullManuscriptParameters.debitTolerance]

@[simp] theorem curvature_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    curvature.eval (originalInput v ε)=KSFullManuscriptParameters.curvatureTolerance N (Real.sqrt ε) := by
  simp [curvature,KSFullManuscriptParameters.curvatureTolerance]

@[simp] theorem fullCenter_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    fullCenter.eval (originalInput v ε)=KSDebitUniformFloor.centerRadius v (Real.sqrt ε)
      (KSFullManuscriptParameters.debitTolerance N (Real.sqrt ε)) := by
  simp [fullCenter,KSDebitUniformFloor.centerRadius,KSDebitUniformFloor.debitBound]

@[simp] theorem fullFloor_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    fullFloor.eval (originalInput v ε)=KSDebitUniformFloor.uniformFloor v (Real.sqrt ε)
      (KSFullManuscriptParameters.debitTolerance N (Real.sqrt ε)) (ksRegularizerScale ε (Fin d)) := by
  simp [fullFloor,densityFloor,denominator,physicalDimension,
    KSDebitUniformFloor.uniformFloor,KSOptimizerFloor.inputDenominator]

@[simp] theorem fullRadius_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    fullRadius.eval (originalInput v ε)=KSJointBoundParameters.radius v (Real.sqrt ε)
      (KSFullManuscriptParameters.debitTolerance N (Real.sqrt ε)) (ksRegularizerScale ε (Fin d)) := by
  simp [fullRadius,radius,KSJointBoundParameters.radius,KSComplexPerturbationRadius.radius]

@[simp] theorem fullObjective_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    fullObjective.eval (originalInput v ε)=KSJointBoundParameters.objectiveCap v (Real.sqrt ε)
      (KSFullManuscriptParameters.debitTolerance N (Real.sqrt ε)) (ksRegularizerScale ε (Fin d)) := by
  simp [fullObjective,objectiveCap,physicalDimension,
    KSJointBoundParameters.objectiveCap,KSJointBoundParameters.centerCap,KSComplexObjectiveBound.valueCap]
  ring

@[simp] theorem fullJoint_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    fullJoint.eval (originalInput v ε)=KSJointBoundParameters.jointCap v (Real.sqrt ε)
      (KSFullManuscriptParameters.debitTolerance N (Real.sqrt ε)) (ksRegularizerScale ε (Fin d)) := by
  simp [fullJoint,KSJointBoundParameters.jointCap]

variable [Nonempty (Fin d)]

@[simp] theorem fullM_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    fullM.eval (originalInput v ε)=KSFullManuscriptAlgorithm.taylorBudget v ε := by
  simp [fullM,envelope,KSFullManuscriptAlgorithm.taylorBudget,KSFullManuscriptTaylor.budget,
    KSTaylorBudget.envelopeCap]

@[simp] theorem fullQuery_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    fullQuery.eval (originalInput v ε)=KSFullManuscriptParameters.queryStep N (Real.sqrt ε)
      (KSFullManuscriptAlgorithm.taylorBudget v ε) := by
  simp [fullQuery,KSFullManuscriptParameters.queryStep]

@[simp] theorem fullValue_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    fullValue.eval (originalInput v ε)=KSFullManuscriptParameters.valueTolerance N (Real.sqrt ε)
      (KSFullManuscriptAlgorithm.taylorBudget v ε) := by
  simp [fullValue,KSFullManuscriptParameters.valueTolerance]

@[simp] theorem fullMovement_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    fullMovement.eval (originalInput v ε)=KSFullManuscriptParameters.movementStep N (Real.sqrt ε)
      (KSFullManuscriptAlgorithm.taylorBudget v ε) := by
  simp [fullMovement,KSFullManuscriptParameters.movementStep]

@[simp] theorem eighthFloor_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    eighthFloor.eval (originalInput v ε)=KSEighthJointBoundPoint.floor (n:=Fin d)
      (KSEighthInputTaylorBound.centerCap v) (KSEighthInputTaylorBound.sourceCap v)
      (ksRegularizerScale ε (Fin d)) := by
  simp [eighthFloor,densityFloor,denominator,physicalDimension,eighthCenter,
    KSEighthJointBoundPoint.floor,KSEighthInputTaylorBound.centerCap,KSEighthInputTaylorBound.slopeBudget,
    KSOptimizerFloor.inputDenominator]

@[simp] theorem eighthRadius_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    eighthRadius.eval (originalInput v ε)=KSEighthJointBoundPoint.radius (n:=Fin d)
      (KSEighthInputTaylorBound.centerCap v) (KSEighthInputTaylorBound.sourceCap v)
      (ksRegularizerScale ε (Fin d)) := by
  simp [eighthRadius,radius,KSEighthJointBoundPoint.radius,KSComplexPerturbationRadius.radius]

@[simp] theorem eighthJoint_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    eighthJoint.eval (originalInput v ε)=KSEighthInputTaylorBound.jointBudget v
      (ksRegularizerScale ε (Fin d)) := by
  simp [eighthJoint,objectiveCap,physicalDimension,eighthCenter,eighthDirection,
    KSEighthInputTaylorBound.jointBudget,KSEighthJointBoundPoint.jointCap,
    KSEighthJointBoundPoint.valueCap,KSEighthInputTaylorBound.centerCap,
    KSEighthInputTaylorBound.directionCap,KSEighthInputTaylorBound.slopeBudget,
    KSComplexObjectiveBound.valueCap]
  ring_nf
  simp

@[simp] theorem eighthM_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    eighthM.eval (originalInput v ε)=KSEighthManuscriptParameters.fourthCap v
      (ksRegularizerScale ε (Fin d)) := by
  simp [eighthM,envelope,KSEighthManuscriptParameters.fourthCap,KSEighthInputTaylorBound.fourthBudget]

@[simp] theorem eighthRho_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    eighthRho.eval (originalInput v ε)=KSEighthManuscriptParameters.rho N (Real.sqrt ε) := by
  simp [eighthRho,KSEighthManuscriptParameters.rho]

@[simp] theorem eighthKappa_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    eighthKappa.eval (originalInput v ε)=KSEighthManuscriptParameters.kappa N (Real.sqrt ε) := by
  simp [eighthKappa,KSEighthManuscriptParameters.kappa]

@[simp] theorem eighthPrecision_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    eighthPrecision.eval (originalInput v ε)=KSEighthManuscriptParameters.precision N (Real.sqrt ε) := by
  simp [eighthPrecision,KSEighthManuscriptParameters.precision]

@[simp] theorem eighthBeta_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    eighthBeta.eval (originalInput v ε)=KSEighthManuscriptParameters.beta v (Real.sqrt ε)
      (ksRegularizerScale ε (Fin d)) := by
  simp [eighthBeta,KSEighthManuscriptParameters.beta]

@[simp] theorem eighthMovement_eval (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    eighthMovement.eval (originalInput v ε)=KSEighthManuscriptParameters.movementStep v (Real.sqrt ε)
      (ksRegularizerScale ε (Fin d)) := by
  simp only [eighthMovement,mul_eval,div_eval,least_eval,root_eval,c_eval,r_eval,sq_eval,
    delta_eval,eighthM_eval,eighthRho_eval,originalInput_0,KSEighthManuscriptParameters.movementStep]
  norm_num only [Nat.cast_ofNat]
  rw [show (N:ℝ)^2*N=(N:ℝ)^3 by ring]

def originalOutputs (v : Fin N → Fin d → ℂ) (ε : ℝ) : Fin 14 → ℝ :=
  let δ := Real.sqrt ε
  let θ := ksRegularizerScale ε (Fin d)
  let M := KSFullManuscriptAlgorithm.taylorBudget v ε
  ![δ,θ,KSFullManuscriptParameters.debitTolerance N δ,
    KSFullManuscriptParameters.curvatureTolerance N δ,M,
    KSFullManuscriptParameters.queryStep N δ M,KSFullManuscriptParameters.valueTolerance N δ M,
    KSFullManuscriptParameters.movementStep N δ M,KSEighthManuscriptParameters.fourthCap v θ,
    KSEighthManuscriptParameters.rho N δ,KSEighthManuscriptParameters.kappa N δ,
    KSEighthManuscriptParameters.precision N δ,KSEighthManuscriptParameters.beta v δ θ,
    KSEighthManuscriptParameters.movementStep v δ θ]

theorem circuit_outputs (v : Fin N → Fin d → ℂ) (ε : ℝ) :
    circuit.eval (originalInput v ε)=originalOutputs v ε := by
  funext i
  change (formulas i).eval (originalInput v ε)=originalOutputs v ε i
  fin_cases i <;> simp [formulas,originalOutputs]

theorem originalInput_positive (v : Fin N → Fin d → ℂ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) :
    ∀i,0<originalInput v ε i := by
  have hd : 0<d := by simpa using (Fintype.card_pos (α:=Fin d))
  intro i
  fin_cases i <;> simp only [originalInput] <;> dsimp
  · exact_mod_cast hN
  · exact_mod_cast hd
  · exact hε
  · exact KSDebitUniformFloor.atomBudget_pos v
  · exact KSComplexPolynomialBounds.slopeBudget_pos v
  · exact KSDebitUniformFloor.spinBudget_pos v
  · exact KSComplexPolynomialBounds.sourceBudget_pos v
  · exact KSComplexTraceBounds.sourceBudget_pos (KSEighthActualState.family v)

/-- Safety of every division and scalar square root follows from the original
positive-dimensional input domain, with no numerical accuracy hypothesis. -/
theorem circuit_executes (v : Fin N → Fin d → ℂ) (hN : 0<N) {ε : ℝ} (hε : 0<ε)
    (i : Fin 14) :
    Expr.Executes (originalInput v ε) (circuit.output i) (originalOutputs v ε i)
      (circuit.output i).cost := by
  have h := PositiveFormula.executes (formulas i) (originalInput v ε) (originalInput_positive v hN hε)
  have hv := congrFun (circuit_outputs v ε) i
  change (formulas i).eval (originalInput v ε)=originalOutputs v ε i at hv
  simpa only [hv] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem circuit_cost : circuit.cost ≤ 10000000 := by decide

def compute (v : Fin N → Fin d → ℂ) : Counted (Fin 14 → ℝ) :=
  let q := KSInputSetup.compute v
  let x : Reg → ℝ := ![(N:ℝ),(d:ℝ),q.value.epsilon,q.value.budgets 0,q.value.budgets 1,
    q.value.budgets 2,q.value.budgets 3,q.value.budgets 4]
  ⟨circuit.eval x,q.cost+circuit.cost+32⟩

theorem compute_value (v : Fin N → Fin d → ℂ) :
    (compute v).value = originalOutputs v (KSEighthManuscriptPreprocess.epsilon v) := by
  have h := KSInputSetup.compute_outputs v
  simp only [compute,h.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2]
  exact circuit_outputs v _

theorem compute_cost (v : Fin N → Fin d → ℂ) :
    (compute v).cost ≤ 10000400*(N+1)*(d+1) := by
  have hi := KSInputSetup.compute_cost v
  have hc := circuit_cost
  dsimp [compute]
  nlinarith

end MatrixSpencer.RealRAM.KSParameterSetup
