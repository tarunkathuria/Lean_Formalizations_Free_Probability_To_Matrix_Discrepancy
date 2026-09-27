import SeamlessKS.RuntimeInput
import SeamlessKS.RuntimeCaps
import MatrixSpencer.RealRAMPositiveFormula
import MatrixSpencer.RealRAMCeiling

/-! Exact scalar setup for the seamless walk. Every displayed analytic scale
is evaluated by a fixed primitive arithmetic expression. Positivity of the
original Parseval input makes every division and scalar square root safe. -/
open scoped BigOperators
noncomputable section
namespace SeamlessKS.RuntimeParameters
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev Reg := Fin 3
abbrev Formula := PositiveFormula Reg
local instance : Add Formula := ⟨PositiveFormula.add⟩
local instance : Mul Formula := ⟨PositiveFormula.mul⟩
local instance : Div Formula := ⟨PositiveFormula.div⟩
def c (n : ℕ) (h : 0<n := by decide) : Formula := .constant n (by exact_mod_cast h)
def r (i : Reg) : Formula := .input i
def sq (a : Formula) := a*a
def fourth (a : Formula) := sq (sq a)
def root (a : Formula) := PositiveFormula.sqrt a
def least (a b : Formula) := PositiveFormula.minimum a b
@[simp] theorem c_eval (n : ℕ) (h : 0<n) (x : Reg → ℝ) : (c n h).eval x=n := by simp [c]
@[simp] theorem r_eval (i : Reg) (x : Reg → ℝ) : (r i).eval x=x i := rfl
@[simp] theorem add_eval (a b : Formula) (x : Reg → ℝ) : (a+b).eval x=a.eval x+b.eval x := rfl
@[simp] theorem mul_eval (a b : Formula) (x : Reg → ℝ) : (a*b).eval x=a.eval x*b.eval x := rfl
@[simp] theorem div_eval (a b : Formula) (x : Reg → ℝ) : (a/b).eval x=a.eval x/b.eval x := rfl
@[simp] theorem sq_eval (a : Formula) (x : Reg → ℝ) : (sq a).eval x=(a.eval x)^2 := by simp [sq,pow_two]
@[simp] theorem fourth_eval (a : Formula) (x : Reg → ℝ) : (fourth a).eval x=(a.eval x)^4 := by simp [fourth]; ring
@[simp] theorem root_eval (a : Formula) (x : Reg → ℝ) : (root a).eval x=Real.sqrt (a.eval x) := rfl
@[simp] theorem least_eval (a b : Formula) (x : Reg → ℝ) :
    (least a b).eval x=min (a.eval x) (b.eval x) := PositiveFormula.eval_minimum _ _ _

def epsilon := r 2
def delta := root epsilon
def theta := delta/root (c 2*r 1)
def rho := c 1/(c 100*sq (r 0))
def outwardStep := rho/c 16
def zeta := outwardStep/c 10
def beta := delta/(c 100*r 0)
def densityFloor := sq (theta/c 40)
def complexRadius := least (least (least (c 1) densityFloor) rho) zeta/c 10000
def objectiveBound := c 10000*sq (c 2*r 1+c 1)
def jointDerivativeBound := objectiveBound*fourth (c 10/complexRadius)
def coercivity := theta/c 2
def derivativeBudget := c 1+(jointDerivativeBound+c 3*sq jointDerivativeBound/coercivity)*
  fourth (c 1+jointDerivativeBound/coercivity)
def queryStep := least (rho/c 16) (root (beta/(c 128*r 0*derivativeBudget)))
def movementStep := least (rho/c 16) (root (beta/(c 4*derivativeBudget)))
def hessianAccuracy := beta*sq queryStep/(c 128*r 0)
def localAccuracy := beta*sq movementStep/c 8
def horizonArgument := c 16*r 0/sq movementStep

def formulas : Fin 18 → Formula := ![epsilon,delta,theta,rho,outwardStep,zeta,beta,
  densityFloor,complexRadius,objectiveBound,jointDerivativeBound,coercivity,derivativeBudget,
  queryStep,movementStep,hessianAccuracy,localAccuracy,horizonArgument]
def circuit : Circuit Reg (Fin 18) := ⟨fun i => (formulas i).toExpr⟩

variable {N d : ℕ}
def input (v : Fin N → Fin d → ℂ) : Reg → ℝ := ![(N:ℝ),(d:ℝ),Input.epsilon v]
@[simp] theorem input_0 (v : Fin N → Fin d → ℂ) : input v 0=(N:ℝ) := rfl
@[simp] theorem input_1 (v : Fin N → Fin d → ℂ) : input v 1=(d:ℝ) := rfl
@[simp] theorem input_2 (v : Fin N → Fin d → ℂ) : input v 2=Input.epsilon v := rfl

@[simp] theorem epsilon_eval (v : Fin N → Fin d → ℂ) : epsilon.eval (input v)=Input.epsilon v := rfl
@[simp] theorem delta_eval (v : Fin N → Fin d → ℂ) : delta.eval (input v)=Input.delta v := by simp [delta,Input.delta]
@[simp] theorem theta_eval (v : Fin N → Fin d → ℂ) : theta.eval (input v)=Input.theta v := by simp [theta,Input.theta]
@[simp] theorem rho_eval (v : Fin N → Fin d → ℂ) : rho.eval (input v)=Parameters.rho N := by simp [rho,Parameters.rho]
@[simp] theorem outwardStep_eval (v : Fin N → Fin d → ℂ) : outwardStep.eval (input v)=Parameters.outwardStep N := by simp [outwardStep,Parameters.outwardStep]
@[simp] theorem zeta_eval (v : Fin N → Fin d → ℂ) : zeta.eval (input v)=Parameters.zeta N := by simp [zeta,Parameters.zeta]
@[simp] theorem beta_eval (v : Fin N → Fin d → ℂ) : beta.eval (input v)=Parameters.beta v := by simp [beta,Parameters.beta]
@[simp] theorem densityFloor_eval (v : Fin N → Fin d → ℂ) : densityFloor.eval (input v)=Parameters.densityFloor v := by simp [densityFloor,Parameters.densityFloor]
@[simp] theorem complexRadius_eval (v : Fin N → Fin d → ℂ) : complexRadius.eval (input v)=Parameters.complexRadius v := by simp [complexRadius,Parameters.complexRadius]
@[simp] theorem objectiveBound_eval (v : Fin N → Fin d → ℂ) : objectiveBound.eval (input v)=Parameters.objectiveBound d := by simp [objectiveBound,Parameters.objectiveBound]
@[simp] theorem jointDerivativeBound_eval (v : Fin N → Fin d → ℂ) : jointDerivativeBound.eval (input v)=Parameters.jointDerivativeBound v := by simp [jointDerivativeBound,Parameters.jointDerivativeBound]
@[simp] theorem coercivity_eval (v : Fin N → Fin d → ℂ) : coercivity.eval (input v)=Parameters.coercivity v := by simp [coercivity,Parameters.coercivity]
@[simp] theorem derivativeBudget_eval (v : Fin N → Fin d → ℂ) : derivativeBudget.eval (input v)=Parameters.derivativeBudget v := by simp [derivativeBudget,Parameters.derivativeBudget]
@[simp] theorem queryStep_eval (v : Fin N → Fin d → ℂ) : queryStep.eval (input v)=Parameters.queryStep v := by simp [queryStep,Parameters.queryStep]
@[simp] theorem movementStep_eval (v : Fin N → Fin d → ℂ) : movementStep.eval (input v)=Parameters.movementStep v := by simp [movementStep,Parameters.movementStep]
@[simp] theorem hessianAccuracy_eval (v : Fin N → Fin d → ℂ) : hessianAccuracy.eval (input v)=Parameters.hessianAccuracy v := by simp [hessianAccuracy,Parameters.hessianAccuracy]
@[simp] theorem localAccuracy_eval (v : Fin N → Fin d → ℂ) : localAccuracy.eval (input v)=Parameters.localAccuracy v := by simp [localAccuracy,Parameters.localAccuracy]
@[simp] theorem horizonArgument_eval (v : Fin N → Fin d → ℂ) : horizonArgument.eval (input v)=16*(N:ℝ)/Parameters.movementStep v^2 := by simp [horizonArgument]

def outputs (v : Fin N → Fin d → ℂ) : Fin 18 → ℝ :=
  ![Input.epsilon v,Input.delta v,Input.theta v,Parameters.rho N,Parameters.outwardStep N,
    Parameters.zeta N,Parameters.beta v,Parameters.densityFloor v,Parameters.complexRadius v,
    Parameters.objectiveBound d,Parameters.jointDerivativeBound v,Parameters.coercivity v,
    Parameters.derivativeBudget v,Parameters.queryStep v,Parameters.movementStep v,
    Parameters.hessianAccuracy v,Parameters.localAccuracy v,16*(N:ℝ)/Parameters.movementStep v^2]

theorem circuit_outputs (v : Fin N → Fin d → ℂ) : circuit.eval (input v)=outputs v := by
  funext i
  change (formulas i).eval (input v)=outputs v i
  fin_cases i <;> simp [formulas,outputs]

theorem input_positive (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) : ∀ i, 0 < input v i := by
  intro i
  fin_cases i <;> dsimp [input]
  · exact_mod_cast Input.labels_pos v hd hp
  · exact_mod_cast hd
  · exact Input.epsilon_pos v hd hp

theorem circuit_valid (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) : circuit.Valid (input v) :=
  fun i => (PositiveFormula.safe_and_positive (formulas i) _ (input_positive v hd hp)).1

theorem circuit_execution (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (i : Fin 18) :
    Expr.Executes (input v) (circuit.output i) (outputs v i) (circuit.output i).cost := by
  have hh := Expr.executes_of_valid (input v) (circuit.output i) (circuit_valid v hd hp i)
  have he := congrFun (circuit_outputs v) i
  change (circuit.output i).eval (input v)=outputs v i at he
  rwa [he] at hh

theorem circuit_cost : circuit.cost≤10000000 := by decide

def computeScalars (v : Fin N → Fin d → ℂ) : Counted (Fin 18 → ℝ) :=
  let e := RuntimeInput.compute v
  ⟨circuit.eval ![(N:ℝ),(d:ℝ),e.value],e.cost+circuit.cost+8⟩
@[simp] theorem computeScalars_value (v : Fin N → Fin d → ℂ) :
    (computeScalars v).value=outputs v := by
  simp only [computeScalars,RuntimeInput.compute_value]
  exact circuit_outputs v

theorem computeScalars_cost (v : Fin N → Fin d → ℂ) :
    (computeScalars v).cost≤10000100*(N+1)*(d+1) := by
  have hi := RuntimeInput.compute_cost v
  have hc := circuit_cost
  dsimp only [computeScalars]
  nlinarith

/-- The actual horizon is the output of a bounded comparison/addition
program. Its cap is an explicit natural polynomial in the input dimensions. -/
def horizonInput (p : Fin 18 → ℝ) : Ceiling.Register → ℝ
  | .argument => p 17
  | .counter => 0

def horizonProgram (N d : ℕ) := Ceiling.program (RuntimeBudgets.horizonCap N d)

theorem horizon_le (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    Parameters.horizon v≤RuntimeBudgets.horizonCap N d := by
  have hh := Parameters.horizon_le_polynomial v hd hp
  rw [←RuntimeBudgets.cast_horizonCap] at hh
  exact_mod_cast hh

theorem horizon_execution (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    ∃ q k, Program.Executes (horizonProgram N d)
      (horizonInput (computeScalars v).value) q k ∧
      q .counter=(Parameters.horizon v:ℝ) ∧ k≤8*RuntimeBudgets.horizonCap N d+3 := by
  have harg : horizonInput (computeScalars v).value .argument=
      16*(N:ℝ)/Parameters.movementStep v^2 := by rw [computeScalars_value]; rfl
  have hcap : horizonInput (computeScalars v).value .argument≤RuntimeBudgets.horizonCap N d := by
    rw [harg]
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (horizon_le v hd hp))
  obtain ⟨q,k,he,hq,_,hk⟩ := Ceiling.execution (RuntimeBudgets.horizonCap N d)
    (horizonInput (computeScalars v).value) hcap
  refine ⟨q,k,he,?_,hk⟩
  simpa only [harg,Parameters.horizon] using hq


/-- Complete finite setup. The horizon is computed by counted comparison
steps, using the cap just formed by the natural arithmetic circuit. -/
def compute (v : Fin N → Fin d → ℂ) : Counted ((Fin 18 → ℝ) × ℕ) :=
  let p := computeScalars v
  let caps := RuntimeCaps.compute N d
  let loop := JacobiRayleigh.ceilLoop (p.value 17) (caps.value 7)
  ⟨(p.value,loop.value),p.cost+caps.cost+loop.cost+12⟩

@[simp] theorem compute_parameters (v : Fin N → Fin d → ℂ) :
    (compute v).value.1=outputs v := computeScalars_value v

theorem compute_horizon (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i,KSRankOne.atom (v i))=1) :
    (compute v).value.2=Parameters.horizon v := by
  have hcap : 16*(N:ℝ)/Parameters.movementStep v^2≤RuntimeBudgets.horizonCap N d :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (horizon_le v hd hp))
  simp only [compute,computeScalars_value,RuntimeCaps.compute_value]
  change (JacobiRayleigh.ceilLoop (16*(N:ℝ)/Parameters.movementStep v^2)
    (RuntimeBudgets.horizonCap N d)).value=Parameters.horizon v
  exact JacobiRayleigh.ceilLoop_exact _ _ hcap

theorem compute_value (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i,KSRankOne.atom (v i))=1) :
    (compute v).value=(outputs v,Parameters.horizon v) :=
  Prod.ext (compute_parameters v) (compute_horizon v hd hp)

def costBound (N d : ℕ) := 12000100*(N+1)*(d+1)+8*RuntimeBudgets.horizonCap N d+100

theorem compute_cost (v : Fin N → Fin d → ℂ) : (compute v).cost≤costBound N d := by
  have hp := computeScalars_cost v
  have hc := RuntimeCaps.compute_cost N d
  dsimp only [compute]
  rw [JacobiRayleigh.ceilLoop_cost,RuntimeCaps.compute_value]
  change (computeScalars v).cost+(RuntimeCaps.compute N d).cost+
    (8*RuntimeBudgets.horizonCap N d+3)+12≤costBound N d
  unfold costBound
  nlinarith


/-- Primitive execution certificates for the entire setup. The register
identities proved above connect the output of each stage to the next stage. -/
def SetupExecutes (v : Fin N → Fin d → ℂ) : Prop :=
  (∀ i, Expr.Executes (KSInputSetup.input v) (KSInputSetup.sizeExpr i)
    (Input.size v i) (8*d+1)) ∧
  (∃ q k, Program.Executes (RuntimeInput.maxProgram (List.finRange N))
    (RuntimeInput.maxInput (KSInputSetup.sizes v).value) q k ∧
    q (.inr ())=Input.epsilon v ∧ k≤5*N+2) ∧
  (∀ i, Expr.Executes (input v) (circuit.output i) (outputs v i) (circuit.output i).cost) ∧
  (∀ i, Expr.Executes (fun j => (RuntimeCaps.input N d j:ℝ)) (RuntimeCaps.circuit.output i)
    (RuntimeCaps.outputs N d i:ℝ) (RuntimeCaps.circuit.output i).cost) ∧
  (∃ q k, Program.Executes (horizonProgram N d)
    (horizonInput (computeScalars v).value) q k ∧
    q .counter=(Parameters.horizon v:ℝ) ∧ k≤8*RuntimeBudgets.horizonCap N d+3)

theorem setup_execution (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i,KSRankOne.atom (v i))=1) : SetupExecutes v :=
  ⟨RuntimeInput.sizes_execution v,RuntimeInput.maximum_execution v,
    circuit_execution v hd hp,RuntimeCaps.circuit_execution N d,horizon_execution v hd hp⟩

end SeamlessKS.RuntimeParameters
