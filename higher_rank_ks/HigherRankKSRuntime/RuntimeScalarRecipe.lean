import HigherRankKSRuntime.RuntimeParameterSetup
import MatrixSpencer.RealRAMPositiveFormula

/-! A fixed primitive arithmetic circuit evaluates every runtime scalar.
All divisions and square roots are certified on the actual parameter domain.
The cost is a fixed natural number, independent of the matrix entries and
rank exponent. No power, logarithm, or minimum primitive is introduced. -/
noncomputable section
namespace HigherRankKSRuntime.RuntimeScalarRecipe
open AugmentedHigherRankKS RuntimeParameters MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
set_option maxHeartbeats 1600000

abbrev Formula := PositiveFormula (Fin 3)
local instance : Add Formula := ⟨.add⟩
local instance : Mul Formula := ⟨.mul⟩
local instance : Div Formula := ⟨.div⟩

@[simp] theorem eval_add_formula (f g : Formula) (v : Fin 3 → ℝ) :
    (f+g).eval v = f.eval v+g.eval v := rfl
@[simp] theorem eval_mul_formula (f g : Formula) (v : Fin 3 → ℝ) :
    (f*g).eval v = f.eval v*g.eval v := rfl
@[simp] theorem eval_div_formula (f g : Formula) (v : Fin 3 → ℝ) :
    (f/g).eval v = f.eval v/g.eval v := rfl

def one : Formula := .constant 1 (by norm_num)
def two : Formula := .constant 2 (by norm_num)
def four : Formula := .constant 4 (by norm_num)
def eight : Formula := .constant 8 (by norm_num)
def sixteen : Formula := .constant 16 (by norm_num)
def twenty : Formula := .constant 20 (by norm_num)
def twentySeven : Formula := .constant 27 (by norm_num)
def sixtyFour : Formula := .constant 64 (by norm_num)
def hundred : Formula := .constant 100 (by norm_num)
def twoFiftySix : Formula := .constant 256 (by norm_num)
def thousandTwentyFour : Formula := .constant 1024 (by norm_num)

def power (f : Formula) : ℕ → Formula
  | 0 => one
  | k+1 => power f k * f

@[simp] theorem eval_power (f : Formula) (k : ℕ) (v : Fin 3 → ℝ) :
    (power f k).eval v = (f.eval v)^k := by
  induction k with
  | zero => simp [power,one]
  | succ k ih => rw [power,eval_mul_formula,ih,pow_succ]

def fSize : Formula := ((one+.input 0)+.input 1)+.input 2
def fA : Formula := thousandTwentyFour*.input 2
def fTheta : Formula := one/power fSize 10
def fBbar : Formula := (sixtyFour*fA)*fSize
def fS0 : Formula := power (fTheta/fBbar) 2
def fP0 : Formula := fS0*fTheta
def fTau0 : Formula := ((four*fS0)*power fTheta 2)/fBbar
def fGamma : Formula := (fA*fTau0)/four
def fMdim : Formula := four*.input 1
def fC0 : Formula := eight*.sqrt fA
def fL0 : Formula := ((four*fA)/fTheta+two/fS0)+one
def fH0 : Formula := (hundred*.sqrt fMdim)*fL0
def fA0 : Formula := ((one+twenty*.sqrt fMdim)+two*fC0)+fTheta*.sqrt fMdim
def fB2 : Formula := (four*fA0)*power fH0 2
def fB3 : Formula := (twentySeven*fA0)*power fH0 3
def fM : Formula := fB3*power (one+fB2/(fTheta/two)) 3
def fRadius : Formula := .minimum (fTheta/four) (.sqrt (fTheta/(four*fA)))
def fPrep : Formula := .minimum fTheta (fP0/((eight*fA)*fM))
def fStencil : Formula := .minimum (fRadius/four) (fGamma/((sixtyFour*.input 0)*fM))
def fWalk : Formula := .minimum (fRadius/four) (fGamma/(sixteen*fM))
def fAccuracy : Formula := .minimum one (.minimum ((fPrep*fP0)/(sixtyFour*fA))
  (.minimum ((fGamma*power fStencil 2)/(twoFiftySix*.input 0))
    ((fGamma*power fWalk 2)/sixtyFour)))

inductive Key where
  | size | a | theta | Bbar | s0 | p0 | tau0 | gamma | m | C0 | L0 | H0 | A0
  | B2 | B3 | M | radius | prep | stencil | walk | accuracy
  deriving DecidableEq,Fintype

def formula : Key → Formula
  | .size => fSize | .a => fA | .theta => fTheta | .Bbar => fBbar | .s0 => fS0
  | .p0 => fP0 | .tau0 => fTau0 | .gamma => fGamma | .m => fMdim | .C0 => fC0
  | .L0 => fL0 | .H0 => fH0 | .A0 => fA0 | .B2 => fB2 | .B3 => fB3 | .M => fM
  | .radius => fRadius | .prep => fPrep | .stencil => fStencil | .walk => fWalk
  | .accuracy => fAccuracy

def value (p : Dimensions) : Key → ℝ
  | .size => size p | .a => a p | .theta => theta p | .Bbar => Bbar p | .s0 => s0 p
  | .p0 => p0 p | .tau0 => tau0 p | .gamma => gamma p | .m => m p | .C0 => C0 p
  | .L0 => L0 p | .H0 => H0 p | .A0 => A0 p | .B2 => B2 p | .B3 => B3 p | .M => M p
  | .radius => radius p | .prep => prep p | .stencil => stencil p | .walk => walk p
  | .accuracy => accuracy p

def inputs (p : Dimensions) : Fin 3 → ℝ := ![p.N,p.D,p.q]

/-- The circuit evaluates exactly the scalar recipe used in all analytic
and runtime lemmas, with repeated multiplication replacing fixed powers. -/
theorem formula_value (p : Dimensions) (j : Key) :
    (formula j).eval (inputs p) = value p j := by
  cases j <;>
    simp [formula,value,fSize,fA,fTheta,fBbar,fS0,fP0,fTau0,fGamma,fMdim,fC0,fL0,
      fH0,fA0,fB2,fB3,fM,fRadius,fPrep,fStencil,fWalk,fAccuracy,
      one,two,four,eight,sixteen,twenty,twentySeven,sixtyFour,hundred,twoFiftySix,
      thousandTwentyFour,inputs,size,a,theta,Bbar,s0,p0,tau0,gamma,m,C0,L0,H0,A0,B2,B3,M,
      radius,prep,stencil,walk,accuracy,one_div]

theorem inputs_positive (p : Dimensions) (hp : p ∈ Domain) : ∀ i, 0 < inputs p i := by
  rcases hp with ⟨hN,hD,hq⟩
  intro i
  fin_cases i
  · change 0 < p.N
    linarith
  · change 0 < p.D
    linarith
  · change 0 < p.q
    linarith

theorem formula_valid (p : Dimensions) (hp : p ∈ Domain) (j : Key) :
    (formula j).toExpr.Valid (inputs p) :=
  ((formula j).safe_and_positive (inputs p) (inputs_positive p hp)).1

theorem formula_executes (p : Dimensions) (hp : p ∈ Domain) (j : Key) :
    Expr.Executes (inputs p) (formula j).toExpr (value p j) (formula j).cost := by
  rw [←formula_value p j]
  exact (formula j).executes (inputs p) (inputs_positive p hp)

/-- A fixed operation count for the fully expanded scalar circuits. Sharing
registers would lower it, but is unnecessary for the polynomial theorem. -/
def recipeCost : ℕ := (∑ j : Key,(formula j).cost)+Fintype.card Key

def compute (p : Dimensions) : Counted (Key → ℝ) :=
  ⟨fun j => (formula j).eval (inputs p),recipeCost⟩

theorem compute_value (p : Dimensions) : (compute p).value=value p :=
  funext (formula_value p)

theorem compute_cost (p : Dimensions) : (compute p).cost=recipeCost := rfl

def setup (N d r : ℕ) : Counted (Dimensions × ℕ × (Key → ℝ)) :=
  let base := RuntimeParameterSetup.setup N d r
  let vals := compute base.value.1
  ⟨(base.value.1,base.value.2,vals.value),base.cost+vals.cost⟩

theorem setup_value (N d r : ℕ) :
    (setup N d r).value=((RuntimeParameterSetup.setup N d r).value.1,
      (RuntimeParameterSetup.setup N d r).value.2,
      value (RuntimeParameterSetup.setup N d r).value.1) := by
  simp only [setup,compute_value]

theorem setup_cost {N d r : ℕ} (hN : 1≤N) (hd : 1≤d) (hr : 1≤r) :
    (setup N d r).cost≤20*d+18+recipeCost := by
  have hh := (RuntimeParameterSetup.setup_spec hN hd hr).2.2.2.2.2.2.2.2.2
  dsimp only [setup,compute]
  omega

/-- The remaining discrepancy threshold has a fourth data input, epsilon.
It permits epsilon=0; its square root is therefore certified as nonnegative. -/
def thresholdInputs (a ε : ℝ) : Fin 2 → ℝ := ![a,ε]
def alphaExpr : Expr (Fin 2) := .mul (.mul (.constant 8) (.input 0)) (.input 1)
def deltaExpr : Expr (Fin 2) := .mul (.constant 5) (.sqrt alphaExpr)
def thresholdCost : ℕ := alphaExpr.cost+deltaExpr.cost+2

theorem alphaExpr_value (a ε : ℝ) : alphaExpr.eval (thresholdInputs a ε)=8*a*ε := by
  simp [alphaExpr,Expr.eval,thresholdInputs]
theorem deltaExpr_value (a ε : ℝ) : deltaExpr.eval (thresholdInputs a ε)=5*Real.sqrt (8*a*ε) := by
  simp only [deltaExpr,Expr.eval,alphaExpr_value,Rat.cast_ofNat]

theorem threshold_executes {a ε : ℝ} (ha : 0≤a) (hε : 0≤ε) :
    Expr.Executes (thresholdInputs a ε) alphaExpr (8*a*ε) alphaExpr.cost ∧
    Expr.Executes (thresholdInputs a ε) deltaExpr (5*Real.sqrt (8*a*ε)) deltaExpr.cost := by
  have hvalid : alphaExpr.Valid (thresholdInputs a ε) := by
    simp [alphaExpr,Expr.Valid]
  constructor
  · rw [←alphaExpr_value]
    exact Expr.executes_of_valid _ _ hvalid
  · rw [←deltaExpr_value]
    apply Expr.executes_of_valid
    refine ⟨trivial,hvalid,?_⟩
    rw [alphaExpr_value]
    positivity

def thresholds (a ε : ℝ) : Counted (ℝ×ℝ) :=
  ⟨(alphaExpr.eval (thresholdInputs a ε),deltaExpr.eval (thresholdInputs a ε)),thresholdCost⟩

theorem thresholds_value (a ε : ℝ) : (thresholds a ε).value=(8*a*ε,5*Real.sqrt (8*a*ε)) := by
  simp only [thresholds,alphaExpr_value,deltaExpr_value]
theorem thresholds_cost (a ε : ℝ) : (thresholds a ε).cost=thresholdCost := rfl

def parameterWork : ℕ := recipeCost+thresholdCost

end HigherRankKSRuntime.RuntimeScalarRecipe
