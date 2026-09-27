import MatrixSpencer.RealRAMMSOwnerReport
import MatrixSpencer.MSConvexValueAcceptance

/-! Primitive arithmetic for the six convex-value queries used by the two
square-MS acceptance reports. Matrix shifts are computed entry by entry,
finite-difference scales use explicit real expressions, and the final Boolean
uses scalar comparisons. The caller supplies counted owner-value queries. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.RealRAM.MSValueAcceptance
open JacobiIteration (Counted)
open MSConvexAnchorTangent
variable {N d : ℕ}
set_option maxHeartbeats 1400000
set_option maxRecDepth 4000

def parametersInput (θ R ε : ℝ) : Fin 3 → ℝ := ![θ,R,ε]
def spacingExpr : Expr (Fin 3) :=
  .div (.input 2) (.mul (.constant 6)
    (.add (.mul (.div (.constant 2) (.input 0)) (.mul (.input 1) (.input 1))) (.constant 1)))
def precisionExpr : Expr (Fin 3) := .div (.mul (.input 2) spacingExpr) (.constant 6)

theorem spacingExpr_eval (θ R ε : ℝ) :
    spacingExpr.eval (parametersInput θ R ε)=spacing θ R ε := by
  simp [spacingExpr,Expr.eval,parametersInput,spacing,curvature,pow_two]

theorem precisionExpr_eval (θ R ε : ℝ) :
    precisionExpr.eval (parametersInput θ R ε)=precision θ R ε := by
  change ε*spacingExpr.eval (parametersInput θ R ε)/6=precision θ R ε
  rw [spacingExpr_eval]
  rfl

theorem spacingExpr_valid {θ R ε : ℝ} (hθ : 0<θ) :
    spacingExpr.Valid (parametersInput θ R ε) := by
  simp only [spacingExpr,Expr.Valid,Expr.eval,parametersInput,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_fin_one,Rat.cast_ofNat,
    true_and,and_true,Rat.cast_one]
  refine ⟨hθ.ne',?_⟩
  have hRR : 0≤R*R := mul_self_nonneg R
  have hh : 0<6*((2/θ)*(R*R)+1) := by positivity
  exact hh.ne'

theorem precisionExpr_valid {θ R ε : ℝ} (hθ : 0<θ) :
    precisionExpr.Valid (parametersInput θ R ε) :=
  ⟨⟨trivial,spacingExpr_valid hθ⟩,trivial,by norm_num [Expr.eval]⟩

def parameters (θ R ε : ℝ) : Counted (ℝ×ℝ) :=
  ⟨(spacingExpr.eval (parametersInput θ R ε),precisionExpr.eval (parametersInput θ R ε)),
    spacingExpr.cost+precisionExpr.cost+2⟩

theorem parameters_value (θ R ε : ℝ) :
    (parameters θ R ε).value=(spacing θ R ε,precision θ R ε) := by
  simp only [parameters,spacingExpr_eval,precisionExpr_eval]

theorem parameters_cost (θ R ε : ℝ) : (parameters θ R ε).cost≤50 := by norm_num [parameters,spacingExpr,precisionExpr,Expr.cost]

def shift (H D : Matrix (Fin d) (Fin d) ℂ) (s : ℝ) : Counted (Matrix (Fin d) (Fin d) ℂ) :=
  MSOwnerReport.center H (fun _:Fin 1=>D) (fun _=>s)

theorem shift_value (H D : Matrix (Fin d) (Fin d) ℂ) (s : ℝ) :
    (shift H D s).value=H+s•D := by
  rw [shift,MSOwnerReport.center_value]
  simp

theorem shift_cost (H D : Matrix (Fin d) (Fin d) ℂ) (s : ℝ) :
    (shift H D s).cost=16*d*d+1 := by
  rw [shift,MSOwnerReport.center_cost]
  ring

def slopeExpr : Expr (Fin 3) := .div (.sub (.input 0) (.input 1)) (.mul (.constant 2) (.input 2))
def slope (a b s : ℝ) : Counted ℝ :=
  ⟨slopeExpr.eval ![a,b,s],slopeExpr.cost+1⟩

theorem slope_value (a b s : ℝ) : (slope a b s).value=KSFirstDifference.sampleSlope a b s := rfl

theorem slope_valid (a b : ℝ) {s : ℝ} (hs : 0<s) : slopeExpr.Valid ![a,b,s] := by
  exact ⟨⟨trivial,trivial⟩,⟨trivial,trivial⟩,by simpa [Expr.eval] using (mul_pos (by norm_num : (0:ℝ)<2) hs).ne'⟩

theorem slope_cost (a b s : ℝ) : (slope a b s).cost≤10 := by norm_num [slope,slopeExpr,Expr.cost]

def tangent (q : Matrix (Fin d) (Fin d) ℂ → ℝ → Counted ℝ)
    (H D : Matrix (Fin d) (Fin d) ℂ) (θ R ε : ℝ) : Counted ℝ :=
  let p := parameters θ R ε
  let plus := shift H D p.value.1
  let minus := shift H D (-p.value.1)
  let a := q plus.value p.value.2
  let b := q minus.value p.value.2
  let s := slope a.value b.value p.value.1
  ⟨s.value,p.cost+plus.cost+minus.cost+a.cost+b.cost+s.cost+4⟩

variable [MSConvexOwnerValue.Oracle]

theorem tangent_value (q : Matrix (Fin d) (Fin d) ℂ → ℝ → Counted ℝ)
    (θ : ℝ) (hd : 0<d)
    (hq : ∀H ν,(q H ν).value=MSConvexCertificateReport.baseReport H θ hd ν)
    (H D : Matrix (Fin d) (Fin d) ℂ) (R ε : ℝ) :
    (tangent q H D θ R ε).value=MSConvexAnchorTangent.tangentReport H D θ R ε hd := by
  simp only [tangent,parameters_value,shift_value,hq,slope_value,neg_smul]
  rfl

theorem tangent_cost (q : Matrix (Fin d) (Fin d) ℂ → ℝ → Counted ℝ)
    (H D : Matrix (Fin d) (Fin d) ℂ) (θ R ε : ℝ) {Q : ℕ}
    (hq : ∀K,(q K (precision θ R ε)).cost≤Q) :
    (tangent q H D θ R ε).cost≤2*Q+32*d*d+70 := by
  have h1 := hq (H+spacing θ R ε•D)
  have h2 := hq (H+(-spacing θ R ε)•D)
  have hp := parameters_cost θ R ε
  have hs := slope_cost
    (q (H+spacing θ R ε•D) (precision θ R ε)).value
    (q (H+(-spacing θ R ε)•D) (precision θ R ε)).value (spacing θ R ε)
  simp only [tangent,parameters_value,shift_value,shift_cost]
  nlinarith

def subtractExpr : Expr (Fin 3) := .sub (.sub (.input 0) (.input 1)) (.input 2)
def subtract (a b c : ℝ) : Counted ℝ := ⟨subtractExpr.eval ![a,b,c],subtractExpr.cost+1⟩
theorem subtract_value (a b c : ℝ) : (subtract a b c).value=a-b-c := rfl
theorem subtract_valid (a b c : ℝ) : subtractExpr.Valid ![a,b,c] := ⟨⟨trivial,trivial⟩,trivial⟩
theorem subtract_cost (a b c : ℝ) : (subtract a b c).cost=6 := rfl

def certificate
    (qo : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin N) (Fin N) ℝ → ℝ → Counted ℝ)
    (qb : Matrix (Fin d) (Fin d) ℂ → ℝ → Counted ℝ)
    (Hstar H : Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin N) (Fin N) ℝ)
    (θ R ε : ℝ) : Counted ℝ :=
  let D := shift H Hstar (-1)
  let a := qo H C (ε/3)
  let b := qb Hstar (ε/3)
  let c := tangent qb Hstar D.value θ R ε
  let result := subtract a.value b.value c.value
  ⟨result.value,D.cost+a.cost+b.cost+c.cost+result.cost+12⟩

theorem certificate_value
    (qo : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin N) (Fin N) ℝ → ℝ → Counted ℝ)
    (qb : Matrix (Fin d) (Fin d) ℂ → ℝ → Counted ℝ)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (θ : ℝ) (hd : 0<d)
    (hqo : ∀H C ν,(qo H C ν).value=MSConvexOwnerValue.report H A C θ hd ν)
    (hqb : ∀H ν,(qb H ν).value=MSConvexCertificateReport.baseReport H θ hd ν)
    (Hstar H : Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin N) (Fin N) ℝ) (R ε : ℝ) :
    (certificate qo qb Hstar H C θ R ε).value=
      MSConvexValueCertificate.report Hstar H A C θ R ε hd := by
  simp only [certificate,shift_value,neg_one_smul,←sub_eq_add_neg,hqo,hqb,
    tangent_value qb θ hd hqb,subtract_value]
  rfl

theorem certificate_cost
    (qo : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin N) (Fin N) ℝ → ℝ → Counted ℝ)
    (qb : Matrix (Fin d) (Fin d) ℂ → ℝ → Counted ℝ)
    (Hstar H : Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin N) (Fin N) ℝ)
    (θ R ε : ℝ) {Q : ℕ}
    (hqo : (qo H C (ε/3)).cost≤Q) (hqb : (qb Hstar (ε/3)).cost≤Q)
    (hqt : ∀K,(qb K (precision θ R ε)).cost≤Q) :
    (certificate qo qb Hstar H C θ R ε).cost≤4*Q+48*d*d+100 := by
  have ht := tangent_cost qb Hstar (H+(-1:ℝ)•Hstar) θ R ε hqt
  simp only [certificate,shift_value,shift_cost,subtract_cost]
  nlinarith

attribute [local instance] Classical.propDecidable

def thresholdExpr (a : ℚ) : Expr (Fin 1) := .mul (.constant a) (.input 0)
def decision (failed : Bool) (s psi tan : ℝ) : Counted Bool :=
  ⟨!failed && decide (psi≤(thresholdExpr (33/2)).eval ![s]) &&
    decide (tan≤(thresholdExpr (9/2)).eval ![s]),
    (thresholdExpr (33/2)).cost+(thresholdExpr (9/2)).cost+12⟩

theorem decision_value (failed : Bool) (s psi tan : ℝ) :
    (decision failed s psi tan).value=MSManuscriptNumericalAcceptance.acceptReports failed s psi tan := by
  simp [decision,thresholdExpr,Expr.eval,MSManuscriptNumericalAcceptance.acceptReports]

theorem thresholdExpr_valid (a : ℚ) (s : ℝ) : (thresholdExpr a).Valid ![s] := ⟨trivial,trivial⟩
theorem decision_cost (failed : Bool) (s psi tan : ℝ) : (decision failed s psi tan).cost=18 := rfl

def acceptance
    (qo : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin N) (Fin N) ℝ → ℝ → Counted ℝ)
    (qb : Matrix (Fin d) (Fin d) ℂ → ℝ → Counted ℝ)
    (cfg : MSManuscriptNumericalAcceptance.Config N d)
    (e : MSManuscriptNumericalAcceptance.Endpoint N d) : Counted Bool :=
  let ε := MSManuscriptNumericalAcceptance.tolerance cfg
  let p := certificate qo qb cfg.savedCenter e.center e.covariance cfg.theta cfg.radius ε
  let t := tangent qb cfg.savedCenter e.movementSum cfg.theta cfg.radius ε
  let a := decision e.cleaningFailed (MSManuscriptNumericalAcceptance.scale cfg) p.value t.value
  ⟨a.value,p.cost+t.cost+a.cost+12⟩

theorem acceptance_value
    (qo : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin N) (Fin N) ℝ → ℝ → Counted ℝ)
    (qb : Matrix (Fin d) (Fin d) ℂ → ℝ → Counted ℝ)
    (cfg : MSManuscriptNumericalAcceptance.Config N d)
    (e : MSManuscriptNumericalAcceptance.Endpoint N d)
    (hqo : ∀H C ν,(qo H C ν).value=MSConvexOwnerValue.report H cfg.family C cfg.theta cfg.dimension_pos ν)
    (hqb : ∀H ν,(qb H ν).value=MSConvexCertificateReport.baseReport H cfg.theta cfg.dimension_pos ν) :
    (acceptance qo qb cfg e).value=MSConvexValueAcceptance.accepts cfg e := by
  simp only [acceptance,certificate_value qo qb cfg.family cfg.theta cfg.dimension_pos hqo hqb,
    tangent_value qb cfg.theta cfg.dimension_pos hqb,decision_value]
  rfl

theorem acceptance_cost
    (qo : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin N) (Fin N) ℝ → ℝ → Counted ℝ)
    (qb : Matrix (Fin d) (Fin d) ℂ → ℝ → Counted ℝ)
    (cfg : MSManuscriptNumericalAcceptance.Config N d)
    (e : MSManuscriptNumericalAcceptance.Endpoint N d) {Q : ℕ}
    (hqo : (qo e.center e.covariance (MSManuscriptNumericalAcceptance.tolerance cfg/3)).cost≤Q)
    (hqb : (qb cfg.savedCenter (MSManuscriptNumericalAcceptance.tolerance cfg/3)).cost≤Q)
    (hqt : ∀K,(qb K (precision cfg.theta cfg.radius (MSManuscriptNumericalAcceptance.tolerance cfg))).cost≤Q) :
    (acceptance qo qb cfg e).cost≤6*Q+80*d*d+200 := by
  have hp := certificate_cost qo qb cfg.savedCenter e.center e.covariance cfg.theta cfg.radius
    (MSManuscriptNumericalAcceptance.tolerance cfg) hqo hqb hqt
  have ht := tangent_cost qb cfg.savedCenter e.movementSum cfg.theta cfg.radius
    (MSManuscriptNumericalAcceptance.tolerance cfg) hqt
  simp only [acceptance,decision_cost]
  nlinarith

end MatrixSpencer.RealRAM.MSValueAcceptance
