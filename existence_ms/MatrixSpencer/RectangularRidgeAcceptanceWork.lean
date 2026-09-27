import MatrixSpencer.RectangularRidgeTangentWork
import MatrixSpencer.RectangularRidgeSDPSetup

/-! The six-query acceptance routine with actual SDP coefficient construction.
Each query evaluates the affine coefficient circuits before invoking the
permitted polynomial convex solver. Center differences, finite-difference
parameters, report subtraction and the Boolean filter use primitive arithmetic.
The final uniform bound includes all six materializations and solves. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeAcceptanceWork
open RealRAM.JacobiIteration (Counted)
open RectangularRidgeSolverCertificate RectangularRidgeTangentParameters
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgeAcceptanceWorkCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeAcceptanceWorkSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
set_option maxHeartbeats 600000
set_option maxRecDepth 4000

/-- These arithmetic identities do not require a square-potential oracle. -/
theorem subtract_value (a b c : ℝ) :
    (RealRAM.MSValueAcceptance.subtract a b c).value=a-b-c := rfl
theorem subtract_cost (a b c : ℝ) :
    (RealRAM.MSValueAcceptance.subtract a b c).cost=6 := rfl
theorem decision_value (failed : Bool) (s psi tan : ℝ) :
    (RealRAM.MSValueAcceptance.decision failed s psi tan).value=
      MSManuscriptNumericalAcceptance.acceptReports failed s psi tan := by
  simp [RealRAM.MSValueAcceptance.decision,RealRAM.MSValueAcceptance.thresholdExpr,
    RealRAM.Expr.eval,MSManuscriptNumericalAcceptance.acceptReports]
theorem decision_cost (failed : Bool) (s psi tan : ℝ) :
    (RealRAM.MSValueAcceptance.decision failed s psi tan).cost=18 := rfl

def base (P : RectangularRidgeConvexValue.PolynomialSolver) (m : ℕ) (hm : 1 ≤ m)
    (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (θ ν : ℝ) : Counted ℝ :=
  RealRAM.RectangularRidgeSDPEntries.report P m hm a H emptyFamily emptyFamily_hermitian 0 θ ν

theorem base_value (P : RectangularRidgeConvexValue.PolynomialSolver) (m : ℕ) (hm : 1 ≤ m)
    (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (θ ν : ℝ) :
    (base P m hm a H θ ν).value=baseReport P.solver m hm a H θ (1/(d : ℝ)) ν := by
  rw [base,RealRAM.RectangularRidgeSDPEntries.report_value]
  rfl

def tangent (P : RectangularRidgeConvexValue.PolynomialSolver) (m : ℕ) (hm : 1 ≤ m)
    (a : Fin d) (H X : Matrix (Fin d) (Fin d) ℂ) (θ R ε : ℝ) : Counted ℝ :=
  RealRAM.MSValueAcceptance.tangent (fun K ν=>base P m hm a K θ ν) H X (1/(d : ℝ)) R ε

theorem tangent_value (P : RectangularRidgeConvexValue.PolynomialSolver) (m : ℕ) (hm : 1 ≤ m)
    (a : Fin d) (H X : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) (θ R ε : ℝ) :
    (tangent P m hm a H X θ R ε).value=
      tangentReport P.solver m hm a H X θ (1/(d : ℝ)) R ε := by
  simp only [tangent,RealRAM.MSValueAcceptance.tangent,RealRAM.MSValueAcceptance.parameters_value,RealRAM.MSValueAcceptance.shift_value,base_value,RealRAM.MSValueAcceptance.slope_value,neg_smul]
  rfl

def sixthExpr : RealRAM.Expr (Fin 1) := .div (.input 0) (.constant 6)
def sixth (ε : ℝ) : Counted ℝ := ⟨sixthExpr.eval ![ε],sixthExpr.cost+1⟩
theorem sixth_value (ε : ℝ) : (sixth ε).value=ε/6 := rfl
theorem sixth_cost (ε : ℝ) : (sixth ε).cost=4 := rfl
theorem sixth_executes (ε : ℝ) : RealRAM.Expr.Executes ![ε] sixthExpr (ε/6) 3 := by
  exact RealRAM.Expr.executes_of_valid ![ε] sixthExpr
    ⟨trivial,trivial,by norm_num [RealRAM.Expr.eval]⟩

def certificate (P : RectangularRidgeConvexValue.PolynomialSolver) (m : ℕ) (hm : 1 ≤ m)
    (a : Fin d) (Hstar H : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) (θ R ε : ℝ) : Counted ℝ :=
  let precision:=sixth ε
  let X:=RealRAM.MSValueAcceptance.shift H Hstar (-1)
  let owner:=RealRAM.RectangularRidgeSDPEntries.report P m hm a H A hA C θ precision.value
  let anchor:=base P m hm a Hstar θ precision.value
  let tan:=tangent P m hm a Hstar X.value θ R ε
  let result:=RealRAM.MSValueAcceptance.subtract owner.value anchor.value tan.value
  ⟨result.value,precision.cost+X.cost+owner.cost+anchor.cost+tan.cost+result.cost+12⟩

theorem certificate_value (P : RectangularRidgeConvexValue.PolynomialSolver)
    (m : ℕ) (hm : 1 ≤ m) (a : Fin d)
    (Hstar H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) (hC : (C : Matrix (Fin N) (Fin N) ℝ).PosSemidef)
    (θ R ε : ℝ) :
    (certificate P m hm a Hstar H A hA C θ R ε).value=
      certificateReport P.solver m hm a Hstar H A hA C hC θ (1/(d : ℝ)) R ε := by
  simp only [certificate,sixth_value,RealRAM.MSValueAcceptance.shift_value,neg_one_smul,←sub_eq_add_neg,
    RealRAM.RectangularRidgeSDPEntries.report_value,base_value,subtract_value]
  rw [show ((H : Matrix (Fin d) (Fin d) ℂ)-(Hstar : Matrix (Fin d) (Fin d) ℂ))=
    ((H-Hstar : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ) from rfl,
    tangent_value]
  rfl

def scaleExpr : RealRAM.Expr (Fin 1) := .sqrt (.input 0)
def scale (count : ℕ) : Counted ℝ := ⟨scaleExpr.eval ![(count : ℝ)],scaleExpr.cost+1⟩
theorem scale_value (count : ℕ) : (scale count).value=Real.sqrt (count : ℝ) := rfl
theorem scale_cost (count : ℕ) : (scale count).cost=3 := rfl
theorem scale_executes (count : ℕ) :
    RealRAM.Expr.Executes ![(count : ℝ)] scaleExpr (Real.sqrt (count : ℝ)) 2 := by
  exact RealRAM.Expr.executes_of_valid _ _ ⟨trivial,by simp [RealRAM.Expr.eval]⟩

def acceptance (P : RectangularRidgeConvexValue.PolynomialSolver)
    (cfg : RectangularRidgeSolverAcceptance.Config N d)
    (e : RectangularRidgeSolverAcceptance.Endpoint N d) : Counted Bool :=
  let C : selfAdjoint (Matrix (Fin N) (Fin N) ℝ):=⟨e.covariance,e.covariance_psd.isHermitian⟩
  let psi:=certificate P cfg.depth cfg.depth_pos cfg.coordinate cfg.anchor e.center
    cfg.atoms cfg.hermitian C cfg.theta cfg.radius tolerance
  let tan:=tangent P cfg.depth cfg.depth_pos cfg.coordinate cfg.anchor e.movement
    cfg.theta cfg.radius tolerance
  let s:=scale cfg.count
  let result:=RealRAM.MSValueAcceptance.decision e.failed s.value psi.value tan.value
  ⟨result.value,psi.cost+tan.cost+s.cost+result.cost+12⟩

theorem acceptance_value (P : RectangularRidgeConvexValue.PolynomialSolver)
    (cfg : RectangularRidgeSolverAcceptance.Config N d)
    (e : RectangularRidgeSolverAcceptance.Endpoint N d) (hκ : cfg.ridge=1/(d : ℝ)) :
    (acceptance P cfg e).value=RectangularRidgeSolverAcceptance.accepts P.solver cfg e := by
  simp only [acceptance,scale_value,decision_value]
  rw [certificate_value P cfg.depth cfg.depth_pos cfg.coordinate cfg.anchor e.center
    cfg.atoms cfg.hermitian _ e.covariance_psd,tangent_value]
  simp only [RectangularRidgeSolverAcceptance.accepts,RectangularRidgeSolverAcceptance.psiReport,
    RectangularRidgeSolverAcceptance.tangentReport,RectangularRidgeSolverAcceptance.scale,
    RectangularRidgeSolverAcceptance.tolerance,hκ]

def queryBound (P : RectangularRidgeConvexValue.PolynomialSolver) (N d V : ℕ) : ℕ :=
  1000000*(N+2*d+2)^11+RectangularRidgeTangentWork.queryBound P d V

theorem primitive_base_cost (P : RectangularRidgeConvexValue.PolynomialSolver)
    (hN : 1 ≤ N) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (θ : ℝ)
    {ν : ℝ} (hν : 0<ν) {V : ℕ} (hV : ν⁻¹≤(V : ℝ)) :
    (base P (RectangularRidgeTuning.depth N d hN) (RectangularRidgeTuning.depth_positive N d hN)
      a H θ ν).cost≤queryBound P N d V := by
  apply (RealRAM.RectangularRidgeSDPEntries.primitive_report_cost_le P hN a H emptyFamily emptyFamily_hermitian 0 θ hν hV).trans
  unfold queryBound RectangularRidgeTangentWork.queryBound
  simp only [Fintype.card_empty,zero_add]
  gcongr
  omega

theorem fixed_precision_bound (hN : 1 ≤ N) (a : Fin d) :
    0<RectangularRidgeTangentValues.precision (1/(d : ℝ)) (radius ((d+N+2 : ℕ) : ℝ)) tolerance ∧
    (RectangularRidgeTangentValues.precision (1/(d : ℝ)) (radius ((d+N+2 : ℕ) : ℝ)) tolerance)⁻¹≤
      ((68400000000*(d+N+2)^5 : ℕ) : ℝ) := by
  have hd : 1 ≤ d := by have := a.isLt; omega
  have hs : (1 : ℝ)≤((d+N+2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ d+N+2)
  have hd' : (1 : ℝ)≤d := by exact_mod_cast hd
  have hds : (d : ℝ)≤((d+N+2 : ℕ) : ℝ) := by exact_mod_cast (by omega : d≤d+N+2)
  refine ⟨RectangularRidgeTangentValues.precision_pos
    (by positivity) (by norm_num [tolerance]),?_⟩
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using (fixed_inverse_bounds hs hd' hds).2

theorem primitive_tangent_cost (P : RectangularRidgeConvexValue.PolynomialSolver)
    (hN : 1 ≤ N) (a : Fin d) (H X : Matrix (Fin d) (Fin d) ℂ) (θ : ℝ) :
    (tangent P (RectangularRidgeTuning.depth N d hN) (RectangularRidgeTuning.depth_positive N d hN)
      a H X θ (radius ((d+N+2 : ℕ) : ℝ)) tolerance).cost≤
      2*queryBound P N d (68400000000*(d+N+2)^5)+32*d*d+70 :=
  RectangularRidgeTangentWork.finite_tangent_cost _ _ _ _ _ _
    (fun K=>primitive_base_cost P hN a K θ (fixed_precision_bound hN a).1
      (fixed_precision_bound hN a).2)

theorem sixth_inverse_bound (hN : 1 ≤ N) :
    (tolerance/6)⁻¹≤((68400000000*(d+N+2)^5 : ℕ) : ℝ) := by
  have hs : (1 : ℝ)≤((d+N+2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ d+N+2)
  have hp : (1 : ℝ)≤((d+N+2 : ℕ) : ℝ)^5 := one_le_pow₀ hs
  norm_num [tolerance]
  push_cast at hp
  linarith

theorem primitive_certificate_cost (P : RectangularRidgeConvexValue.PolynomialSolver)
    (hN : 1 ≤ N) (a : Fin d) (Hstar H : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) (θ : ℝ) :
    (certificate P (RectangularRidgeTuning.depth N d hN) (RectangularRidgeTuning.depth_positive N d hN)
      a Hstar H A hA C θ (radius ((d+N+2 : ℕ) : ℝ)) tolerance).cost≤
      4*queryBound P N d (68400000000*(d+N+2)^5)+48*d*d+110 := by
  have hν : 0<tolerance/6 := by norm_num [tolerance]
  have ho:=RealRAM.RectangularRidgeSDPEntries.primitive_report_cost_le P hN a H A hA C θ hν (sixth_inverse_bound (d:=d) hN)
  simp only [Fintype.card_fin] at ho
  have hb:=primitive_base_cost P hN a Hstar θ hν (sixth_inverse_bound (d:=d) hN)
  have ht:=primitive_tangent_cost P hN a Hstar (H+(-1 : ℝ)•Hstar) θ
  change _≤queryBound P N d (68400000000*(d+N+2)^5) at ho
  simp only [certificate,sixth_value,sixth_cost,RealRAM.MSValueAcceptance.shift_value,RealRAM.MSValueAcceptance.shift_cost,subtract_cost]
  nlinarith

/-- A polynomial bound for the actual materialized acceptance routine. Its
only numerical oracle is the supplied polynomial accurate affine-LMI solver. -/
theorem primitive_acceptance_cost (P : RectangularRidgeConvexValue.PolynomialSolver)
    (hN : 1 ≤ N) (cfg : RectangularRidgeSolverAcceptance.Config N d)
    (e : RectangularRidgeSolverAcceptance.Endpoint N d)
    (hm : cfg.depth=RectangularRidgeTuning.depth N d hN)
    (hR : cfg.radius=radius ((d+N+2 : ℕ) : ℝ)) :
    (acceptance P cfg e).cost≤
      6*queryBound P N d (68400000000*(d+N+2)^5)+80*d*d+220 := by
  let C : selfAdjoint (Matrix (Fin N) (Fin N) ℝ):=⟨e.covariance,e.covariance_psd.isHermitian⟩
  have hp:=primitive_certificate_cost P hN cfg.coordinate cfg.anchor e.center
    cfg.atoms cfg.hermitian C cfg.theta
  have ht:=primitive_tangent_cost P hN cfg.coordinate cfg.anchor e.movement cfg.theta
  simp only [acceptance,scale_cost,decision_cost,hm,hR]
  nlinarith

end MatrixSpencer.RectangularRidgeAcceptanceWork
