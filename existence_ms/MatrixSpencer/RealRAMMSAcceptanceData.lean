import MatrixSpencer.RealRAMMSConvexAcceptance
import MatrixSpencer.RealRAMMSCleanup
import MatrixSpencer.MSConvexValueAcceptedEpoch

/-! Entry-by-entry construction of the actual square-MS acceptance endpoint
and saved report configuration. Physical covariance uses two counted matrix
products and an explicit frame transpose; the stopping failure bit uses only
its actual scalar comparison. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.RealRAM.MSAcceptanceData
open JacobiIteration (Counted)
open MSManuscriptSupportedOwner (Owner)
open MSManuscriptNumericalConfig
variable {N d : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

/-- Transpose is a scalar load/store scan over the stored frame. -/
def transpose (O : Owner N) : Counted (Matrix (Fin O.dim) (Fin N) ℝ) :=
  ⟨fun i j=>O.frame j i,2*N*O.dim+1⟩
theorem transpose_value (O : Owner N) : (transpose O).value=O.frameᵀ := rfl

def physical (O : Owner N) : Counted (Matrix (Fin N) (Fin N) ℝ) :=
  let T:=transpose O
  let A:=MSCleanup.multiply O.frame O.matrix
  let B:=MSCleanup.multiply A.value T.value
  ⟨B.value,T.cost+A.cost+B.cost+2⟩

theorem physical_value (O : Owner N) : (physical O).value=O.physical := by
  simp only [physical,transpose_value,MSCleanup.multiply_value,Owner.physical]

theorem physical_cost (O : Owner N) (hO : O.dim≤N) :
    (physical O).cost≤1000*(N+1)^3 := by
  have h1:=(MSCleanup.multiply_cost O.frame O.matrix).trans
    (Nat.mul_le_mul_left 12 (Nat.pow_le_pow_left (by omega : N+O.dim+O.dim+1≤3*N+1) 3))
  have h2:=(MSCleanup.multiply_cost (MSCleanup.multiply O.frame O.matrix).value
    (transpose O).value).trans
    (Nat.mul_le_mul_left 12 (Nat.pow_le_pow_left (by omega : N+O.dim+N+1≤3*N+1) 3))
  have hm : 2*N*O.dim≤2*N*N := Nat.mul_le_mul_left _ hO
  dsimp only [transpose] at h2
  simp only [physical,transpose]
  nlinarith

def failureExpr : Expr (Fin 3) := .add (.input 1) (.input 2)
def thresholdExpr : Expr (Fin 3) := .div (.input 0) (.constant 64)
def cleaningFailed (N : ℕ) (paid dust : ℝ) : Counted Bool :=
  ⟨decide (thresholdExpr.eval ![(N:ℝ),paid,dust] < failureExpr.eval ![(N:ℝ),paid,dust]),
    thresholdExpr.cost+failureExpr.cost+4⟩
theorem cleaningFailed_value (N : ℕ) (paid dust : ℝ) :
    (cleaningFailed N paid dust).value=decide ((N:ℝ)/64<paid+dust) := rfl
theorem failureExpr_valid (N : ℕ) (paid dust : ℝ) : failureExpr.Valid ![(N:ℝ),paid,dust] := ⟨trivial,trivial⟩
theorem thresholdExpr_valid (N : ℕ) (paid dust : ℝ) : thresholdExpr.Valid ![(N:ℝ),paid,dust] :=
  ⟨trivial,trivial,by norm_num [Expr.eval]⟩
theorem cleaningFailed_cost (N : ℕ) (paid dust : ℝ) : (cleaningFailed N paid dust).cost=10 := rfl

variable [Nonempty (Fin d)]

def endpoint (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d)
    (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) :
    Counted (MSManuscriptNumericalAcceptance.Endpoint N d) :=
  let H:=MSOwnerReport.center cfg.offset cfg.matrices (WithLp.ofLp s.val.point)
  let C:=physical s.val.owner
  let M:=MSOwnerReport.center 0 cfg.matrices (WithLp.ofLp s.val.centered)
  let f:=cleaningFailed N s.val.paid s.val.dust
  ⟨⟨H.value,C.value,M.value,f.value⟩,H.cost+C.cost+M.cost+f.cost+4⟩

theorem endpoint_value (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d)
    (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) :
    (endpoint cfg hd s).value=MSManuscriptAcceptedEpoch.endpoint cfg hd s := by
  simp only [endpoint,MSOwnerReport.center_epoch,physical_value,MSOwnerReport.center_value,
    zero_add,cleaningFailed_value,MSManuscriptAcceptedEpoch.endpoint,
    MSManuscriptInputRadius.combination,EpochConfig.center,epochCenter_coe]
  rfl

theorem endpoint_cost (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d)
    (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) :
    (endpoint cfg hd s).cost≤16*d*d*(N+1)+1000*(N+1)^3+20 := by
  have hc:=physical_cost s.val.owner s.property.1.dim_le
  simp only [endpoint,MSOwnerReport.center_cost,cleaningFailed_cost]
  nlinarith

def radiusExpr : Expr (Fin 3) :=
  .mul (.sqrt (.input 1)) (.add (.mul (.constant 2) (.input 0)) (.mul (.input 2) (.input 0)))

theorem radiusExpr_eval (ε : ℝ) : radiusExpr.eval ![(N:ℝ),(d:ℝ),ε]=
    MSManuscriptInputRadius.radius N d (ε*N) := rfl

theorem radiusExpr_valid (ε : ℝ) : radiusExpr.Valid ![(N:ℝ),(d:ℝ),ε] :=
  ⟨⟨trivial,Nat.cast_nonneg d⟩,⟨trivial,trivial⟩,trivial,trivial⟩

def reportConfig (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d) :
    Counted (MSManuscriptNumericalAcceptance.Config N d) :=
  let H:=MSOwnerReport.center cfg.offset cfg.matrices (WithLp.ofLp cfg.start)
  let R:=radiusExpr.eval ![(N:ℝ),(d:ℝ),cfg.epsilon]
  ⟨{savedCenter:=H.value,family:=cfg.matrices,theta:=1,radius:=R,count:=N,
    dimension_pos:=hd,count_pos:=count_pos cfg,theta_pos:=by norm_num,
    radius_nonneg:=by
      change 0≤radiusExpr.eval ![(N:ℝ),(d:ℝ),cfg.epsilon]
      rw [radiusExpr_eval]
      exact MSManuscriptInputRadius.radius_nonneg (mul_nonneg cfg.epsilon_pos.le (Nat.cast_nonneg N)),
    savedCenter_hermitian:=by rw [MSOwnerReport.center_epoch]; exact (cfg.center cfg.start).property,
    family_hermitian:=cfg.hermitian},
    H.cost+radiusExpr.cost+2*N*d*d+20⟩

theorem reportConfig_value (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d) :
    (reportConfig cfg hd).value=MSManuscriptAcceptedEpoch.reportConfig cfg hd := by
  have hcenter := MSOwnerReport.center_epoch cfg.offset cfg.matrices cfg.hermitian cfg.start
  simp only [reportConfig,hcenter,radiusExpr_eval,
    MSManuscriptAcceptedEpoch.reportConfig,EpochConfig.anchor,EpochConfig.center]

theorem reportConfig_cost (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d) :
    (reportConfig cfg hd).cost≤100*(N+1)*(d+1)^2 := by
  simp only [reportConfig,MSOwnerReport.center_cost]
  norm_num [radiusExpr,Expr.cost]
  nlinarith

def accepts (P : KSPolynomialConvexSolver.PolynomialSolver)
    (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d)
    (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) : Counted Bool :=
  let C:=reportConfig cfg hd
  let E:=endpoint cfg hd s
  let A:=MSConvexAcceptance.acceptance P C.value E.value
  ⟨A.value,C.cost+E.cost+A.cost+2⟩

theorem accepts_value (P : KSPolynomialConvexSolver.PolynomialSolver)
    (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d)
    (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) :
    (accepts P cfg hd s).value=
      @MSConvexValueAcceptedEpoch.accepts (MSRawOwnerReport.oracle P) N d cfg hd s := by
  simp only [accepts,reportConfig_value,endpoint_value,MSConvexAcceptance.acceptance_value]
  rfl

def epochCost (P : KSPolynomialConvexSolver.PolynomialSolver) (N d S V : ℕ) : ℕ :=
  100*(N+1)*(d+1)^2+16*d*d*(N+1)+1000*(N+1)^3+
    6*MSConvexAcceptance.queryBudget P N d S V+80*d*d+222

theorem accepts_cost (P : KSPolynomialConvexSolver.PolynomialSolver)
    (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d)
    (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) {S V : ℕ}
    (hS : KSPolynomialConvexSolver.dataSize
      (KSFullManuscriptAffineData.dimension (⟨0,hd⟩:Fin d))
      (KSFullManuscriptAffineData.matrixSize (Fin d))≤S)
    (hV : (MSManuscriptNumericalAcceptance.tolerance (MSManuscriptAcceptedEpoch.reportConfig cfg hd)/3)⁻¹≤(V:ℝ))
    (hT : (MSConvexAnchorTangent.precision 1 (MSManuscriptAcceptedEpoch.reportConfig cfg hd).radius
      (MSManuscriptNumericalAcceptance.tolerance (MSManuscriptAcceptedEpoch.reportConfig cfg hd)))⁻¹≤(V:ℝ)) :
    (accepts P cfg hd s).cost≤epochCost P N d S V := by
  have hcfg:=reportConfig_cost cfg hd
  have he:=endpoint_cost cfg hd s
  have ha:=MSConvexAcceptance.acceptance_cost P (MSManuscriptAcceptedEpoch.reportConfig cfg hd)
    (MSManuscriptAcceptedEpoch.endpoint cfg hd s) hS hV hT
  simp only [accepts,reportConfig_value,endpoint_value,epochCost]
  omega

end MatrixSpencer.RealRAM.MSAcceptanceData
