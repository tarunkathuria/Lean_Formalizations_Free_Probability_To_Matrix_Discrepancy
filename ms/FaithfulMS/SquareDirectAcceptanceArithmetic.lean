import FaithfulMS.SquareDirectCountedAcceptance
import FaithfulMS.DirectSDPArithmetic
import FaithfulMS.DirectAffineArithmetic
import MatrixSpencer.RealRAMMSAcceptanceData

/-! The endpoint test uses two primal SDP outputs and two ordinary matrix
traces. The supporting density is returned by the source-free saved-center
SDP; the other query evaluates the endpoint potential. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.SquareDirectAcceptanceArithmetic
open MatrixSpencer RealRAM
open RealRAM.JacobiIteration (Counted)
open MSManuscriptNumericalAcceptance (Config Endpoint)
variable {N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000
variable (P : DirectSDP.PolynomialService)

def compute (cfg : Config N d) (e : Endpoint N d) (he : e.Valid cfg) : Counted Bool :=
  let a := DirectSDPArithmetic.square P cfg.savedCenter
    (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ)) (fun i => i.elim)
    0 Matrix.PosSemidef.zero cfg.dimension_pos cfg.theta
  let b := DirectSDPArithmetic.square P e.center cfg.family cfg.family_hermitian
    e.covariance he.2.1 cfg.dimension_pos cfg.theta
  let diff := MSValueAcceptance.shift e.center cfg.savedCenter (-1)
  let tangent := DirectMatrixArithmetic.tracePair a.value.density e.movementSum
  let supporting := DirectMatrixArithmetic.tracePair a.value.density diff.value
  let gap := MSValueAcceptance.subtract b.value.value a.value.value supporting.value
  let scale : Counted ℝ := ⟨(Expr.sqrt (.input (0 : Fin 1))).eval ![(cfg.count:ℝ)],3⟩
  let test := MSValueAcceptance.decision e.cleaningFailed scale.value gap.value tangent.value
  ⟨test.value,a.cost+b.cost+diff.cost+tangent.cost+supporting.cost+gap.cost+scale.cost+test.cost+8⟩

theorem compute_value (cfg : Config N d) (e : Endpoint N d) (he : e.Valid cfg) :
    (compute P cfg e he).value = @SquareDirectAcceptance.accepts ⟨P.service⟩ N d cfg e := by
  letI : SquareDirectOracle.Oracle := ⟨P.service⟩
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp cfg.dimension_pos
  have hd : (DirectSDPArithmetic.square P cfg.savedCenter
      (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ)) (fun i => i.elim)
      0 Matrix.PosSemidef.zero cfg.dimension_pos cfg.theta).value.density =
      SquareDirectAcceptance.savedDensity cfg :=
    DirectSDPArithmetic.square_density _ _ _ _ _ _ _ _ cfg.theta_pos
  have hv : (DirectSDPArithmetic.square P cfg.savedCenter
      (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ)) (fun i => i.elim)
      0 Matrix.PosSemidef.zero cfg.dimension_pos cfg.theta).value.value =
      SquareDirectAcceptance.savedValue cfg := by
    rw [DirectSDPArithmetic.square_value _ _ _ _ _ _ _ _ cfg.theta_pos]
    exact (SquareDirectAcceptance.savedSolution cfg).owner_value_eq
      (fun i => i.elim) Matrix.PosSemidef.zero |>.symm
  simp only [compute,MSValueAcceptance.subtract_value,
    DirectMatrixArithmetic.tracePair_value,hd,hv,MSValueAcceptance.shift_value,
    neg_one_smul,←sub_eq_add_neg,
    DirectSDPArithmetic.square_value _ _ _ _ _ _ _ _ cfg.theta_pos,
    Expr.eval,Matrix.cons_val_zero,SquareDirectAcceptance.accepts,
    SquareDirectAcceptance.psiReport,SquareDirectAcceptance.tangentReport,
    SquareDirectAcceptance.endpointValue_eq cfg e he,MSManuscriptNumericalAcceptance.scale]
  simp [MSValueAcceptance.decision,MSValueAcceptance.thresholdExpr,Expr.eval,
    MSManuscriptNumericalAcceptance.acceptReports]

def reportWork (P : DirectSDP.PolynomialService) (N d : ℕ) : ℕ :=
  2*DirectSDPArithmetic.squareCost P N d+16*d*d+2*(d*(16*d+3)+2)+36

theorem compute_cost (cfg : Config N d) (e : Endpoint N d) (he : e.Valid cfg) :
    (compute P cfg e he).cost ≤ reportWork P N d := by
  have ha := DirectSDPArithmetic.square_cost_le P cfg.savedCenter
    (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ)) (fun i => i.elim)
    0 Matrix.PosSemidef.zero cfg.dimension_pos cfg.theta
  have hb := DirectSDPArithmetic.square_cost_le P e.center cfg.family cfg.family_hermitian
    e.covariance he.2.1 cfg.dimension_pos cfg.theta
  have ht := DirectMatrixArithmetic.tracePair_cost
    (DirectSDPArithmetic.square P cfg.savedCenter
      (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ)) (fun i => i.elim)
      0 Matrix.PosSemidef.zero cfg.dimension_pos cfg.theta).value.density e.movementSum
  have hc := DirectMatrixArithmetic.tracePair_cost
    (DirectSDPArithmetic.square P cfg.savedCenter
      (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ)) (fun i => i.elim)
      0 Matrix.PosSemidef.zero cfg.dimension_pos cfg.theta).value.density
    (MSValueAcceptance.shift e.center cfg.savedCenter (-1)).value
  simp only [Fintype.card_fin,Fintype.card_empty] at ha hb
  have hm : DirectSDPArithmetic.squareCost P 0 d ≤ DirectSDPArithmetic.squareCost P N d := by
    unfold DirectSDPArithmetic.squareCost
    gcongr
    exact Nat.zero_le N
  simp only [compute,MSValueAcceptance.shift_cost,MSValueAcceptance.subtract_cost,
    MSValueAcceptance.decision_cost]
  unfold reportWork
  omega

variable [Nonempty (Fin d)]

def accepts (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d)
    (s : MSManuscriptNumericalEpochRun.Certified (MSManuscriptNumericalConfig.ofEpochConfig cfg hd)) :
    Counted Bool :=
  let c := MSAcceptanceData.reportConfig cfg hd
  let e := MSAcceptanceData.endpoint cfg hd s
  have he : e.value.Valid c.value := by
    rw [MSAcceptanceData.endpoint_value,MSAcceptanceData.reportConfig_value]
    exact MSManuscriptAcceptedEpoch.endpoint_valid cfg hd s
  let t := compute P c.value e.value he
  ⟨t.value,c.cost+e.cost+t.cost+2⟩

theorem accepts_value (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d)
    (s : MSManuscriptNumericalEpochRun.Certified (MSManuscriptNumericalConfig.ofEpochConfig cfg hd)) :
    (accepts P cfg hd s).value = @SquareDirectAcceptedEpoch.accepts ⟨P.service⟩ N d cfg hd s := by
  letI : SquareDirectOracle.Oracle := ⟨P.service⟩
  simp only [accepts,compute_value,MSAcceptanceData.reportConfig_value,MSAcceptanceData.endpoint_value]
  rfl

def work (P : DirectSDP.PolynomialService) (N d : ℕ) : ℕ :=
  100*(N+1)*(d+1)^2+16*d*d*(N+1)+1000*(N+1)^3+reportWork P N d+22

theorem accepts_cost (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d)
    (s : MSManuscriptNumericalEpochRun.Certified (MSManuscriptNumericalConfig.ofEpochConfig cfg hd)) :
    (accepts P cfg hd s).cost ≤ work P N d := by
  have hc := MSAcceptanceData.reportConfig_cost cfg hd
  have he := MSAcceptanceData.endpoint_cost cfg hd s
  have ht := compute_cost P (MSAcceptanceData.reportConfig cfg hd).value
    (MSAcceptanceData.endpoint cfg hd s).value (by
      rw [MSAcceptanceData.endpoint_value,MSAcceptanceData.reportConfig_value]
      exact MSManuscriptAcceptedEpoch.endpoint_valid cfg hd s)
  dsimp only [accepts]
  unfold work
  omega

def evaluation (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d) :
    @SquareDirectCountedAcceptance.Evaluation ⟨P.service⟩ N d cfg hd := by
  letI : SquareDirectOracle.Oracle := ⟨P.service⟩
  exact ⟨accepts P cfg hd, accepts_value P cfg hd⟩

theorem work_mono {m N d : ℕ} (h : m ≤ N) : work P m d ≤ work P N d := by
  unfold work reportWork DirectSDPArithmetic.squareCost
  gcongr

end FaithfulMS.SquareDirectAcceptanceArithmetic
