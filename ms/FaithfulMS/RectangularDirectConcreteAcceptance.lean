import FaithfulMS.DirectSDPPolynomialCost
import FaithfulMS.DirectAffineArithmetic
import FaithfulMS.RectangularDirectEndpointInputs
import MatrixSpencer.RealRAMMSValueAcceptance

/-! The concrete rectangular acceptance computation reads the optimizing
anchor density, evaluates its two trace pairings, and compares the resulting
certificate and tangent with the stopping thresholds. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularDirectConcreteAcceptance
open FaithfulMS RealRAM
open RealRAM.JacobiIteration (Counted)
variable {N d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

private def scaleExpr : Expr (Fin 1) := .sqrt (.input 0)
def scale (k : ℕ) : Counted ℝ :=
  ⟨scaleExpr.eval ![(k:ℝ)],scaleExpr.cost+1⟩
theorem scale_value (k : ℕ) : (scale k).value = Real.sqrt (k:ℝ) := rfl
theorem scale_cost (k : ℕ) : (scale k).cost = 3 := rfl
theorem scale_execution (k : ℕ) :
    Expr.Executes ![(k:ℝ)] scaleExpr (scale k).value scaleExpr.cost := by
  apply Expr.executes_of_valid
  exact ⟨trivial,by simp [Expr.eval]⟩

private theorem subtract_cost (a b c : ℝ) : (MSValueAcceptance.subtract a b c).cost=6 := rfl
private theorem decision_cost (f : Bool) (s p t : ℝ) :
    (MSValueAcceptance.decision f s p t).cost=18 := rfl
private theorem decision_value (f : Bool) (s p t : ℝ) :
    (MSValueAcceptance.decision f s p t).value =
      MSManuscriptNumericalAcceptance.acceptReports f s p t := by
  simp [MSValueAcceptance.decision,MSValueAcceptance.thresholdExpr,Expr.eval,
    MSManuscriptNumericalAcceptance.acceptReports]

def raw (P : DirectSDP.PolynomialService) (cfg : RectangularDirectAcceptance.Config N d)
    (e : RectangularDirectAcceptance.Endpoint N d) : Counted Bool :=
  let hd := Fin.pos_iff_nonempty.mpr (inferInstance : Nonempty (Fin d))
  let a := DirectSDPArithmetic.rectangular P cfg.depth cfg.depth_pos cfg.anchor
    (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ)) (fun i => nomatch i)
    0 Matrix.PosSemidef.zero hd cfg.theta
  let b := DirectSDPArithmetic.rectangular P cfg.depth cfg.depth_pos e.center cfg.atoms
    cfg.hermitian e.covariance e.covariance_psd hd cfg.theta
  let shift := MSValueAcceptance.shift (e.center : Matrix (Fin d) (Fin d) ℂ)
    (cfg.anchor : Matrix (Fin d) (Fin d) ℂ) (-1)
  let u := DirectMatrixArithmetic.tracePair a.value.density shift.value
  let v := DirectMatrixArithmetic.tracePair a.value.density (e.movement : Matrix (Fin d) (Fin d) ℂ)
  let psi := MSValueAcceptance.subtract b.value.value a.value.value u.value
  let s := scale cfg.count
  let out := MSValueAcceptance.decision e.failed s.value psi.value v.value
  ⟨out.value,a.cost+b.cost+shift.cost+u.cost+v.cost+psi.cost+s.cost+out.cost⟩

theorem raw_value (P : DirectSDP.PolynomialService) (cfg : RectangularDirectAcceptance.Config N d)
    (e : RectangularDirectAcceptance.Endpoint N d) (hκ : cfg.ridge=1/d) :
    (raw P cfg e).value = RectangularDirectAcceptance.accepts P.service cfg e := by
  have hd : 0 < d := Fin.pos_iff_nonempty.mpr inferInstance
  have ha : (DirectSDPArithmetic.rectangular P cfg.depth cfg.depth_pos cfg.anchor
      (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ)) (fun i => nomatch i)
      0 Matrix.PosSemidef.zero hd cfg.theta).value.density =
      (RectangularDirectAcceptance.anchorSolution P.service cfg).density := by
    rw [DirectSDPArithmetic.rectangular_density _ _ _ _ _ _ _ _ _ _ cfg.theta_pos]
    rw [DirectDensity.RectangularSolution.saved_density_eq _ cfg.depth_pos cfg.theta_pos (by positivity),
      RectangularDirectAcceptance.anchor_density_eq,hκ]
  have hv : (DirectSDPArithmetic.rectangular P cfg.depth cfg.depth_pos cfg.anchor
      (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ)) (fun i => nomatch i)
      0 Matrix.PosSemidef.zero hd cfg.theta).value.value =
      RectangularDirectAcceptance.anchorValue P.service cfg := by
    rw [DirectSDPArithmetic.rectangular_value _ _ _ _ _ _ _ _ _ _ cfg.theta_pos,
      RectangularDirectAcceptance.anchorValue_eq]
    have hB : covarianceKraus (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ))
        (0 : Matrix Empty Empty ℝ) = (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ)) :=
      funext (fun i => nomatch i)
    rw [hB,RectangularRidgeCertificate.empty_potential_eq_base,hκ]
    rfl
  have he : (DirectSDPArithmetic.rectangular P cfg.depth cfg.depth_pos e.center cfg.atoms
      cfg.hermitian e.covariance e.covariance_psd hd cfg.theta).value.value =
      RectangularRidgeCovarianceCalculus.ownerObjective cfg.depth e.center cfg.atoms e.covariance
        cfg.theta cfg.ridge (RectangularDirectAcceptance.endpointSolution P.service cfg e).density := by
    rw [DirectSDPArithmetic.rectangular_value _ _ _ _ _ _ _ _ _ _ cfg.theta_pos,
      (RectangularDirectAcceptance.endpointSolution P.service cfg e).owner_value_eq
        cfg.hermitian e.covariance_psd,
      RectangularRidgeCovarianceCalculus.ownerPotential_eq_densityPotential _ _ _ cfg.hermitian e.covariance_psd]
    rw [hκ]
  simp only [raw,decision_value,scale_value,MSValueAcceptance.subtract_value,
    DirectMatrixArithmetic.tracePair_value,MSValueAcceptance.shift_value,ha,hv,he,
    neg_one_smul,sub_eq_add_neg]
  simp only [RectangularDirectAcceptance.accepts,RectangularDirectAcceptance.scale,
    RectangularDirectAcceptance.psiReport,RectangularDirectAcceptance.tangentReport,sub_eq_add_neg]

private theorem queryCost_mono (P : DirectSDP.PolynomialService) {r R m M : ℕ}
    (hr : r ≤ R) (hm : m ≤ M) :
    DirectSDPArithmetic.rectangularCost P r m d ≤ DirectSDPArithmetic.rectangularCost P R M d := by
  unfold DirectSDPArithmetic.rectangularCost DirectSDPArithmetic.rectangularSize
  gcongr

theorem raw_cost (P : DirectSDP.PolynomialService) (cfg : RectangularDirectAcceptance.Config N d)
    (e : RectangularDirectAcceptance.Endpoint N d) :
    (raw P cfg e).cost ≤ 2*DirectSDPArithmetic.rectangularCost P N cfg.depth d+100*(d+1)^2 := by
  unfold raw
  dsimp only
  have ha := DirectSDPArithmetic.rectangular_cost_le P cfg.depth cfg.depth_pos cfg.anchor
    (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ)) (fun i => nomatch i)
    0 Matrix.PosSemidef.zero (Fin.pos_iff_nonempty.mpr inferInstance) cfg.theta
  have ha' : DirectSDPArithmetic.rectangularCost P (Fintype.card Empty) cfg.depth d ≤
      DirectSDPArithmetic.rectangularCost P N cfg.depth d := queryCost_mono P (by simp) le_rfl
  have hb := DirectSDPArithmetic.rectangular_cost_le P cfg.depth cfg.depth_pos e.center cfg.atoms
    cfg.hermitian e.covariance e.covariance_psd (Fin.pos_iff_nonempty.mpr inferInstance) cfg.theta
  simp only [Fintype.card_fin] at hb
  rw [MSValueAcceptance.shift_cost,subtract_cost,scale_cost,decision_cost]
  have ht (X Y : Matrix (Fin d) (Fin d) ℂ) := DirectMatrixArithmetic.tracePair_cost X Y
  calc
    _ ≤ DirectSDPArithmetic.rectangularCost P N cfg.depth d+
        DirectSDPArithmetic.rectangularCost P N cfg.depth d+(16*d*d+1)+
          (d*(16*d+3)+2)+(d*(16*d+3)+2)+6+3+18 := by
      gcongr
      · exact ha.trans ha'
      · exact ht _ _
      · exact ht _ _
    _ ≤ _ := by nlinarith

def accepts (P : DirectSDP.PolynomialService) (a : Fin d)
    (c : RectangularRidgeEpochInput.Config N d) (s : RectangularDirectEpochRun.Certified c) : Counted Bool :=
  let cfg := RectangularDirectEndpointInputs.config a c
  let e := RectangularDirectEndpointInputs.endpoint c s
  let out := raw P cfg.value e.value
  ⟨out.value,cfg.cost+e.cost+out.cost⟩

theorem accepts_value (P : DirectSDP.PolynomialService) (a : Fin d)
    (c : RectangularRidgeEpochInput.Config N d) (s : RectangularDirectEpochRun.Certified c) :
    (accepts P a c s).value = RectangularDirectEpochAcceptanceData.accepts P.service a c s := by
  simp only [accepts,RectangularDirectEndpointInputs.config_value,RectangularDirectEndpointInputs.endpoint_value]
  apply raw_value
  rfl

def acceptanceBudget (P : DirectSDP.PolynomialService) (N d : ℕ) :=
  d*d*(8*N+8)+10*d+12*N+30032 +
    (2*d*d*(8*N+8)+1760*(N+1)^3+42)+
      (2*DirectSDPArithmetic.rectangularCost P N (d+1) d+100*(d+1)^2)

theorem accepts_cost (P : DirectSDP.PolynomialService) (a : Fin d)
    (c : RectangularRidgeEpochInput.Config N d) (s : RectangularDirectEpochRun.Certified c) :
    (accepts P a c s).cost ≤ acceptanceBudget P N d := by
  have hcfg := RectangularDirectEndpointInputs.config_cost a c
  have he := RectangularDirectEndpointInputs.endpoint_cost c s
  have hr := raw_cost P (RectangularDirectEndpointInputs.config a c).value
    (RectangularDirectEndpointInputs.endpoint c s).value
  have hm : (RectangularDirectEndpointInputs.config a c).value.depth ≤ d+1 := by
    rw [RectangularDirectEndpointInputs.config_value]
    exact RectangularRidgeTuning.depth_le N d c.count_pos
  have hq := queryCost_mono (d:=d) P (show N ≤ N from le_rfl) hm
  unfold accepts acceptanceBudget
  dsimp only
  omega

theorem acceptanceBudget_polynomial (P : DirectSDP.PolynomialService) :
    NatPolynomialBound.Bounded (fun N d _ => acceptanceBudget P N d) := by
  have hn := NatPolynomialBound.first
  have hd := NatPolynomialBound.second
  have hc := NatPolynomialBound.constant
  have hdd := NatPolynomialBound.mul hd hd
  have hlinear := NatPolynomialBound.add (NatPolynomialBound.mul (hc 8) hn) (hc 8)
  have hfirst := NatPolynomialBound.add
    (NatPolynomialBound.add (NatPolynomialBound.add (NatPolynomialBound.mul hdd hlinear)
      (NatPolynomialBound.mul (hc 10) hd)) (NatPolynomialBound.mul (hc 12) hn)) (hc 30032)
  have hsecond := NatPolynomialBound.add
    (NatPolynomialBound.add (NatPolynomialBound.mul
      (NatPolynomialBound.mul (NatPolynomialBound.mul (hc 2) hd) hd) hlinear)
      (NatPolynomialBound.mul (hc 1760) (NatPolynomialBound.pow (NatPolynomialBound.add hn (hc 1)) 3)))
    (hc 42)
  have hsize := NatPolynomialBound.add
    (NatPolynomialBound.add (NatPolynomialBound.add hn (NatPolynomialBound.add hd (hc 1))) hd) (hc 1)
  have hquery : NatPolynomialBound.Bounded
      (fun N d _ => DirectSDPArithmetic.rectangularCost P N (d+1) d) :=
    NatPolynomialBound.of_le
      (NatPolynomialBound.mul (hc (1000100+P.coefficient*1000^P.degree))
        (NatPolynomialBound.pow hsize (11+6*P.degree)))
      (fun N d _ => DirectSDPArithmetic.rectangularCost_polynomial P N (d+1) d)
  exact NatPolynomialBound.add (NatPolynomialBound.add hfirst hsecond)
    (NatPolynomialBound.add (NatPolynomialBound.mul (hc 2) hquery)
      (NatPolynomialBound.mul (hc 100) (NatPolynomialBound.pow (NatPolynomialBound.add hd (hc 1)) 2)))

end MatrixSpencer.RectangularDirectConcreteAcceptance
