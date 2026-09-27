import FaithfulMS.RectangularDirectCompiledEpoch
import FaithfulMS.RectangularDirectEpochAcceptanceData

/-! Materialized inputs and complete cost of the actual epoch acceptance.
All three physical matrix centers, the owner covariance, live count, scalar
parameters and final finite SDP queries are computed by the displayed routines. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularDirectEndpointInputs
open RealRAM.JacobiIteration (Counted)
open RectangularRidgeEpochInput RectangularDirectEpochRun
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgeEndpointWorkCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
attribute [local instance] Classical.propDecidable

theorem live_scan (c : Config N d) :
    (RectangularRidgeStateWork.liveLabels c.start (List.finRange N)).value.length=live c := by
  rw [RectangularRidgeStateWork.liveLabels_value]
  rfl

def config (a : Fin d) (c : Config N d) : Counted (RectangularDirectAcceptance.Config N d) :=
  let H:=RectangularDirectCompiledEpoch.parameters c c.start
  let v:=RectangularRidgeEpochSetup.setup c
  let L:=RectangularRidgeStateWork.liveLabels c.start (List.finRange N)
  ⟨{anchor:=H.value.center,atoms:=c.atoms,hermitian:=c.hermitian,
    depth:=v.value.depth,
    depth_pos:=by rw [RectangularRidgeEpochSetup.setup_depth];exact RectangularRidgeTuning.depth_positive N d c.count_pos,
    theta:=v.value.theta,
    theta_pos:=by rw [RectangularRidgeEpochSetup.setup_theta];exact RectangularRidgePrimitiveParameters.weight_positive c.count_pos c.rectangular,
    ridge:=v.value.fixed .ridge,
    ridge_pos:=by
      rw [RectangularRidgeEpochSetup.setup_fixed]
      exact (RectangularDirectEpochAcceptanceData.acceptanceConfig a c).ridge_pos,
    radius:=v.value.fixed .radius,
    radius_nonneg:=by
      rw [RectangularRidgeEpochSetup.setup_fixed]
      exact mul_nonneg (by norm_num) (sq_nonneg _),
    count:=L.value.length,
    count_pos:=by rw [live_scan];have := live_large c;omega,
    coordinate:=a},H.cost+v.cost+L.cost+20⟩

theorem config_value (a : Fin d) (c : Config N d) :
    (config a c).value=RectangularDirectEpochAcceptanceData.acceptanceConfig a c := by
  simp only [config,RectangularDirectCompiledEpoch.parameters_value,
    RectangularRidgeEpochSetup.setup_depth,RectangularRidgeEpochSetup.setup_theta,
    RectangularRidgeEpochSetup.setup_fixed,live_scan]
  congr 1
  simp only [RectangularRidgeEpochSetup.specified,RectangularRidgeTangentParameters.radius,
    RectangularRidgeNumericalOptimizerFloor.size,Nat.cast_add,Nat.cast_ofNat]

theorem config_cost (a : Fin d) (c : Config N d) :
    (config a c).cost≤d*d*(8*N+8)+10*d+12*N+30032 := by
  have hv:=RectangularRidgeEpochSetup.setup_cost c
  simp only [config,RectangularDirectCompiledEpoch.parameters_cost,
    RectangularRidgeStateWork.liveLabels_cost,List.length_finRange]
  nlinarith

def endpoint (c : Config N d) (s : Certified c) : Counted (RectangularDirectAcceptance.Endpoint N d) :=
  let H:=RectangularDirectCompiledEpoch.parameters c s.val.point
  let X:=RectangularDirectCompiledEpoch.parameters c s.val.centered
  let C:=RealRAM.MSGammaTop.physical s.val.owner
  ⟨{center:=H.value.center,covariance:=C.value,
    covariance_psd:=by
      rw [RealRAM.MSGammaTop.physical_value]
      exact (RectangularDirectEpochAcceptanceData.endpoint c s).covariance_psd,
    movement:=X.value.center,
    failed:=decide ((live c : ℝ)/64<s.val.paid+s.val.dust)},H.cost+X.cost+C.cost+20⟩

theorem endpoint_value (c : Config N d) (s : Certified c) :
    (endpoint c s).value=RectangularDirectEpochAcceptanceData.endpoint c s := by
  simp only [endpoint,RectangularDirectCompiledEpoch.parameters_value,RealRAM.MSGammaTop.physical_value]
  simp only [params,center,epochCenter,zero_add,RectangularDirectEpochAcceptanceData.endpoint,
    ownerPhysicalIncrement]

theorem endpoint_cost (c : Config N d) (s : Certified c) :
    (endpoint c s).cost≤2*d*d*(8*N+8)+1760*(N+1)^3+42 := by
  have hc:=RealRAM.MSGammaTop.physical_cost s.val.owner
  have hs:=s.property.1.dim_le.trans (live_le c)
  have hp : (N+s.val.owner.dim+1)^3≤8*(N+1)^3 := by
    calc _≤(2*(N+1))^3 := Nat.pow_le_pow_left (by omega) _
      _=_ := by ring
  simp only [endpoint,RectangularDirectCompiledEpoch.parameters_cost]
  nlinarith

end MatrixSpencer.RectangularDirectEndpointInputs
