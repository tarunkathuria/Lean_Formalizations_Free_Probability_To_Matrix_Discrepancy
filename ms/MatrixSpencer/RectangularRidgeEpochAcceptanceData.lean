import MatrixSpencer.RectangularRidgeEpochSuccess
import MatrixSpencer.RectangularRidgeSolverAcceptance

/-! The literal finite SDP acceptance input of the actual ridge epoch. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeEpochAcceptanceData
open RectangularRidgeEpochInput RectangularRidgeEpochRun RectangularRidgeEpochMoments
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgeEpochAcceptDataCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeEpochAcceptDataSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
attribute [local instance] Classical.propDecidable

def acceptanceConfig (a : Fin d) (c : Config N d) : RectangularRidgeSolverAcceptance.Config N d where
  anchor := anchor c
  atoms := c.atoms
  hermitian := c.hermitian
  depth := depth c
  depth_pos := RectangularRidgeTuning.depth_positive N d c.count_pos
  theta := theta c
  theta_pos := RectangularRidgePrimitiveParameters.weight_positive c.count_pos c.rectangular
  ridge := ridge c
  ridge_pos := by
    have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by have := c.count_pos; have := c.rectangular; omega)
    exact one_div_pos.mpr hd
  radius := 3 * RectangularRidgeNumericalOptimizerFloor.size d N ^ 2
  radius_nonneg := by positivity
  count := live c
  count_pos := by have := live_large c; omega
  coordinate := a

def endpoint (c : Config N d) (s : Certified c) : RectangularRidgeSolverAcceptance.Endpoint N d where
  center := center c s.val.point
  covariance := s.val.owner.physical
  covariance_psd := s.property.1.owner_valid.physical_posSemidef _ (by norm_num [RectangularRidgePreparationData.floor])
  movement := ownerPhysicalIncrement c.atoms c.hermitian s.val.centered
  failed := decide ((live c : ℝ) / 64 < s.val.paid + s.val.dust)

def accepts (solver : RectangularRidgeConvexValue.Solver) (a : Fin d) (c : Config N d) (s : Certified c) : Bool :=
  RectangularRidgeSolverAcceptance.accepts solver (acceptanceConfig a c) (endpoint c s)

end MatrixSpencer.RectangularRidgeEpochAcceptanceData
