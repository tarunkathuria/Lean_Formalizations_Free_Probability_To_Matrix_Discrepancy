import FaithfulMS.DirectSDP
import MatrixSpencer.RectangularRidgePreparationData

/-! Exact primal-density implementation of the rectangular covariance report.
The service supplies a maximizer of the affine SDP. Uniqueness identifies the
returned density, and the explicit transport formula computes Gamma. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularDirectSolver
open MSManuscriptSupportedOwner RectangularRidgePreparationData
open FaithfulMS.DirectDensity
abbrev Service := FaithfulMS.DirectSDP.Service
abbrev PolynomialService := FaithfulMS.DirectSDP.PolynomialService
variable {N d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
attribute [local instance] Classical.propDecidable

def solution (solver : Service) (_a : Fin d) (P : Parameters N d)
    (hP : P.Valid) (O : Owner N) (hO : State O) :
    RectangularSolution (P.center : Matrix (Fin d) (Fin d) ℂ)
      (mixFamily P.atoms O.frame) O.matrix (depth P) (theta P) (ridge P) :=
  solver.rectangularSolution (depth P) (RectangularRidgeTuning.depth_positive N d P.count_pos)
    P.center (mixFamily P.atoms O.frame) (mixFamily_isHermitian _ _ hP.1) O.matrix
    (hO.1.matrix_posSemidef O (by norm_num [floor]))
    (lt_of_lt_of_le (by omega) (P.count_pos.trans P.rectangular))
    (theta P) (ridge P) (RectangularRidgePrimitiveParameters.weight_positive P.count_pos P.rectangular)
    (by dsimp [ridge]; positivity)

def value (solver : Service) (a : Fin d) (P : Parameters N d) (hP : P.Valid)
    (O : Owner N) : Matrix (Fin O.dim) (Fin O.dim) ℝ :=
  if hO : State O then gamma (mixFamily P.atoms O.frame) O.matrix (solution solver a P hP O hO).density
  else 0

theorem value_eq (solver : Service) (a : Fin d) (P : Parameters N d) (hP : P.Valid)
    (O : Owner N) (hO : State O) : value solver a P hP O = gram P O := by
  rw [value, dif_pos hO, RectangularSolution.density_eq_optimizer _
    (RectangularRidgeTuning.depth_positive N d P.count_pos)
    (RectangularRidgePrimitiveParameters.weight_positive P.count_pos P.rectangular)
    (show 0 ≤ ridge P by dsimp [ridge]; positivity)]
  rfl

def report (solver : Service) (a : Fin d) (P : Parameters N d) (hP : P.Valid) : Report P where
  value := value solver a P hP
  symmetric O := by
    by_cases hO : State O
    · rw [value_eq solver a P hP O hO]
      exact gram_isSymm P hP O
    · simp [value, hO, Matrix.IsSymm]
  accuracy O hO := by
    rw [value_eq solver a P hP O hO, sub_self, map_zero, norm_zero]
    exact div_nonneg (threshold_pos P hP).le (by norm_num)

end MatrixSpencer.RectangularDirectSolver
