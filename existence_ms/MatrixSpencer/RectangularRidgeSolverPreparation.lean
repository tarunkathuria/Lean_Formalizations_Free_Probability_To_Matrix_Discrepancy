import MatrixSpencer.RectangularRidgeSolverGamma
import MatrixSpencer.RectangularRidgePreparationData

/-! The accurate-report interface of the concrete rectangular preparation
is discharged by the actual finite SDP-value differences. Symmetrization is
ordinary entry arithmetic and equals the stored covariance on valid states. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeSolverPreparation
open MSManuscriptSupportedOwner RectangularRidgePreparationData
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgeSolverPreparationCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeSolverPreparationSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance

def coefficients (O : Owner N) : selfAdjoint (Matrix (Fin O.dim) (Fin O.dim) ℝ) :=
  selfAdjointPart ℝ O.matrix

theorem coefficients_eq (O : Owner N) (hO : State O) :
    (coefficients O : Matrix (Fin O.dim) (Fin O.dim) ℝ)=O.matrix :=
  IsSelfAdjoint.coe_selfAdjointPart_apply ℝ
    (hO.1.matrix_posSemidef O (by norm_num [floor])).isHermitian

def value (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) : Matrix (Fin O.dim) (Fin O.dim) ℝ :=
  RectangularRidgeSolverGamma.report solver a P.center P.atoms hP.1 O.frame P.count_pos (coefficients O)

def report (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) : Report P where
  value := value solver a P hP
  symmetric O := RectangularRidgeSolverGamma.report_isSymm solver a P.center P.atoms hP.1
    O.frame P.count_pos (coefficients O)
  accuracy O hO := by
    have he := coefficients_eq O hO
    have hf : floor • (1 : Matrix (Fin O.dim) (Fin O.dim) ℝ)≤coefficients O := by rw [he]; exact hO.1.2
    have hc : (coefficients O : Matrix (Fin O.dim) (Fin O.dim) ℝ)≤1 := by
      rw [he]
      exact MSManuscriptFrameFamily.stored_matrix_le_one O hO.1 hO.2.1
    have hp : covarianceLift O.frame (coefficients O)≤1 := by rw [he]; exact hO.2.1
    have hh := RectangularRidgeSolverGamma.report_accuracy solver a P.center P.atoms hP.1 hP.2.1
      O.frame hO.1.1 P.count_pos P.rectangular hO.2.2 hP.2.2.1 (coefficients O)
      (δ:=floor) (by norm_num [floor]) (by norm_num [floor]) hf hc hp hP.2.2.2
    change ‖Matrix.toEuclideanCLM (𝕜:=ℝ)
      (RectangularRidgePaidQueries.gram P.center (mixFamily P.atoms O.frame) (coefficients O)
        (depth P) (theta P) (ridge P)-value solver a P hP O)‖≤P.threshold/64 at hh
    rwa [he] at hh

end MatrixSpencer.RectangularRidgeSolverPreparation
