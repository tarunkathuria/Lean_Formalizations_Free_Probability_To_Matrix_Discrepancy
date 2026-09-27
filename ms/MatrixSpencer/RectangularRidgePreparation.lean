import MatrixSpencer.RectangularRidgePreparationRun
import MatrixSpencer.RectangularRidgeSolverPreparation

/-! End-to-end finite paid preparation, using the actual finite-accuracy SDP
value report and actual finite stored-frame cleanup/Jacobi direction. The only
oracle is the explicitly stated convex value-solver contract. There is no
report-accuracy, favorable-direction, or successful-preparation assumption. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgePreparation
open MSManuscriptSupportedOwner RectangularRidgePreparationData
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgePreparationCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}

def prepare (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) : Option (Owner N × ℕ) :=
  RectangularRidgePreparationRun.output P (RectangularRidgeSolverPreparation.report solver a P hP) O

theorem prepare_isSome (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    (prepare solver a P hP O).isSome=true :=
  RectangularRidgePreparationRun.output_isSome P hP _ O hO

theorem prepare_sound (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O)
    {y : Owner N × ℕ} (ho : prepare solver a P hP O=some y) :
    RectangularRidgePreparationRun.Certificate P O (RectangularRidgePreparationRun.budget P) y :=
  RectangularRidgePreparationRun.output_sound P hP _ O hO ho

theorem prepare_paid_count (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O)
    {y : Owner N × ℕ} (ho : prepare solver a P hP O=some y) :
    (y.2:ℝ)≤(N:ℝ)/paidSize P :=
  RectangularRidgePreparationRun.output_paid_count P hP _ O hO ho

theorem prepare_unpaid_loss (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O)
    {y : Owner N × ℕ} (ho : prepare solver a P hP O=some y) :
    realTrace O.physical-realTrace y.1.physical-paidSize P*(y.2:ℝ)≤4*floor*N :=
  RectangularRidgePreparationRun.output_unpaid_loss P hP _ O hO ho

theorem prepare_range_le (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O)
    {y : Owner N × ℕ} (ho : prepare solver a P hP O=some y) :
    LinearMap.range (Matrix.toEuclideanCLM (𝕜:=ℝ) y.1.physical).toLinearMap ≤
      LinearMap.range (Matrix.toEuclideanCLM (𝕜:=ℝ) O.physical).toLinearMap :=
  RectangularRidgePreparationRun.output_range_le P hP _ O hO ho

def rounds (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) : ℕ :=
  RectangularRidgePreparationRun.tests P (RectangularRidgeSolverPreparation.report solver a P hP)
    (RectangularRidgePreparationRun.budget P) O

/-- The actual cleanup/cap-test rounds have a literal polynomial bound. -/
theorem rounds_le (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) :
    rounds solver a P hP O≤2^320*(d+N+2)^63+1 :=
  RectangularRidgePreparationRun.tests_le_fuel P _ _ O

theorem rounds_eq_paid_add_one (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N)
    {y : Owner N × ℕ} (ho : prepare solver a P hP O=some y) :
    rounds solver a P hP O=y.2+1 :=
  RectangularRidgePreparationRun.tests_of_run_some P _ _ ho

def prepareMatrix (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (C : Matrix (Fin N) (Fin N) ℝ) :=
  prepare solver a P hP (RectangularRidgePreparationRun.initial C)

theorem prepareMatrix_isSome (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (C : Matrix (Fin N) (Fin N) ℝ)
    (hfloor : floor • (1 : Matrix (Fin N) (Fin N) ℝ)≤C) (hC1 : C≤1) :
    (prepareMatrix solver a P hP C).isSome=true :=
  RectangularRidgePreparationRun.prepareMatrix_isSome P hP _ C hfloor hC1

theorem prepareIdentity_isSome (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) :
    (prepareMatrix solver a P hP (1 : Matrix (Fin N) (Fin N) ℝ)).isSome=true :=
  RectangularRidgePreparationRun.prepareIdentity_isSome P hP _

end MatrixSpencer.RectangularRidgePreparation
