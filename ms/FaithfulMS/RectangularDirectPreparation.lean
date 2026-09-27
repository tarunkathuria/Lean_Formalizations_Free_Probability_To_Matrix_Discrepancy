import FaithfulMS.RectangularDirectPreparationRun
import FaithfulMS.RectangularDirectSolver

/-! Finite paid preparation from the optimizing SDP density. The covariance
response is its transport Gram matrix; exact EVD identifies an over-budget
direction. Stored-frame cleanup remains the certified finite cleanup routine.
The report, direction certificate and preparation termination are derived. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularDirectPreparation
open MSManuscriptSupportedOwner RectangularRidgePreparationData
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgePreparationCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}

def prepare (solver : RectangularDirectSolver.Service) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) : Option (Owner N × ℕ) :=
  RectangularDirectPreparationRun.output P (RectangularDirectSolver.report solver a P hP) O

theorem prepare_isSome (solver : RectangularDirectSolver.Service) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    (prepare solver a P hP O).isSome=true :=
  RectangularDirectPreparationRun.output_isSome P hP _ O hO

theorem prepare_sound (solver : RectangularDirectSolver.Service) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O)
    {y : Owner N × ℕ} (ho : prepare solver a P hP O=some y) :
    RectangularDirectPreparationRun.Certificate P O (RectangularDirectPreparationRun.budget P) y :=
  RectangularDirectPreparationRun.output_sound P hP _ O hO ho

theorem prepare_paid_count (solver : RectangularDirectSolver.Service) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O)
    {y : Owner N × ℕ} (ho : prepare solver a P hP O=some y) :
    (y.2:ℝ)≤(N:ℝ)/paidSize P :=
  RectangularDirectPreparationRun.output_paid_count P hP _ O hO ho

theorem prepare_unpaid_loss (solver : RectangularDirectSolver.Service) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O)
    {y : Owner N × ℕ} (ho : prepare solver a P hP O=some y) :
    realTrace O.physical-realTrace y.1.physical-paidSize P*(y.2:ℝ)≤4*floor*N :=
  RectangularDirectPreparationRun.output_unpaid_loss P hP _ O hO ho

theorem prepare_range_le (solver : RectangularDirectSolver.Service) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O)
    {y : Owner N × ℕ} (ho : prepare solver a P hP O=some y) :
    LinearMap.range (Matrix.toEuclideanCLM (𝕜:=ℝ) y.1.physical).toLinearMap ≤
      LinearMap.range (Matrix.toEuclideanCLM (𝕜:=ℝ) O.physical).toLinearMap :=
  RectangularDirectPreparationRun.output_range_le P hP _ O hO ho

def rounds (solver : RectangularDirectSolver.Service) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) : ℕ :=
  RectangularDirectPreparationRun.tests P (RectangularDirectSolver.report solver a P hP)
    (RectangularDirectPreparationRun.budget P) O

/-- The actual cleanup/cap-test rounds have a literal polynomial bound. -/
theorem rounds_le (solver : RectangularDirectSolver.Service) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) :
    rounds solver a P hP O≤2^320*(d+N+2)^63+1 :=
  RectangularDirectPreparationRun.tests_le_fuel P _ _ O

theorem rounds_eq_paid_add_one (solver : RectangularDirectSolver.Service) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N)
    {y : Owner N × ℕ} (ho : prepare solver a P hP O=some y) :
    rounds solver a P hP O=y.2+1 :=
  RectangularDirectPreparationRun.tests_of_run_some P _ _ ho

def prepareMatrix (solver : RectangularDirectSolver.Service) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (C : Matrix (Fin N) (Fin N) ℝ) :=
  prepare solver a P hP (RectangularDirectPreparationRun.initial C)

theorem prepareMatrix_isSome (solver : RectangularDirectSolver.Service) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (C : Matrix (Fin N) (Fin N) ℝ)
    (hfloor : floor • (1 : Matrix (Fin N) (Fin N) ℝ)≤C) (hC1 : C≤1) :
    (prepareMatrix solver a P hP C).isSome=true :=
  RectangularDirectPreparationRun.prepareMatrix_isSome P hP _ C hfloor hC1

theorem prepareIdentity_isSome (solver : RectangularDirectSolver.Service) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) :
    (prepareMatrix solver a P hP (1 : Matrix (Fin N) (Fin N) ℝ)).isSome=true :=
  RectangularDirectPreparationRun.prepareIdentity_isSome P hP _

end MatrixSpencer.RectangularDirectPreparation
