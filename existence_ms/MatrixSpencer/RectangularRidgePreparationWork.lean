import MatrixSpencer.RectangularRidgeCountedPreparationRun
import MatrixSpencer.RectangularRidgeCountedResponse
import MatrixSpencer.RectangularRidgePreparationScalars

/-! Complete polynomial real-RAM accounting for the concrete finite paid
preparation. The only external algorithm contract is the permitted polynomial
solver for its actual finite affine SDP. Every response, Jacobi cutoff,
cleanup, paid cut, and loop length is instantiated from original inputs. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgePreparationWork
open RealRAM.JacobiIteration (Counted)
open RectangularRidgePreparationData MSManuscriptSupportedOwner
open RectangularRidgeCountedPreparationRun
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgePreparationWorkCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 900000
set_option maxRecDepth 10000

def evaluator (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) :
    Evaluator P (RectangularRidgeSolverPreparation.report S.solver a P hP) where
  response := RectangularRidgeCountedResponse.response S a P hP
  response_value O _ := RectangularRidgeCountedResponse.response_value S a P hP O

theorem bounds (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) :
    Bounds P (RectangularRidgeSolverPreparation.report S.solver a P hP) (evaluator S a P hP)
      (MSManuscriptPolynomialQueryCleanup.cleanupJacobi N)
      (RectangularRidgeResponseMagnitude.topBudget N d)
      (RectangularRidgeCountedResponse.responseBudget S N d) := by
  constructor
  · intro O hO
    exact MSManuscriptPolynomialQueryCleanup.ceiling_input_le O hO.2.2 hO.1 hO.2.1
  · intro O hO
    change KSJacobiIteration.denominator O.dim*KSJacobiStep.offDiagonalEnergy
      (-(RectangularRidgeCountedResponse.response S a P hP O).value)/(P.threshold/64)^2≤_
    rw [RectangularRidgeCountedResponse.response_value]
    exact RectangularRidgeResponseMagnitude.top_ceiling_input_le S.solver a P hP O hO
  · intro O hO
    exact RectangularRidgeCountedResponse.response_cost S a P hP O hO

/-- A literal fixed-degree polynomial in the input dimensions, composed with
the fixed polynomial supplied by the permitted convex solver. -/
def budget (S : RectangularRidgeConvexValue.PolynomialSolver) (N d : ℕ) : ℕ :=
  10000+(2^320*(d+N+2)^63+1)*roundBudget N
    (MSManuscriptPolynomialQueryCleanup.cleanupJacobi N)
    (RectangularRidgeResponseMagnitude.topBudget N d)
    (RectangularRidgeCountedResponse.responseBudget S N d)+7

private def setupThen {α β : Type*} (t : Counted α) (f : α → Counted β) : Counted β :=
  ⟨(f t.value).value,t.cost+(f t.value).cost+6⟩

private theorem setupThen_value {α β : Type*} (t : Counted α) (f : α → Counted β)
    (v : α) (hv : t.value=v) : (setupThen t f).value=(f v).value := by
  simp only [setupThen,hv]

private theorem setupThen_cost {α β : Type*} (t : Counted α) (f : α → Counted β)
    (v : α) (hv : t.value=v) {B : ℕ} (ht : t.cost≤10000) (hf : (f v).cost≤B+1) :
    (setupThen t f).cost≤10000+B+7 := by
  simp only [setupThen,hv]
  omega

def prepare (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) : Counted (Option (Owner N×ℕ)) :=
  setupThen (RectangularRidgePreparationScalars.compute N d) (fun t =>
    RectangularRidgeCountedPreparationRun.run P
      (RectangularRidgeSolverPreparation.report S.solver a P hP) (evaluator S a P hP)
      t.cleanup t.top t.paid (if 0<t.paid then t.fuel else 0) O)

attribute [local irreducible] RectangularRidgeCountedPreparationRun.run
  RectangularRidgePreparationRun.run RectangularRidgePreparationScalars.compute

private theorem guarded_run_correct (P : Parameters N d) (hP : P.Valid)
    (R : Report P) (E : Evaluator P R) (C J B : ℕ) (hB : Bounds P R E C J B)
    (α : ℝ) (hα : α=paidSize P) (fuel : ℕ) (O : Owner N) (hO : State O) :
    (run P R E C J α (if 0<α then fuel else 0) O).value=
      RectangularRidgePreparationRun.run P R fuel O ∧
    (run P R E C J α (if 0<α then fuel else 0) O).cost≤fuel*roundBudget N C J B+1 := by
  have ha : 0<α := hα.symm ▸ paidSize_pos P
  rw [if_pos ha]
  exact run_correct P hP R E C J B hB α hα fuel O hO

/-- The executed program has exactly the original preparation's output,
and every work bound is discharged from the original state invariants. -/
theorem prepare_correct (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    (prepare S a P hP O).value=RectangularRidgePreparation.prepare S.solver a P hP O ∧
      (prepare S a P hP O).cost≤budget S N d := by
  have hh:=guarded_run_correct P hP (RectangularRidgeSolverPreparation.report S.solver a P hP)
    (evaluator S a P hP) _ _ _ (bounds S a P hP) (paidSize P) rfl
    (RectangularRidgePreparationRun.budget P) O hO
  constructor
  · exact (setupThen_value _ _ _ (RectangularRidgePreparationScalars.compute_value N d)).trans hh.1
  · exact setupThen_cost _ _ _ (RectangularRidgePreparationScalars.compute_value N d)
      (RectangularRidgePreparationScalars.compute_cost N d) hh.2

theorem prepare_isSome (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    (prepare S a P hP O).value.isSome=true := by
  rw [(prepare_correct S a P hP O hO).1]
  exact RectangularRidgePreparation.prepare_isSome S.solver a P hP O hO

theorem prepare_sound (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O)
    {y : Owner N×ℕ} (hy : (prepare S a P hP O).value=some y) :
    RectangularRidgePreparationRun.Certificate P O (RectangularRidgePreparationRun.budget P) y := by
  rw [(prepare_correct S a P hP O hO).1] at hy
  exact RectangularRidgePreparation.prepare_sound S.solver a P hP O hO hy

end MatrixSpencer.RectangularRidgePreparationWork
