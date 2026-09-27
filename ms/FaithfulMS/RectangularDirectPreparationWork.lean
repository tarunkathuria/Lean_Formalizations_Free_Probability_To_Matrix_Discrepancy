import FaithfulMS.RectangularDirectCountedPreparationRun
import FaithfulMS.RectangularDirectPrograms
import MatrixSpencer.MSManuscriptPolynomialQueryCleanup
import MatrixSpencer.RectangularRidgePreparationScalars

/-! Counted finite preparation. Each response comes from the direct-density
implementation; exact EVD selects its dangerous direction, and the existing
finite Jacobi cleanup repairs the stored frame. The local response budget is
an intermediate implementation obligation discharged in the final endpoint. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularDirectPreparationWork
open RealRAM.JacobiIteration (Counted)
open RectangularRidgePreparationData MSManuscriptSupportedOwner
open RectangularDirectCountedPreparationRun
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgePreparationWorkCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 900000
set_option maxRecDepth 10000

def evaluator (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) :
    Evaluator P (RectangularDirectSolver.report S.service a P hP) where
  response := W.response a P hP
  response_value O hO := W.response_value a P hP O hO

theorem bounds (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) :
    Bounds P (RectangularDirectSolver.report S.service a P hP) (evaluator S W a P hP)
      (MSManuscriptPolynomialQueryCleanup.cleanupJacobi N)
      0
      (W.responseBudget N d) := by
  constructor
  · intro O hO
    exact MSManuscriptPolynomialQueryCleanup.ceiling_input_le O hO.2.2 hO.1 hO.2.1
  · intro O hO
    exact W.response_cost a P hP O hO

/-- A literal fixed-degree polynomial in the input dimensions, composed with
the fixed polynomial supplied by the permitted convex solver. -/
def budget (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (N d : ℕ) : ℕ :=
  10000+(2^320*(d+N+2)^63+1)*roundBudget N
    (MSManuscriptPolynomialQueryCleanup.cleanupJacobi N)
    0
    (W.responseBudget N d)+7

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

def prepare (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) : Counted (Option (Owner N×ℕ)) :=
  setupThen (RectangularRidgePreparationScalars.compute N d) (fun t =>
    RectangularDirectCountedPreparationRun.run P
      (RectangularDirectSolver.report S.service a P hP) (evaluator S W a P hP)
      t.cleanup 0 t.paid (if 0<t.paid then t.fuel else 0) O)

attribute [local irreducible] RectangularDirectCountedPreparationRun.run
  RectangularDirectPreparationRun.run RectangularRidgePreparationScalars.compute

private theorem guarded_run_correct (P : Parameters N d) (hP : P.Valid)
    (R : Report P) (E : Evaluator P R) (C J B : ℕ) (hB : Bounds P R E C J B)
    (α : ℝ) (hα : α=paidSize P) (fuel : ℕ) (O : Owner N) (hO : State O) :
    (run P R E C J α (if 0<α then fuel else 0) O).value=
      RectangularDirectPreparationRun.run P R fuel O ∧
    (run P R E C J α (if 0<α then fuel else 0) O).cost≤fuel*roundBudget N C J B+1 := by
  have ha : 0<α := hα.symm ▸ paidSize_pos P
  rw [if_pos ha]
  exact run_correct P hP R E C J B hB α hα fuel O hO

/-- The executed program has exactly the direct preparation's output,
and every work bound is discharged from the original state invariants. -/
theorem prepare_correct (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    (prepare S W a P hP O).value=RectangularDirectPreparation.prepare S.service a P hP O ∧
      (prepare S W a P hP O).cost≤budget S W N d := by
  have hh:=guarded_run_correct P hP (RectangularDirectSolver.report S.service a P hP)
    (evaluator S W a P hP) _ _ _ (bounds S W a P hP) (paidSize P) rfl
    (RectangularDirectPreparationRun.budget P) O hO
  constructor
  · exact (setupThen_value _ _ _ (RectangularRidgePreparationScalars.compute_value N d)).trans hh.1
  · exact setupThen_cost _ _ _ (RectangularRidgePreparationScalars.compute_value N d)
      (RectangularRidgePreparationScalars.compute_cost N d) hh.2

theorem prepare_isSome (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    (prepare S W a P hP O).value.isSome=true := by
  rw [(prepare_correct S W a P hP O hO).1]
  exact RectangularDirectPreparation.prepare_isSome S.service a P hP O hO

theorem prepare_sound (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O)
    {y : Owner N×ℕ} (hy : (prepare S W a P hP O).value=some y) :
    RectangularDirectPreparationRun.Certificate P O (RectangularDirectPreparationRun.budget P) y := by
  rw [(prepare_correct S W a P hP O hO).1] at hy
  exact RectangularDirectPreparation.prepare_sound S.service a P hP O hO hy

end MatrixSpencer.RectangularDirectPreparationWork
