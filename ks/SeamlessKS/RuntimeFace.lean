import SeamlessKS.RuntimeQueries
import SeamlessKS.Walk
import SeamlessKS.RuntimeLiveCoordinates

/-! Actual counted live-face queries, including finite label enumeration
and coordinate extension before materializing the SDP. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace SeamlessKS.RuntimeFace
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open MatrixSpencer.KSPolynomialConvexSolver
open SeamlessKS.Walk SeamlessKS.Parameters
open MatrixSpencer.KSLiveEnumeration (count)
variable {N d : ℕ} [Nonempty (Fin d)]

def report (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (s : WalkState N)
    (z : EuclideanSpace ℝ (Fin (count s.coeff))) : Counted ℝ :=
  let y := RuntimeLiveCoordinates.face s.coeff z
  let r := RuntimeQueries.report P v y.value (zeta N) (Input.theta v) (hessianAccuracy v)
  ⟨r.value,y.cost+r.cost+2⟩

theorem report_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (s : WalkState N)
    (z : EuclideanSpace ℝ (Fin (count s.coeff))) :
    (report P v s z).value=Walk.faceReport P.solver v s z := by
  simp only [report,RuntimeLiveCoordinates.face_value,RuntimeQueries.report_value]
  rfl

def reportBound (P : PolynomialSolver) (N d : ℕ) : ℕ :=
  RuntimeLiveCoordinates.faceBound N+RuntimeQueries.queryBound P N d (RuntimeBudgets.hessianAccuracyInverseCap N d)+2

theorem report_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N)
    (z : EuclideanSpace ℝ (Fin (count s.coeff))) : (report P v s z).cost≤reportBound P N d := by
  have hy := RuntimeLiveCoordinates.face_cost s.coeff z
  have hr := RuntimeQueries.hessian_report_cost P v hd hp
    (RuntimeLiveCoordinates.face s.coeff z).value
  dsimp only [report,reportBound]
  omega

end SeamlessKS.RuntimeFace
