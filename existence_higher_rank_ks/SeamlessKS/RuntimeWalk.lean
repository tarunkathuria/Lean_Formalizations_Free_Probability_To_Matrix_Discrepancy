import SeamlessKS.RuntimeGeometry
import SeamlessKS.RuntimeSelection
import SeamlessKS.RuntimeFace
import SeamlessKS.RuntimeAcceptance
import MatrixSpencer.KSOnlinePathRuntime

/-! A counted evaluator for the actual local walk. The queried label and
exact-EVD direction are computed here; proof fields certify the resulting arrays
and are not computational inputs. -/
open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.RuntimeWalk
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open MatrixSpencer.KSPolynomialConvexSolver
open SeamlessKS.State SeamlessKS.Parameters SeamlessKS.Walk
open MatrixSpencer.KSLiveEnumeration (count)
attribute [local instance] Classical.propDecidable
variable {N d : ℕ} [Nonempty (Fin d)]

def liveOutput (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (s : WalkState N) (hs : ¬Walk.terminal s) :
    Counted (EuclideanSpace ℝ (Fin (count s.coeff))) :=
  let w := RuntimeGeometry.weights s
  let q := RuntimeDirection.compute (RuntimeFace.report P v s) w.value (queryStep v) (liveCount_pos s hs)
  ⟨q.value,w.cost+q.cost+2⟩

theorem liveOutput_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N) (hs : ¬Walk.terminal s) :
    (liveOutput P v s hs).value=Walk.liveOutput P.solver v s hs := by
  simp only [liveOutput,RuntimeGeometry.weights_value]
  exact RuntimeDirection.actual_value P.solver v hd hp s hs (RuntimeFace.report P v s)
    (RuntimeFace.report_value P v s)

def liveOutputBound (P : PolynomialSolver) (N d : ℕ) : ℕ :=
  50*(N+1)^2+N^2*(4*RuntimeFace.reportBound P N d+100*(N+1)+18)+
    600*(N+1)^3+7

theorem liveOutput_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N) (hs : ¬Walk.terminal s) :
    (liveOutput P v s hs).cost≤liveOutputBound P N d := by
  have hw := RuntimeGeometry.weights_cost s
  have hq := RuntimeDirection.compute_cost (RuntimeFace.report P v s) (RuntimeGeometry.weights s).value
    (queryStep v) (liveCount_pos s hs)
    (fun z _ => RuntimeFace.report_cost P v hd hp s z)
  have hm := NumericQueries.liveCount_le s.coeff
  have hq' : (RuntimeDirection.compute (RuntimeFace.report P v s) (RuntimeGeometry.weights s).value
      (queryStep v) (liveCount_pos s hs)).cost≤
      N^2*(4*RuntimeFace.reportBound P N d+100*(N+1)+18)+
        600*(N+1)^3+5 := hq.trans (by gcongr)
  dsimp only [liveOutput,liveOutputBound]
  omega

def direction (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (s : WalkState N) (hs : ¬Walk.terminal s) : Counted (EuclideanSpace ℝ (Fin N)) :=
  let q := liveOutput P v s hs
  let e := RuntimeLiveCoordinates.extension s.coeff q.value
  ⟨e.value,q.cost+e.cost+1⟩

theorem direction_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N) (hs : ¬Walk.terminal s) :
    (direction P v s hs).value=Walk.direction P.solver v s hs := by
  simp only [direction,RuntimeLiveCoordinates.extension_value,liveOutput_value P v hd hp]
  rfl

def directionBound (P : PolynomialSolver) (N d : ℕ) : ℕ := liveOutputBound P N d+RuntimeLiveCoordinates.extensionBound N+1

theorem direction_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N) (hs : ¬Walk.terminal s) :
    (direction P v s hs).cost≤directionBound P N d := by
  have hq := liveOutput_cost P v hd hp s hs
  have he := RuntimeLiveCoordinates.extension_cost s.coeff (liveOutput P v s hs).value
  dsimp only [direction,directionBound]
  omega

/-- Only the computed coefficient array survives erasure. The canonical
state contributes proofs of cube membership and no computational fields. -/
def certifyMove {ρ : ℝ} (canonical : CubeState N ρ) (x : Fin N → ℝ)
    (hx : x=canonical.coeff) : CubeState N ρ where
  coeff := x
  cube := hx.symm ▸ canonical.cube
  rho_nonneg := canonical.rho_nonneg

theorem certifyMove_value {ρ : ℝ} (canonical : CubeState N ρ) (x : Fin N → ℝ)
    (hx : x=canonical.coeff) : certifyMove canonical x hx=canonical := by
  cases canonical
  simp only [certifyMove,CubeState.mk.injEq]
  exact hx

def rawStep (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (b : Bool) : Counted (CubeState N (rho N)) := by
  let label := RuntimeSelection.chosenLabel P v s
  let canonical := Walk.rawStep P.solver v hd hp s hs b
  exact match hi : label.value with
  | some i =>
    let y := RuntimeSelection.outward s.coeff i (outwardStep N)
    have hlabel : Walk.chosenLabel P.solver v s=some i := by
      rw [←RuntimeSelection.chosenLabel_value P v s]; exact hi
    have he : y.value=canonical.coeff := by
      dsimp only [canonical]
      rw [WalkGeometry.rawStep_some P.solver v hd hp s hs i hlabel b]
      exact RuntimeSelection.outward_value s.coeff i (outwardStep N)
    ⟨certifyMove canonical y.value he,label.cost+y.cost+N+5⟩
  | none =>
    let q := direction P v s hs
    let y := RuntimeGeometry.movement s.coeff q.value (zeta N) (signedStep v b)
    have hlabel : Walk.chosenLabel P.solver v s=none := by
      rw [←RuntimeSelection.chosenLabel_value P v s]; exact hi
    have he : y.value=canonical.coeff := by
      dsimp only [canonical]
      rw [WalkGeometry.rawStep_none P.solver v hd hp s hs hlabel b]
      simp only [y,RuntimeGeometry.movement_value,q,direction_value P v hd hp]
      rfl
    ⟨certifyMove canonical y.value he,label.cost+q.cost+y.cost+N+10⟩

theorem rawStep_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (b : Bool) :
    (rawStep P v hd hp s hs b).value=Walk.rawStep P.solver v hd hp s hs b := by
  unfold rawStep
  dsimp only
  split <;> simp only [certifyMove_value]

def rawStepBound (P : PolynomialSolver) (N d : ℕ) : ℕ :=
  RuntimeSelection.selectionBound P N d (RuntimeBudgets.localAccuracyInverseCap N d)+
    directionBound P N d+45*N+30

theorem rawStep_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (b : Bool) :
    (rawStep P v hd hp s hs b).cost≤rawStepBound P N d := by
  have hl := RuntimeSelection.chosenLabel_cost P v hd hp s
  have hq := direction_cost P v hd hp s hs
  unfold rawStep
  dsimp only
  split
  · rename_i i hi
    have hy := RuntimeSelection.outward_cost s.coeff i (outwardStep N)
    dsimp only
    unfold rawStepBound
    omega
  · have hy := RuntimeGeometry.movement_cost s.coeff (direction P v s hs).value
      (zeta N) (signedStep v b)
    dsimp only
    unfold rawStepBound
    omega

def step (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (b : Bool) : Counted (WalkState N) :=
  if hs : Walk.terminal s then ⟨s,(RuntimeAcceptance.signTest s.coeff).cost+2*N+3⟩ else
    let a := rawStep P v hd hp s hs b
    let q := RuntimeGeometry.prepareCounted (rho_pos (Input.labels_pos v hd hp)).le a.value
    ⟨q.value,(RuntimeAcceptance.signTest s.coeff).cost+a.cost+q.cost+3⟩

theorem step_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N) (b : Bool) :
    (step P v hd hp s b).value=Walk.step P.solver v hd hp s b := by
  by_cases hs : Walk.terminal s
  · simp only [step,Walk.step,dif_pos hs]
  · simp only [step,Walk.step,dif_neg hs,RuntimeGeometry.prepareCounted_value,rawStep_value]

def stepBound (P : PolynomialSolver) (N d : ℕ) : ℕ := rawStepBound P N d+50*N+7

theorem step_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N) (b : Bool) :
    (step P v hd hp s b).cost≤stepBound P N d := by
  by_cases hs : Walk.terminal s
  · simp only [step,dif_pos hs,RuntimeAcceptance.signTest_cost,stepBound]
    omega
  · have ha := rawStep_cost P v hd hp s hs b
    have hq := RuntimeGeometry.prepareCounted_cost (rho_pos (Input.labels_pos v hd hp)).le
      (rawStep P v hd hp s hs b).value
    simp only [step,dif_neg hs,RuntimeAcceptance.signTest_cost,stepBound]
    omega

def evaluator (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) :
    KSOnlinePathRuntime.Evaluator Walk.terminal (KSFiniteCoinRun.coinTransition (Walk.step P.solver v hd hp)) where
  test s := RuntimeAcceptance.signTest s.coeff
  test_correct := RuntimeAcceptance.signTest_value
  child s i := step P v hd hp s (decide (i.val=0))
  child_correct s i := step_value P v hd hp s (decide (i.val=0))

theorem evaluator_test_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N) :
    ((evaluator P v hd hp).test s).cost≤12*N+2 := (RuntimeAcceptance.signTest_cost s.coeff).le

theorem evaluator_child_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N)
    (i : Fin ((KSFiniteCoinRun.coinTransition (Walk.step P.solver v hd hp)) s).arity) :
    ((evaluator P v hd hp).child s i).cost≤stepBound P N d := step_cost P v hd hp s (decide (i.val=0))


def initial (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) : Counted (WalkState N) :=
  RuntimeGeometry.initialCounted v hd hp

omit [Nonempty (Fin d)] in
theorem initial_value (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) : (initial v hd hp).value=Walk.initial v hd hp :=
  RuntimeGeometry.initialCounted_value v hd hp

def initialBound (N : ℕ) : ℕ := 44*N+4

omit [Nonempty (Fin d)] in
theorem initial_cost (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) : (initial v hd hp).cost≤ initialBound N :=
  RuntimeGeometry.initialCounted_cost v hd hp

end SeamlessKS.RuntimeWalk
