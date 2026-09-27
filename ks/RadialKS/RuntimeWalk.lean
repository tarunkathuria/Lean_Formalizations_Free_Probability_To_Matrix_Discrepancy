import RadialKS.RuntimeMotion
import RadialKS.RuntimeDirection
import RadialKS.WalkGeometry
import RadialKS.WalkDrift
import SeamlessKS.RuntimeWalk

/-! Counted execution of the concrete radial step. Scalar array updates,
live-label lookup, both candidate value queries, and the comparison are charged.
The frame is implemented by RuntimeDirection, rather than provided as a primitive. -/
open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace RadialKS.RuntimeWalk
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open MatrixSpencer.KSPolynomialConvexSolver
open SeamlessKS SeamlessKS.State SeamlessKS.Parameters RadialKS.Walk RadialKS.RuntimeMotion
open MatrixSpencer.KSLiveEnumeration (count liveEquiv)
attribute [local instance] Classical.propDecidable
variable {N d : ℕ} [Nonempty (Fin d)]

def liveOutput (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (hn : Walk.chosenLabel P.solver v s=none) :
    Counted (EuclideanSpace ℝ (Fin (count s.coeff))) :=
  let z := positions s
  let q := RadialKS.RuntimeDirection.compute (RuntimeFace.report P v s) z.value (queryStep v)
    (by rw [positions_value]; exact Walk.rank_pos P.solver v hd hp s hs hn)
  ⟨q.value,z.cost+q.cost+2⟩

theorem liveOutput_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (hn : Walk.chosenLabel P.solver v s=none) :
    (liveOutput P v hd hp s hs hn).value=Walk.liveOutput P.solver v hd hp s hs hn := by
  simp only [liveOutput,positions_value,RadialKS.RuntimeDirection.compute_value]
  have he : (fun z => (RuntimeFace.report P v s z).value)=Walk.faceReport P.solver v s :=
    funext (RuntimeFace.report_value P v s)
  rw [he]
  rfl

def liveOutputBound (P : PolynomialSolver) (N d : ℕ) : ℕ :=
  50*(N+1)^2+N^2*(4*RuntimeFace.reportBound P N d+100*(N+1)+18)+
    1000*(N+1)^5+22

theorem liveOutput_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (hn : Walk.chosenLabel P.solver v s=none) :
    (liveOutput P v hd hp s hs hn).cost≤liveOutputBound P N d := by
  have hz := positions_cost s
  have hr : 0 < (Frame.canonical (count s.coeff) (positions s).value).rank := by
    rw [positions_value]
    exact Walk.rank_pos P.solver v hd hp s hs hn
  have hq := RadialKS.RuntimeDirection.compute_cost (RuntimeFace.report P v s) (positions s).value
    (queryStep v) hr (fun z _ => RuntimeFace.report_cost P v hd hp s z)
  have hm := NumericQueries.liveCount_le s.coeff
  have hq' : (RadialKS.RuntimeDirection.compute (RuntimeFace.report P v s) (positions s).value
      (queryStep v) hr).cost≤
      N^2*(4*RuntimeFace.reportBound P N d+100*(N+1)+18)+1000*(N+1)^5+20 :=
    hq.trans (by gcongr)
  dsimp only [liveOutput,liveOutputBound]
  omega

abbrev certifyMove := @SeamlessKS.RuntimeWalk.certifyMove
abbrev certifyMove_value := @SeamlessKS.RuntimeWalk.certifyMove_value

def rawStep (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) : Counted (CubeState N (rho N)) := by
  let label := RuntimeSelection.chosenLabel P v s
  let canonical := Walk.rawStep P.solver v hd hp s hs
  exact match hi : label.value with
  | some i =>
    let y := RuntimeSelection.outward s.coeff i (outwardStep N)
    have hlabel : Walk.chosenLabel P.solver v s=some i := by
      exact (RuntimeSelection.chosenLabel_value P v s).symm.trans hi
    have he : y.value=canonical.coeff := by
      dsimp only [canonical]
      rw [WalkGeometry.rawStep_some P.solver v hd hp s hs i hlabel]
      exact RuntimeSelection.outward_value s.coeff i (outwardStep N)
    ⟨certifyMove canonical y.value he,label.cost+y.cost+N+5⟩
  | none =>
    have hlabel : Walk.chosenLabel P.solver v s=none := by
      exact (RuntimeSelection.chosenLabel_value P v s).symm.trans hi
    let q := liveOutput P v hd hp s hs hlabel
    let y := choice P v s q.value
    have he : y.value=canonical.coeff := by
      dsimp only [canonical]
      rw [WalkGeometry.rawStep_none P.solver v hd hp s hs hlabel]
      simp only [y,q,liveOutput_value P v hd hp,choice_value]
      rfl
    ⟨certifyMove canonical y.value he,label.cost+q.cost+y.cost+N+10⟩

theorem rawStep_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) :
    (rawStep P v hd hp s hs).value=Walk.rawStep P.solver v hd hp s hs := by
  unfold rawStep
  dsimp only
  split <;> simp only [certifyMove_value]

def rawStepBound (P : PolynomialSolver) (N d : ℕ) : ℕ :=
  RuntimeSelection.selectionBound P N d (RuntimeBudgets.localAccuracyInverseCap N d)+
    liveOutputBound P N d+choiceBound P N d+10*N+30

theorem rawStep_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) :
    (rawStep P v hd hp s hs).cost≤rawStepBound P N d := by
  have hl := RuntimeSelection.chosenLabel_cost P v hd hp s
  unfold rawStep
  dsimp only
  split
  · rename_i i hi
    have hy := RuntimeSelection.outward_cost s.coeff i (outwardStep N)
    dsimp only
    unfold rawStepBound
    omega
  · rename_i hi
    have hn : Walk.chosenLabel P.solver v s=none := by
      exact (RuntimeSelection.chosenLabel_value P v s).symm.trans hi
    have hq := liveOutput_cost P v hd hp s hs hn
    have hy := choice_cost P v hd hp s (liveOutput P v hd hp s hs hn).value
    dsimp only
    unfold rawStepBound
    omega

def step (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) : Counted (WalkState N) :=
  if hs : Walk.terminal s then ⟨s,(RuntimeAcceptance.signTest s.coeff).cost+2*N+3⟩ else
    let a := rawStep P v hd hp s hs
    let q := RuntimeGeometry.prepareCounted (rho_pos (Input.labels_pos v hd hp)).le a.value
    ⟨q.value,(RuntimeAcceptance.signTest s.coeff).cost+a.cost+q.cost+3⟩

theorem step_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N) :
    (step P v hd hp s).value=Walk.step P.solver v hd hp s := by
  by_cases hs : Walk.terminal s
  · simp only [step,Walk.step,dif_pos hs]
  · simp only [step,Walk.step,dif_neg hs,RuntimeGeometry.prepareCounted_value,rawStep_value]

def stepBound (P : PolynomialSolver) (N d : ℕ) : ℕ := rawStepBound P N d+50*N+7

theorem step_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N) :
    (step P v hd hp s).cost≤stepBound P N d := by
  by_cases hs : Walk.terminal s
  · simp only [step,dif_pos hs,RuntimeAcceptance.signTest_cost,stepBound]
    omega
  · have ha := rawStep_cost P v hd hp s hs
    have hq := RuntimeGeometry.prepareCounted_cost (rho_pos (Input.labels_pos v hd hp)).le
      (rawStep P v hd hp s hs).value
    simp only [step,dif_neg hs,RuntimeAcceptance.signTest_cost,stepBound]
    omega

abbrev initial := @SeamlessKS.RuntimeWalk.initial
abbrev initial_value := @SeamlessKS.RuntimeWalk.initial_value
abbrev initialBound := SeamlessKS.RuntimeWalk.initialBound
abbrev initial_cost := @SeamlessKS.RuntimeWalk.initial_cost

end RadialKS.RuntimeWalk
