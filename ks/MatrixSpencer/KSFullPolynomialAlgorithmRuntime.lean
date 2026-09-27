import MatrixSpencer.KSFullPolynomialWalkRuntime
import MatrixSpencer.KSCountedRetry
import MatrixSpencer.RealRAMKSHorizonSetup
import MatrixSpencer.RealRAMKSLoopCapSetup
import MatrixSpencer.RealRAMOwnerSDPPolynomialCost

/-! Complete positive-dimensional real-RAM execution bound for the named
full-cube KS convex-solver algorithm. The one supplied computational contract
is polynomial solution of the already compiled convex queries. Parameter
construction, natural caps, actual horizon, initialization, online walks,
acceptance, output copying, and sequential retries are all charged here. -/
open Matrix Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSFullPolynomialAlgorithmRuntime
open RealRAM.JacobiIteration (Counted)
open KSPolynomialConvexSolver KSFullPolynomialWalkRuntime
open KSEighthManuscriptPreprocess KSManuscriptInputPolynomialParameters
open KSConvexQueryBudgets
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
variable {N d : ℕ} [Nonempty (Fin d)]

abbrev trial (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :=
  KSFullConvexOracleAlgorithm.attempt P.solver v (labels_pos v hd hp) (epsilon_pos v hd hp) hd

/-- The concrete initialization is followed by just the selected online path,
using the actually computed finite horizon. -/
def TrialExec (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (l : (trial P v hd hp).Leaves) (k draws : ℕ) : Prop :=
  ∃ w, KSOnlinePathRuntime.Executes (evaluator P v hd hp) (RealRAM.KSHorizonSetup.full v).value.2
    (initial P v hd hp).value ((trial P v hd hp).leafState l) w draws ∧
    k=(initial P v hd hp).cost+w+1

def trialCost (P : PolynomialSolver) (N d : ℕ) : ℕ := initialCost P N d+walkCost P N d+1

theorem trial_exists (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (l : (trial P v hd hp).Leaves) :
    ∃ k draws, TrialExec P v hd hp l k draws := by
  obtain ⟨k,r,he,hk,hr⟩ := leaf_execution_bounded P v hd hp l
  refine ⟨(initial P v hd hp).cost+k+1,r,k,?_,rfl⟩
  rw [RealRAM.KSHorizonSetup.full_value v hd hp,initial_value]
  exact he

theorem trial_bound (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (l : (trial P v hd hp).Leaves) (k draws : ℕ)
    (h : TrialExec P v hd hp l k draws) : k≤trialCost P N d ∧ draws≤fullHorizon N d := by
  obtain ⟨w,he,rfl⟩ := h
  obtain ⟨hw,hr⟩ := KSOnlinePathRuntime.execution_budget (evaluator P v hd hp)
    (evaluator_test_cost P v hd hp) (fun s _ i => evaluator_child_cost P v hd hp s i) he
  rw [RealRAM.KSHorizonSetup.full_value v hd hp] at hw hr
  have hT := full_horizon v hd hp
  have hw' : w≤walkCost P N d := hw.trans (by unfold walkCost; dsimp only; gcongr)
  constructor
  · exact Nat.add_le_add_right (Nat.add_le_add (initial_cost P v hd hp) hw') 1
  · exact hr.trans hT

def copyCircuit (N : ℕ) : RealRAM.Circuit (Fin N) (Fin N) where
  output i := .input i

def copy (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (s : KSDebitWalkRun.State (controller P v hd hp)) :
    Counted (Fin N → ℝ) := ⟨(copyCircuit N).eval s.coeff,(copyCircuit N).cost+N+1⟩

theorem copy_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (s : KSDebitWalkRun.State (controller P v hd hp)) :
    (copy P v hd hp s).value=s.coeff := rfl

theorem copy_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (s : KSDebitWalkRun.State (controller P v hd hp)) :
    (copy P v hd hp s).cost=3*N+1 := by
  simp [copy,copyCircuit,RealRAM.Circuit.cost,RealRAM.Expr.cost]
  omega

/-- This is a fixed polynomial in the input dimensions and retry budget;
its fixed solver coefficient and degree come from the permitted solver. -/
def totalCost (P : PolynomialSolver) (N d r : ℕ) : ℕ :=
  100000+10000400*(N+1)*(d+1)+8*fullHorizon N d+30+
    r*(trialCost P N d+acceptanceCost N d+(3*N+1)+3)+3

/-- A total execution includes the counted cap and scalar/horizon setup
exactly once, followed by first-success retry execution. -/
def Executes (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (r : ℕ)
    (z : KSFullConvexOracleAlgorithm.Draws P.solver v (labels_pos v hd hp) (epsilon_pos v hd hp) hd r)
    (result : Option (Fin N → ℝ)) (cost draws : ℕ) : Prop :=
  ∃ k, KSCountedRetry.Executes (TrialExec P v hd hp) (trial P v hd hp).leafState
    (accepts P v hd hp) (copy P v hd hp) r (KSCountedRetry.fullDraws r z) result k draws ∧
    cost=(RealRAM.KSLoopCapSetup.compute N d).cost+(RealRAM.KSHorizonSetup.full v).cost+k+2

/-- Executing the constructed algorithm returns precisely the output whose
validity and probability were already proved for the convex-solver walk. -/
theorem execution_result (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (r : ℕ)
    (z : KSFullConvexOracleAlgorithm.Draws P.solver v (labels_pos v hd hp) (epsilon_pos v hd hp) hd r)
    (result : Option (Fin N → ℝ)) (cost draws : ℕ) (h : Executes P v hd hp r z result cost draws) :
    result=KSFullConvexOracleAlgorithm.output P.solver v (labels_pos v hd hp) (epsilon_pos v hd hp) hd r z := by
  obtain ⟨k,he,hk⟩ := h
  have hh := KSCountedRetry.executes_result he
  simp only [copy_value,accepts_value] at hh
  rw [KSCountedRetry.full_firstAccepted] at hh
  exact hh

/-- Every prospective finite coin draw admits an execution of the actual
algorithm within the displayed polynomial bound, including failed attempts. -/
theorem exists_execution_bounded (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (r : ℕ)
    (z : KSFullConvexOracleAlgorithm.Draws P.solver v (labels_pos v hd hp) (epsilon_pos v hd hp) hd r) :
    ∃ cost draws, Executes P v hd hp r z
      (KSFullConvexOracleAlgorithm.output P.solver v (labels_pos v hd hp) (epsilon_pos v hd hp) hd r z) cost draws ∧
      cost≤totalCost P N d r ∧ draws≤r*fullHorizon N d := by
  obtain ⟨k,draws,he,hk,hr⟩ := KSCountedRetry.exists_execution_bounded (TrialExec P v hd hp)
    (trial P v hd hp).leafState (accepts P v hd hp) (copy P v hd hp)
    (trial_exists P v hd hp) (trial_bound P v hd hp)
    (fun l => accepts_cost P v hd hp ((trial P v hd hp).leafState l))
    (fun l => (copy_cost P v hd hp ((trial P v hd hp).leafState l)).le) r (KSCountedRetry.fullDraws r z)
  have hout : KSEighthManuscriptRetry.firstAccepted
      (fun l => (copy P v hd hp ((trial P v hd hp).leafState l)).value)
      (fun l => (accepts P v hd hp ((trial P v hd hp).leafState l)).value) r (KSCountedRetry.fullDraws r z)=
      KSFullConvexOracleAlgorithm.output P.solver v (labels_pos v hd hp) (epsilon_pos v hd hp) hd r z := by
    simp only [copy_value,accepts_value]
    rw [KSCountedRetry.full_firstAccepted]
    rfl
  rw [hout] at he
  refine ⟨_,draws,⟨k,he,rfl⟩,?_,hr⟩
  have h1 := RealRAM.KSLoopCapSetup.compute_cost N d
  have h2 := RealRAM.KSHorizonSetup.compute_cost v 7 16 (fullHorizon N d)
  change (RealRAM.KSHorizonSetup.full v).cost≤_ at h2
  unfold totalCost
  omega

end MatrixSpencer.KSFullPolynomialAlgorithmRuntime
