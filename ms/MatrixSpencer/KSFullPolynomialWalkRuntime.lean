import MatrixSpencer.KSFullPolynomialOracleReport
import MatrixSpencer.RealRAMKSNormReport

/-! Original-input polynomial runtime for one full-cube convex-solver trial.
Initialization, every chosen online successor, and the final numerical
acceptance test are implemented. Scalar parameter/horizon construction and
retry orchestration are separate shared components. -/
open Matrix Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSFullPolynomialWalkRuntime
open RealRAM.JacobiIteration (Counted)
open KSPolynomialConvexSolver KSFullManuscriptParameters
open KSEighthManuscriptPreprocess KSManuscriptInputPolynomialParameters
open KSJacobiPolynomialBounds KSConvexQueryBudgets
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
variable {N d : ℕ} [Nonempty (Fin d)]

def valueEvaluator (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d) :=
  KSFullPolynomialOracleReport.evaluator P v (Real.sqrt (epsilon v))
    (debitTolerance N (Real.sqrt (epsilon v))) (ksRegularizerScale (epsilon v) (Fin d)) hd

abbrev controller (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :=
  KSFullConvexOracleAlgorithm.controller P.solver v (labels_pos v hd hp) (epsilon_pos v hd hp) hd

def evaluator (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    KSOnlinePathRuntime.Evaluator KSDebitWalkRun.terminal
      (KSFiniteCoinRun.coinTransition (KSDebitWalkRun.step (controller P v hd hp))) :=
  KSFullConvexRuntime.evaluator (valueEvaluator P v hd) (labels_pos v hd hp)
    (Real.sqrt_pos.mpr (epsilon_pos v hd hp))
    (debitTolerance_pos (labels_pos v hd hp) (Real.sqrt_pos.mpr (epsilon_pos v hd hp)))
    (ksRegularizerScale_pos (n := Fin d) (epsilon_pos v hd hp))
    (KSFullConvexOracleAlgorithm.taylorBudget_pos v (labels_pos v hd hp) (epsilon_pos v hd hp))
    (fullJacobi N d) (KSFullConvexRuntime.actual_cap P.solver v hd hp (valueEvaluator P v hd))

def initial (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) : Counted (KSDebitWalkRun.State (controller P v hd hp)) :=
  KSFullConvexRuntime.prepare (valueEvaluator P v hd) (labels_pos v hd hp)
    (Real.sqrt_pos.mpr (epsilon_pos v hd hp))
    (debitTolerance_pos (labels_pos v hd hp) (Real.sqrt_pos.mpr (epsilon_pos v hd hp)))
    (ksRegularizerScale_pos (n := Fin d) (epsilon_pos v hd hp))
    (KSFullConvexOracleAlgorithm.taylorBudget_pos v (labels_pos v hd hp) (epsilon_pos v hd hp))
    0 (ksCube_zero (by norm_num))

theorem initial_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    (initial P v hd hp).value=KSDebitWalkRun.initialState (controller P v hd hp) := by
  exact KSFullConvexRuntime.prepare_value _ _ _ _ _ _ _ _

def initialCost (P : PolynomialSolver) (N d : ℕ) : ℕ :=
  6*(N+1)^3*(KSFullPolynomialOracleReport.queryCost P N d+20)+2

def stepCost (P : PolynomialSolver) (N d : ℕ) : ℕ :=
  2000*(N+1)^4*(KSFullPolynomialOracleReport.queryCost P N d+fullJacobi N d+20)

def walkCost (P : PolynomialSolver) (N d : ℕ) : ℕ :=
  fullHorizon N d*((15*N+2)+stepCost P N d+3)+(15*N+2)+2

theorem initial_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) : (initial P v hd hp).cost ≤ initialCost P N d := by
  exact KSFullConvexRuntime.prepare_cost _ _ _ _ _ _
    (fun x _ => KSFullPolynomialOracleReport.state_cost P v hd hp x) _ _

theorem evaluator_test_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (s : KSDebitWalkRun.State (controller P v hd hp)) :
    ((evaluator P v hd hp).test s).cost≤15*N+2 := (KSFullConvexRuntime.terminalTest_cost s.coeff).le

theorem evaluator_child_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (s : KSDebitWalkRun.State (controller P v hd hp))
    (i : Fin 2) : ((evaluator P v hd hp).child s i).cost≤stepCost P N d := by
  exact KSFullConvexRuntime.step_cost (valueEvaluator P v hd) (labels_pos v hd hp)
    (Real.sqrt_pos.mpr (epsilon_pos v hd hp))
    (debitTolerance_pos (labels_pos v hd hp) (Real.sqrt_pos.mpr (epsilon_pos v hd hp)))
    (ksRegularizerScale_pos (n := Fin d) (epsilon_pos v hd hp))
    (KSFullConvexOracleAlgorithm.taylorBudget_pos v (labels_pos v hd hp) (epsilon_pos v hd hp))
    (fullJacobi N d) (KSFullConvexRuntime.actual_cap P.solver v hd hp (valueEvaluator P v hd))
    (fun x _ => KSFullPolynomialOracleReport.state_cost P v hd hp x)
    (fun x _ => KSFullPolynomialOracleReport.hessian_cost P v hd hp x) s (decide (i.val=0))

/-- Every original leaf is obtained by executing just its selected coin path.
Both primitive work and random draws have input-polynomial bounds. -/
theorem leaf_execution_bounded (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1)
    (l : (KSFullConvexOracleAlgorithm.attempt P.solver v (labels_pos v hd hp) (epsilon_pos v hd hp) hd).Leaves) :
    ∃ k r, KSOnlinePathRuntime.Executes (evaluator P v hd hp)
      (KSFullConvexOracleAlgorithm.horizon v (epsilon v))
      (KSDebitWalkRun.initialState (controller P v hd hp))
      ((KSFullConvexOracleAlgorithm.attempt P.solver v (labels_pos v hd hp) (epsilon_pos v hd hp) hd).leafState l) k r ∧
      k≤walkCost P N d ∧ r≤fullHorizon N d := by
  obtain ⟨k,r,he,hk,hr⟩ := KSOnlinePathRuntime.coin_leaf_execution_bounded (evaluator P v hd hp)
    (evaluator_test_cost P v hd hp) (fun s _ i => evaluator_child_cost P v hd hp s i)
    (KSFullConvexOracleAlgorithm.horizon v (epsilon v))
    (KSDebitWalkRun.initialState (controller P v hd hp)) l
  have hT : KSFullConvexOracleAlgorithm.horizon v (epsilon v)≤fullHorizon N d := full_horizon v hd hp
  refine ⟨k,r,he,hk.trans ?_,hr.trans hT⟩
  unfold walkCost
  gcongr

/-- Final norm report and signing check, including formation of the matrix. -/
def accepts (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (s : KSDebitWalkRun.State (controller P v hd hp)) : Counted Bool :=
  RealRAM.KSNormReport.acceptance s.coeff (RealRAM.KSFullStateData.signedCenter v s.coeff)
    (Real.sqrt (epsilon v)) (RealRAM.KSNormReport.normCap N d)

theorem accepts_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (s : KSDebitWalkRun.State (controller P v hd hp)) :
    (accepts P v hd hp s).value=KSFullManuscriptAcceptance.accepts (controller P v hd hp) s := by
  have hc : KSJacobiIteration.denominator (d+d)*KSJacobiStep.offDiagonalEnergy
      (KSComplexTraceSqrt.realificationFin (RealRAM.KSFullStateData.signedCenter v s.coeff).value)/
      (Real.sqrt (epsilon v)/4)^2≤(RealRAM.KSNormReport.normCap N d:ℝ) := by
    rw [RealRAM.KSFullStateData.signedCenter_value]
    exact RealRAM.KSNormReport.norm_cap v hd hp s.coeff (fun i => abs_le.mpr ⟨s.cube.1 i,s.cube.2 i⟩)
  rw [accepts,RealRAM.KSNormReport.acceptance_value _ _ _ _ hc,RealRAM.KSFullStateData.signedCenter_value]
  rfl

def acceptanceCost (N d : ℕ) : ℕ :=
  100*(N+1)*(d+1)^2+700*(RealRAM.KSNormReport.normCap N d+1)*(d+d+1)^3+12*N+20

theorem accepts_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (s : KSDebitWalkRun.State (controller P v hd hp)) :
    (accepts P v hd hp s).cost≤acceptanceCost N d := by
  apply (RealRAM.KSNormReport.acceptance_cost s.coeff
    (RealRAM.KSFullStateData.signedCenter v s.coeff) (Real.sqrt (epsilon v)) _).trans
  unfold acceptanceCost
  gcongr
  exact RealRAM.KSFullStateData.signedCenter_cost v s.coeff

end MatrixSpencer.KSFullPolynomialWalkRuntime
