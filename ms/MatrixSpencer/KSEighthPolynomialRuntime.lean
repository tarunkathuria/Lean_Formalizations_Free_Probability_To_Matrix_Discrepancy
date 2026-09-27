import MatrixSpencer.KSEighthCompiledRun
import MatrixSpencer.KSCountedRetry
import MatrixSpencer.RealRAMKSHorizonSetup
import MatrixSpencer.RealRAMKSLoopCapSetup

/-!
# Polynomial real-RAM execution of the eighth-cube convex-solver algorithm

The only abstract routine is the explicitly permitted polynomial convex
solver. Original-input preprocessing, polynomial cap formation, the actual
horizon ceiling, endpoint preparation, finite Hessian queries, Jacobi and
capped-simplex covariance, guarded LDL sampling, acceptance and sequential
retries are included. The execution produces the literal existing output;
therefore its already proved soundness and success probability are retained.
-/
open Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthPolynomialRuntime
open RealRAM RealRAM.JacobiIteration KSEighthManuscriptPreprocess
variable {N d : ℕ}
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
attribute [local instance] Classical.propDecidable

def setup (v : Fin N → Fin d → ℂ) (hd : 0<d) : Counted ((Fin 14 → ℝ) × ℕ) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let c := KSLoopCapSetup.compute N d
  let h := KSHorizonSetup.compute v 13 100 (c.value 4)
  exact ⟨h.value,c.cost+h.cost+3⟩

theorem setup_value (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    (setup v hd).value=(KSParameterSetup.originalOutputs v (epsilon v),
      KSEighthManuscriptBudgets.cutoff v (Real.sqrt (epsilon v)) (ksRegularizerScale (epsilon v) (Fin d))) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  simpa only [setup,KSLoopCapSetup.compute_value,KSLoopCapSetup.originalOutputs,
    Matrix.cons_val_four,Matrix.cons_val_zero] using KSHorizonSetup.eighth_value v hd hp

def setupBudget (N d : ℕ) : ℕ :=
  100000+10000400*(N+1)*(d+1)+8*KSConvexQueryBudgets.eighthHorizon N d+33

theorem setup_cost (v : Fin N → Fin d → ℂ) (hd : 0<d) :
    (setup v hd).cost≤setupBudget N d := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hc := KSLoopCapSetup.compute_cost N d
  have hh := KSHorizonSetup.compute_cost v 13 100 ((KSLoopCapSetup.compute N d).value 4)
  have hcap : (KSLoopCapSetup.compute N d).value 4=KSConvexQueryBudgets.eighthHorizon N d := by
    rw [KSLoopCapSetup.compute_value]
    rfl
  rw [hcap] at hh
  dsimp only [setup,setupBudget]
  rw [hcap]
  omega

def tree (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) :=
  KSEighthManuscriptRun.run (KSEighthConvexRuntime.controller P.solver v hd hp)
    (KSEighthManuscriptBudgets.cutoff v (Real.sqrt (epsilon v)) (ksRegularizerScale (epsilon v) (Fin d)))
    (KSEighthManuscriptRun.initialState (KSEighthConvexRuntime.controller P.solver v hd hp))

def TrialExec (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) (l : (tree P v hd hp).Leaves)
    (cost draws : ℕ) : Prop :=
  ∃k,KSOnlinePathRuntime.Executes (KSEighthCompiledRun.evaluator P v hd hp) (setup v hd).value.2
    (KSEighthCompiledRun.initial P v hd hp).value ((tree P v hd hp).leafState l) k draws ∧
      cost=(KSEighthCompiledRun.initial P v hd hp).cost+k+2

def walkBudget (P : KSPolynomialConvexSolver.PolynomialSolver) (N d : ℕ) : ℕ :=
  KSEighthCompiledRun.initialBudget P N d+
    KSEighthConvexRuntime.pathBudget N d (KSEighthCompiledQueries.queryCost P N d)
      (KSConvexQueryBudgets.eighthHorizon N d)+2

theorem trial_exists (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) (l : (tree P v hd hp).Leaves) :
    ∃k draws,TrialExec P v hd hp l k draws := by
  obtain ⟨k,r,he,hk,hr⟩ := KSEighthCompiledRun.leaf_execution P v hd hp _ l
  refine ⟨_,r,k,?_,rfl⟩
  simpa only [setup_value v hd hp] using he

theorem trial_budget (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) (l : (tree P v hd hp).Leaves)
    (cost draws : ℕ) (he : TrialExec P v hd hp l cost draws) :
    cost≤walkBudget P N d ∧ draws≤KSConvexQueryBudgets.eighthHorizon N d := by
  obtain ⟨k,he,rfl⟩ := he
  have ht := KSConvexQueryBudgets.eighth_horizon v hd hp
  have hi := KSEighthCompiledRun.initial_cost P v hd hp
  have hb := KSOnlinePathRuntime.execution_budget (KSEighthCompiledRun.evaluator P v hd hp)
    (KSEighthCountedRun.test_cost (KSEighthConvexRuntime.controller P.solver v hd hp))
    (fun s hs i=>(KSEighthCountedRun.childCertificate (KSEighthConvexRuntime.controller P.solver v hd hp)
      (KSEighthCompiledRun.operations P v hd hp)
      (fun x _=>KSEighthCompiledQueries.actual_state_cost P v hd hp x)
      (KSEighthCompiledRun.face_cost P v hd hp) s i).property.2 hs) he
  rw [setup_value v hd hp] at hb
  have hk : k≤KSEighthConvexRuntime.pathBudget N d (KSEighthCompiledQueries.queryCost P N d)
      (KSConvexQueryBudgets.eighthHorizon N d) := by
    apply hb.1.trans
    unfold KSEighthConvexRuntime.pathBudget
    gcongr
  exact ⟨by unfold walkBudget;omega,hb.2.trans ht⟩

def accept (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) :=
  KSEighthCompiledRun.acceptance P.solver v (Real.sqrt (epsilon v))
    (ksRegularizerScale (epsilon v) (Fin d)) hd
    (KSEighthCompiledQueries.queries P v (ksRegularizerScale (epsilon v) (Fin d)) hd)
    (KSEighthConvexRuntime.controller P.solver v hd hp)

def signing (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1)
    (s : KSEighthManuscriptRun.State (KSEighthConvexRuntime.controller P.solver v hd hp)) :
    Counted (Fin N → ℝ) := ⟨fun i=>8*s.coeff i,5*N+1⟩

theorem accept_cost (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1)
    (s : KSEighthManuscriptRun.State (KSEighthConvexRuntime.controller P.solver v hd hp)) :
    (accept P v hd hp s).cost≤KSEighthCompiledQueries.queryCost P N d+23*N+15 := by
  have ht := KSEighthCountedRun.test_cost (KSEighthConvexRuntime.controller P.solver v hd hp) s
  have hq := KSEighthCompiledQueries.actual_acceptance_cost P v hd hp s.coeff
  dsimp only [accept,KSEighthCompiledRun.acceptance]
  omega

theorem retry_output (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) (r : ℕ)
    (z : KSEighthConvexExplicit.PositiveDraws P.solver v hd hp r) :
    KSEighthManuscriptRetry.firstAccepted
      (fun l : (tree P v hd hp).Leaves=>(signing P v hd hp ((tree P v hd hp).leafState l)).value)
      (fun l=>(accept P v hd hp ((tree P v hd hp).leafState l)).value) r z=
      KSEighthConvexExplicit.positiveOutput P.solver v hd hp r z := by
  simp only [accept,KSEighthCompiledRun.acceptance_value,signing,
    KSEighthConvexExplicit.positiveOutput,KSEighthConvexAlgorithm.output,
    KSEighthConvexAlgorithm.leafSigning,KSEighthConvexAlgorithm.leafAccepts]
  rfl

def PositiveExec (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) (r : ℕ)
    (z : KSEighthConvexExplicit.PositiveDraws P.solver v hd hp r)
    (result : Option (Fin N → ℝ)) (cost draws : ℕ) : Prop :=
  ∃k,KSCountedRetry.Executes (TrialExec P v hd hp) (tree P v hd hp).leafState
    (accept P v hd hp) (signing P v hd hp) r z result k draws ∧ cost=(setup v hd).cost+k+2

def totalBudget (P : KSPolynomialConvexSolver.PolynomialSolver) (N d r : ℕ) : ℕ :=
  setupBudget N d+r*(walkBudget P N d+(KSEighthCompiledQueries.queryCost P N d+23*N+15)+(5*N+1)+3)+3

theorem execution_result (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) (r : ℕ)
    (z : KSEighthConvexExplicit.PositiveDraws P.solver v hd hp r)
    (result : Option (Fin N → ℝ)) (cost draws : ℕ)
    (he : PositiveExec P v hd hp r z result cost draws) :
    result=KSEighthConvexExplicit.positiveOutput P.solver v hd hp r z := by
  obtain ⟨k,he,hcost⟩ := he
  exact (KSCountedRetry.executes_result he).trans (retry_output P v hd hp r z)

theorem total_execution (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) (r : ℕ)
    (z : KSEighthConvexExplicit.PositiveDraws P.solver v hd hp r) :
    ∃cost draws,PositiveExec P v hd hp r z
      (KSEighthConvexExplicit.positiveOutput P.solver v hd hp r z) cost draws ∧
      cost≤totalBudget P N d r ∧ draws≤r*KSConvexQueryBudgets.eighthHorizon N d := by
  obtain ⟨k,draws,he,hk,hr⟩ := KSCountedRetry.exists_execution_bounded
    (TrialExec P v hd hp) (tree P v hd hp).leafState (accept P v hd hp) (signing P v hd hp)
    (trial_exists P v hd hp) (trial_budget P v hd hp) (fun l=>accept_cost P v hd hp _)
    (fun _=>show 5*N+1≤5*N+1 from le_rfl) r z
  rw [retry_output] at he
  have hs := setup_cost v hd
  refine ⟨(setup v hd).cost+k+2,draws,⟨k,he,rfl⟩,?_,hr⟩
  unfold totalBudget
  omega

end MatrixSpencer.KSEighthPolynomialRuntime
