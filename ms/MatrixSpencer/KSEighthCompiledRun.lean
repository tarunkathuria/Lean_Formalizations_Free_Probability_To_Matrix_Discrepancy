import MatrixSpencer.KSEighthCompiledQueries
import MatrixSpencer.KSEighthCountedScalarExecution
import MatrixSpencer.KSEighthQueryParameterExecution

/-! Complete counted eighth trial components from the primitive Parseval
input and the permitted polynomial convex solver: initial preparation, one
sampled adaptive history, endpoint acceptance and original-label signing. -/
open Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthCompiledRun
open RealRAM.JacobiIteration KSEighthManuscriptPreprocess
open KSEighthCountedPreparation KSEighthManuscriptRun
variable {N d : ℕ}
attribute [local instance] Classical.propDecidable

def acceptance (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (δ θ : ℝ) (hd : 0<d) (q : Queries O v θ hd) (C : Controller N) (s : State C) : Counted Bool :=
  let t := KSEighthCountedRun.test C s
  let r := q.state (δ/4) s.coeff
  ⟨t.value && decide (r.value≤63*δ),t.cost+r.cost+10⟩

theorem acceptance_value (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (δ θ : ℝ) (hd : 0<d) (q : Queries O v θ hd) (C : Controller N) (s : State C) :
    (acceptance O v δ θ hd q C s).value=KSEighthConvexAcceptance.accepts O v δ θ hd C s := by
  apply Bool.eq_iff_iff.mpr
  simp only [acceptance,KSEighthCountedRun.test_value,q.state_value,Bool.and_eq_true,
    decide_eq_true_eq,KSEighthConvexAcceptance.accepts_iff]

def output (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (δ θ : ℝ) (hd : 0<d) (q : Queries O v θ hd) (C : Controller N) (s : State C) :
    Counted (Option (Fin N → ℝ)) :=
  let a := acceptance O v δ θ hd q C s
  ⟨if a.value then some (fun i=>8*s.coeff i) else none,a.cost+5*N+3⟩

theorem output_value (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (δ θ : ℝ) (hd : 0<d) (q : Queries O v θ hd) (C : Controller N) (s : State C) :
    (output O v δ θ hd q C s).value=KSEighthConvexAcceptance.output O v δ θ hd C s := by
  simp only [output,acceptance_value,KSEighthConvexAcceptance.output,KSEighthWalkRun.signing]
  rfl

theorem output_cost (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (δ θ : ℝ) (hd : 0<d) (q : Queries O v θ hd) (C : Controller N) (s : State C) {Q : ℕ}
    (hQ : (q.state (δ/4) s.coeff).cost≤Q) :
    (output O v δ θ hd q C s).cost≤Q+28*N+18 := by
  have ht := KSEighthCountedRun.test_cost C s
  dsimp only [output,acceptance]
  omega

def operations (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) :=
  KSEighthConvexRuntime.operations P.solver v hd hp
    (KSEighthCompiledQueries.queries P v (ksRegularizerScale (epsilon v) (Fin d)) hd)

def initial (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) :
    Counted (State (KSEighthConvexRuntime.controller P.solver v hd hp)) :=
  KSEighthCountedRun.makeState (KSEighthConvexRuntime.controller P.solver v hd hp)
    (operations P v hd hp) 0 (ksCube_zero (by norm_num))

theorem initial_value (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) :
    (initial P v hd hp).value=KSEighthManuscriptRun.initialState (KSEighthConvexRuntime.controller P.solver v hd hp) :=
  KSEighthCountedRun.makeState_value _ _ _ _

def initialBudget (P : KSPolynomialConvexSolver.PolynomialSolver) (N d : ℕ) :=
  50*(N+1)^3*(KSEighthCompiledQueries.queryCost P N d+20)+2

theorem initial_cost (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) :
    (initial P v hd hp).cost ≤ initialBudget P N d := by
  exact KSEighthCountedRun.makeState_cost (KSEighthConvexRuntime.controller P.solver v hd hp)
    (operations P v hd hp) (fun x _=>KSEighthCompiledQueries.actual_state_cost P v hd hp x)
    0 (ksCube_zero (by norm_num))

theorem face_cost (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1)
    (s : State (KSEighthConvexRuntime.controller P.solver v hd hp)) (hs : ¬KSEighthWalkRun.terminal s) :
    ((operations P v hd hp).covariance s hs).cost≤
      KSEighthConvexRuntime.covarianceBudget N d (KSEighthCompiledQueries.queryCost P N d) :=
  KSEighthConvexRuntime.covariance_cost P.solver v hd hp _
    (fun x _ hk y _=>KSEighthCompiledQueries.actual_face_cost P v hd hp x hk y) s hs

def evaluator (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) :=
  KSEighthCountedRun.evaluator (KSEighthConvexRuntime.controller P.solver v hd hp) (operations P v hd hp)
    (fun x _=>KSEighthCompiledQueries.actual_state_cost P v hd hp x) (face_cost P v hd hp)

def trialBudget (P : KSPolynomialConvexSolver.PolynomialSolver) (N d T : ℕ) : ℕ :=
  initialBudget P N d+
    KSEighthConvexRuntime.pathBudget N d (KSEighthCompiledQueries.queryCost P N d) T+
    (KSEighthCompiledQueries.queryCost P N d+28*N+18)+3

theorem leaf_execution (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) (T : ℕ)
    (l : (KSEighthManuscriptRun.run (KSEighthConvexRuntime.controller P.solver v hd hp) T
      (KSEighthManuscriptRun.initialState (KSEighthConvexRuntime.controller P.solver v hd hp))).Leaves) :
    ∃k r,KSOnlinePathRuntime.Executes (evaluator P v hd hp) T (initial P v hd hp).value
      ((KSEighthManuscriptRun.run (KSEighthConvexRuntime.controller P.solver v hd hp) T
        (KSEighthManuscriptRun.initialState (KSEighthConvexRuntime.controller P.solver v hd hp))).leafState l) k r ∧
      (initial P v hd hp).cost+k+
        (output P.solver v (Real.sqrt (epsilon v)) (ksRegularizerScale (epsilon v) (Fin d)) hd
          (KSEighthCompiledQueries.queries P v (ksRegularizerScale (epsilon v) (Fin d)) hd)
          (KSEighthConvexRuntime.controller P.solver v hd hp)
          ((KSEighthManuscriptRun.run (KSEighthConvexRuntime.controller P.solver v hd hp) T
            (KSEighthManuscriptRun.initialState (KSEighthConvexRuntime.controller P.solver v hd hp))).leafState l)).cost+3≤
        trialBudget P N d T ∧ r≤T := by
  obtain ⟨k,r,he,hk,hr⟩ := KSEighthCountedRun.leaf_execution
    (KSEighthConvexRuntime.controller P.solver v hd hp) (operations P v hd hp)
    (fun x _=>KSEighthCompiledQueries.actual_state_cost P v hd hp x) (face_cost P v hd hp) T _ l
  have hi := initial_cost P v hd hp
  let s := (KSEighthManuscriptRun.run (KSEighthConvexRuntime.controller P.solver v hd hp) T
    (KSEighthManuscriptRun.initialState (KSEighthConvexRuntime.controller P.solver v hd hp))).leafState l
  have ho := output_cost P.solver v (Real.sqrt (epsilon v)) (ksRegularizerScale (epsilon v) (Fin d)) hd
    (KSEighthCompiledQueries.queries P v (ksRegularizerScale (epsilon v) (Fin d)) hd)
    (KSEighthConvexRuntime.controller P.solver v hd hp) s
    (KSEighthCompiledQueries.actual_acceptance_cost P v hd hp s.coeff)
  refine ⟨k,r,?_,?_,hr⟩
  · rwa [initial_value]
  · change k≤KSEighthConvexRuntime.pathBudget N d (KSEighthCompiledQueries.queryCost P N d) T at hk
    unfold trialBudget
    dsimp only [s] at ho
    omega

end MatrixSpencer.KSEighthCompiledRun
