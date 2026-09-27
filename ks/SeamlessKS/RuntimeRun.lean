import SeamlessKS.RuntimeWalk
import SeamlessKS.RuntimeParameters
import SeamlessKS.RuntimeRetry
import SeamlessKS.RuntimeSafety

/-! Sequential execution of the actual seamless output. A trial follows one
chosen path of the specified finite law; it does not construct the probability
tree. The setup is charged once, initialization once per inspected trial,
and no further trial is executed after acceptance. -/
open scoped BigOperators
noncomputable section
namespace SeamlessKS.RuntimeRun
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.KSPolynomialConvexSolver
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open SeamlessKS.Walk
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable
variable {N d : ℕ} [Nonempty (Fin d)]

/-- The primitive initialization and the online path are both charged. -/
def TrialExecutes (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (l : (Run.attempt P.solver v hd hp).Leaves) (cost draws : ℕ) : Prop :=
  ∃ k, KSOnlinePathRuntime.Executes (RuntimeWalk.evaluator P v hd hp)
    (Parameters.horizon v) (RuntimeWalk.initial v hd hp).value
    ((Run.attempt P.solver v hd hp).leafState l) k draws ∧
    cost=(RuntimeWalk.initial v hd hp).cost+k+3

def trialBound (P : PolynomialSolver) (N d : ℕ) : ℕ :=
  RuntimeWalk.initialBound N+
    RuntimeBudgets.horizonCap N d*(12*N+2+RuntimeWalk.stepBound P N d+3)+(12*N+2)+5

theorem trial_exists (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (l : (Run.attempt P.solver v hd hp).Leaves) :
    ∃ k draws, TrialExecutes P v hd hp l k draws := by
  obtain ⟨k,draws,he⟩ := KSOnlinePathRuntime.coin_leaf_execution
    (RuntimeWalk.evaluator P v hd hp) (Parameters.horizon v) (Walk.initial v hd hp) l
  refine ⟨(RuntimeWalk.initial v hd hp).cost+k+3,draws,k,?_,rfl⟩
  rwa [RuntimeWalk.initial_value]

theorem trial_budget (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (l : (Run.attempt P.solver v hd hp).Leaves) (cost draws : ℕ)
    (he : TrialExecutes P v hd hp l cost draws) :
    cost≤trialBound P N d ∧ draws≤RuntimeBudgets.horizonCap N d := by
  obtain ⟨k,he,rfl⟩ := he
  have hb := KSOnlinePathRuntime.execution_budget (RuntimeWalk.evaluator P v hd hp)
    (RuntimeWalk.evaluator_test_cost P v hd hp)
    (fun s _ i => RuntimeWalk.evaluator_child_cost P v hd hp s i) he
  have hi := RuntimeWalk.initial_cost v hd hp
  have ht := RuntimeParameters.horizon_le v hd hp
  constructor
  · have hm := Nat.mul_le_mul_right (12*N+2+RuntimeWalk.stepBound P N d+3) ht
    unfold trialBound
    omega
  · exact hb.2.trans ht

/-- The exact new retry output is identified with the computed acceptance
and copy operations, on the same product of potential draws. -/
theorem firstAccepted_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (r : ℕ) (z : Run.Draws P.solver v hd hp r) :
    TrialProbability.Retry.firstAccepted
      (fun l => (RuntimeAcceptance.copy ((Run.attempt P.solver v hd hp).leafState l)).value)
      (fun l => (RuntimeAcceptance.accepts v ((Run.attempt P.solver v hd hp).leafState l)).value)
      r z=Run.output P.solver v hd hp r z := by
  simp only [RuntimeAcceptance.copy_value,RuntimeAcceptance.accepts_value v hd hp]
  rfl

/-- Complete execution, including the scalar setup and its computed horizon.
The retry relation records each actually inspected path and chosen branch. -/
def Executes (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (r : ℕ) (z : Run.Draws P.solver v hd hp r)
    (result : Option (Fin N → ℝ)) (cost draws : ℕ) : Prop :=
  RuntimeSafety.Safe v ∧
  RuntimeParameters.SetupExecutes v ∧
  (RuntimeParameters.compute v).value=
    (RuntimeParameters.outputs v,Parameters.horizon v) ∧
  ∃ retryCost : ℕ, RuntimeRetry.Executes (TrialExecutes P v hd hp)
    (Run.attempt P.solver v hd hp).leafState (RuntimeAcceptance.accepts v)
    RuntimeAcceptance.copy r z result retryCost draws ∧
    cost=(RuntimeParameters.compute v).cost+retryCost+4

def costBound (P : PolynomialSolver) (N d r : ℕ) : ℕ :=
  RuntimeParameters.costBound N d+
    r*(trialBound P N d+RuntimeAcceptance.costBound N d+(3*N+1)+3)+5

theorem execution_output (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    {r cost draws : ℕ} {z : Run.Draws P.solver v hd hp r}
    {result : Option (Fin N → ℝ)} (he : Executes P v hd hp r z result cost draws) :
    result=Run.output P.solver v hd hp r z := by
  obtain ⟨_,_,_,k,hr,_⟩ := he
  exact (RuntimeRetry.executes_result hr).trans (firstAccepted_value P v hd hp r z)

/-- Every certified execution obeys the same input-only budget, including
executions that stop immediately at an already completed state. -/
theorem execution_budget (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    {r cost draws : ℕ} {z : Run.Draws P.solver v hd hp r}
    {result : Option (Fin N → ℝ)} (he : Executes P v hd hp r z result cost draws) :
    cost≤costBound P N d r ∧ draws≤r*RuntimeBudgets.horizonCap N d := by
  obtain ⟨_,_,_,k,hr,rfl⟩ := he
  have hb := RuntimeRetry.executes_budget (trial_budget P v hd hp)
    (fun l => RuntimeAcceptance.accepts_cost v _)
    (fun l => (RuntimeAcceptance.copy_cost _).le) hr
  have hs := RuntimeParameters.compute_cost v
  constructor
  · unfold costBound
    omega
  · exact hb.2

/-- Every prospective draw sequence has an actual sequential execution to
exactly `Run.output`. Both cost and finite-draw bounds are proved from the
input and the fixed polynomial solver; neither is an additional premise. -/
theorem all_paths (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (r : ℕ) (z : Run.Draws P.solver v hd hp r) :
    ∃ cost draws, Executes P v hd hp r z (Run.output P.solver v hd hp r z) cost draws ∧
      cost≤costBound P N d r ∧ draws≤r*RuntimeBudgets.horizonCap N d := by
  obtain ⟨k,draws,he,hk,hr⟩ := RuntimeRetry.exists_execution_bounded
    (TrialExecutes P v hd hp) (Run.attempt P.solver v hd hp).leafState
    (RuntimeAcceptance.accepts v) RuntimeAcceptance.copy (trial_exists P v hd hp)
    (trial_budget P v hd hp)
    (fun l => RuntimeAcceptance.accepts_cost v _)
    (fun l => (RuntimeAcceptance.copy_cost _).le) r z
  rw [firstAccepted_value] at he
  refine ⟨(RuntimeParameters.compute v).cost+k+4,draws,
    ⟨RuntimeSafety.safe v hd hp,RuntimeParameters.setup_execution v hd hp,
      RuntimeParameters.compute_value v hd hp,k,he,rfl⟩,?_,hr⟩
  have hs := RuntimeParameters.compute_cost v
  unfold costBound
  omega

end SeamlessKS.RuntimeRun
