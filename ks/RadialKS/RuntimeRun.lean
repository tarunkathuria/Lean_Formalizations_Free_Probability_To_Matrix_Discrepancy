import RadialKS.RuntimeWalk
import RadialKS.RuntimeSafety
import RadialKS.Run
import SeamlessKS.RuntimeParameters

/-! Sequential real-arithmetic execution of the deterministic radial walk.
The finite loop is padded with absorbing terminal steps. It has no random
input, retry loop, or final acceptance test. -/
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace RadialKS.RuntimeRun
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.KSPolynomialConvexSolver
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open SeamlessKS SeamlessKS.Parameters
variable {N d : ℕ} [Nonempty (Fin d)]

/-- Each constructor appends one evaluated, counted transition. -/
inductive Sequence (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) :
    ℕ → Walk.WalkState N → Walk.WalkState N → ℕ → Prop
  | zero (s) : Sequence P v hd hp 0 s s 1
  | succ {k s a c} (h : Sequence P v hd hp k s a c) :
      Sequence P v hd hp (k+1) s (RuntimeWalk.step P v hd hp a).value
        (c+(RuntimeWalk.step P v hd hp a).cost+2)

def loop (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : Walk.WalkState N) : ℕ → Counted (Walk.WalkState N)
  | 0 => ⟨s,1⟩
  | k+1 =>
    let a := loop P v hd hp s k
    let b := RuntimeWalk.step P v hd hp a.value
    ⟨b.value,a.cost+b.cost+2⟩

theorem loop_execution (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : Walk.WalkState N) (k : ℕ) :
    Sequence P v hd hp k s (loop P v hd hp s k).value (loop P v hd hp s k).cost := by
  induction k with
  | zero => exact Sequence.zero s
  | succ k ih => exact Sequence.succ ih

theorem sequence_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    {s a : Walk.WalkState N} {k c : ℕ} (he : Sequence P v hd hp k s a c) :
    a=DeterministicRun.run (Walk.step P.solver v hd hp) s k := by
  induction he with
  | zero s => rfl
  | succ he ih => simpa only [RuntimeWalk.step_value,ih,DeterministicRun.run]

theorem sequence_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    {s a : Walk.WalkState N} {k c : ℕ} (he : Sequence P v hd hp k s a c) :
    c≤k*(RuntimeWalk.stepBound P N d+2)+1 := by
  induction he with
  | zero s => simp
  | @succ k s a c he ih =>
    have hs := RuntimeWalk.step_cost P v hd hp a
    nlinarith

theorem loop_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : Walk.WalkState N) (k : ℕ) :
    (loop P v hd hp s k).value=DeterministicRun.run (Walk.step P.solver v hd hp) s k :=
  sequence_value P v hd hp (loop_execution P v hd hp s k)

def compute (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) : Counted (Fin N → ℝ) :=
  let setup := RuntimeParameters.compute v
  let init := RuntimeWalk.initial v hd hp
  let a := loop P v hd hp init.value setup.value.2
  let out := RuntimeAcceptance.copy a.value
  ⟨out.value,setup.cost+init.cost+a.cost+out.cost+4⟩

theorem compute_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) :
    (compute P v hd hp).value=Run.output P.solver v hd hp := by
  simp only [compute,RuntimeAcceptance.copy_value,RuntimeParameters.compute_value v hd hp,
    RuntimeWalk.initial_value,loop_value]
  rfl

/-- The complete execution includes safe scalar primitives, computed scales,
initialization, the sequence of transitions, and the final array copy. -/
def Executes (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (result : Fin N → ℝ) (cost : ℕ) : Prop :=
  RuntimeSafety.Safe v ∧ RuntimeParameters.SetupExecutes v ∧
  (RuntimeParameters.compute v).value=(RuntimeParameters.outputs v,horizon v) ∧
  ∃ a c, Sequence P v hd hp (horizon v) (RuntimeWalk.initial v hd hp).value a c ∧
    result=(RuntimeAcceptance.copy a).value ∧
    cost=(RuntimeParameters.compute v).cost+(RuntimeWalk.initial v hd hp).cost+c+
      (RuntimeAcceptance.copy a).cost+4

def costBound (P : PolynomialSolver) (N d : ℕ) : ℕ :=
  RuntimeParameters.costBound N d+RuntimeWalk.initialBound N+
    RuntimeBudgets.horizonCap N d*(RuntimeWalk.stepBound P N d+2)+3*N+6

theorem execution_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    {result : Fin N → ℝ} {cost : ℕ} (he : Executes P v hd hp result cost) :
    result=Run.output P.solver v hd hp := by
  obtain ⟨_,_,_,a,c,hs,rfl,_⟩ := he
  rw [RuntimeAcceptance.copy_value,sequence_value P v hd hp hs,RuntimeWalk.initial_value]
  rfl

theorem execution_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    {result : Fin N → ℝ} {cost : ℕ} (he : Executes P v hd hp result cost) :
    cost≤costBound P N d := by
  obtain ⟨_,_,_,a,c,hs,_,rfl⟩ := he
  have hh := (sequence_cost P v hd hp hs).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (RuntimeParameters.horizon_le v hd hp)) 1)
  have hi := RuntimeWalk.initial_cost v hd hp
  have hp' := RuntimeParameters.compute_cost v
  rw [RuntimeAcceptance.copy_cost]
  unfold costBound
  dsimp only [RuntimeWalk.initial,RuntimeWalk.initialBound] at hi ⊢
  omega

theorem compute_execution (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) :
    Executes P v hd hp (compute P v hd hp).value (compute P v hd hp).cost := by
  dsimp only [compute]
  rw [RuntimeParameters.compute_value v hd hp]
  exact ⟨RuntimeSafety.safe v hd hp,RuntimeParameters.setup_execution v hd hp,
    RuntimeParameters.compute_value v hd hp,_,_,loop_execution P v hd hp _ _,rfl,rfl⟩

/-- Correctness and a dimension-only work bound for the same computed output.
No source of random bits or draws occurs in this execution. -/
theorem guarantee (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    {ε : ℝ} (hε : 0≤ε) (hsize : ∀i,‖KSRankOne.atom (v i)‖≤ε) :
    ∃ cost, Executes P v hd hp (Run.output P.solver v hd hp) cost ∧
      cost≤costBound P N d ∧ (∀i,IsSign (Run.output P.solver v hd hp i)) ∧
      ‖∑i,Run.output P.solver v hd hp i • KSRankOne.atom (v i)‖≤35*Real.sqrt ε := by
  have he := compute_execution P v hd hp
  rw [compute_value P v hd hp] at he
  exact ⟨_,he,execution_cost P v hd hp he,Run.output_signs P.solver v hd hp,
    Run.output_norm_le P.solver v hd hp hε hsize⟩

end RadialKS.RuntimeRun
