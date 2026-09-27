import RadialKS.WalkGeometry
import RadialKS.WalkDrift
import RadialKS.InitialBudget

/-! The defined deterministic radial run and its mathematical output.
The local progress and potential estimates are theorems of the concrete
walk. No transition, curvature or success certificate is an input here. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace RadialKS.Run
open MatrixSpencer SeamlessKS.State SeamlessKS.StatePotential SeamlessKS.Parameters
open RadialKS.Progress RadialKS.DeterministicRun
variable {N d : ℕ} [Nonempty (Fin d)]

def state (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i, KSRankOne.atom (v i) = 1) (t : ℕ) :
    SeamlessKS.Walk.WalkState N :=
  run (Walk.step O v hd hp) (Walk.initial v hd hp) t

def output (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i, KSRankOne.atom (v i) = 1) : Fin N → ℝ :=
  (state O v hd hp (horizon v)).coeff

theorem completed (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i, KSRankOne.atom (v i) = 1) :
    SeamlessKS.State.terminal (state O v hd hp (horizon v)).toCubeState := by
  apply run_terminal (Walk.step O v hd hp)
    (fun s hs => Walk.step_terminal O v hd hp s hs)
    (fun s hs => WalkGeometry.step_energy O v hd hp s hs)
  exact InitialBudget.horizon_strict v hd hp

theorem output_signs (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i, KSRankOne.atom (v i) = 1) :
    ∀ i, IsSign (output O v hd hp i) :=
  (terminal_iff_signing (state O v hd hp (horizon v)).toCubeState).mp
    (completed O v hd hp)

theorem state_budget_le (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i, KSRankOne.atom (v i) = 1) (t : ℕ) :
    budget v (SeamlessKS.Input.theta v) (zeta N) (beta v)
        (state O v hd hp t).toCubeState ≤
      budget v (SeamlessKS.Input.theta v) (zeta N) (beta v)
        (Walk.initial v hd hp).toCubeState :=
  run_monotone (Walk.step O v hd hp)
    (fun s => budget v (SeamlessKS.Input.theta v) (zeta N) (beta v) s.toCubeState)
    (WalkDrift.step_budget O v hd hp) (Walk.initial v hd hp) t

/-- The spectral bound holds throughout the run, as well as at the vertex. -/
theorem state_norm_lt (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i, KSRankOne.atom (v i) = 1) (t : ℕ) :
    ‖signedSum v (state O v hd hp t).coeff‖ < 35 * SeamlessKS.Input.delta v := by
  have hn := norm_le_budget v (SeamlessKS.Input.theta_pos v hd hp) (zeta N)
    (beta_pos v hd hp).le (state O v hd hp t).toCubeState
  exact (hn.trans (state_budget_le O v hd hp t)).trans_lt
    (InitialBudget.initial_budget_lt v hd hp)

theorem output_norm_lt (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i, KSRankOne.atom (v i) = 1) :
    ‖∑ i, output O v hd hp i • KSRankOne.atom (v i)‖ <
      35 * SeamlessKS.Input.delta v :=
  state_norm_lt O v hd hp (horizon v)

theorem output_norm_le (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i, KSRankOne.atom (v i) = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hsize : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε) :
    ‖∑ i, output O v hd hp i • KSRankOne.atom (v i)‖ ≤ 35 * Real.sqrt ε := by
  have hδ : SeamlessKS.Input.delta v ≤ Real.sqrt ε :=
    Real.sqrt_le_sqrt (SeamlessKS.Input.epsilon_le v hε hsize)
  exact (output_norm_lt O v hd hp).le.trans
    (mul_le_mul_of_nonneg_left hδ (by norm_num))

end RadialKS.Run
