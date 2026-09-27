import RadialKS.Run

/-! Mathematical correctness of the actual deterministic radial algorithm.
This theorem bounds the number of updates. A scalar-work or machine-runtime
theorem requires the separate implementation and its operation accounting. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace RadialKS.EndToEnd
open MatrixSpencer SeamlessKS.Parameters
variable {N d : ℕ} [Nonempty (Fin d)]

theorem guarantee (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0 < d) (hp : ∑ i, KSRankOne.atom (v i) = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hsize : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε) :
    (∀ i, IsSign (Run.output O v hd hp i)) ∧
      ‖∑ i, Run.output O v hd hp i • KSRankOne.atom (v i)‖ ≤ 35 * Real.sqrt ε ∧
      horizon v ≤ SeamlessKS.RuntimeBudgets.horizonCap N d :=
  ⟨Run.output_signs O v hd hp, Run.output_norm_le O v hd hp hε hsize,
    InitialBudget.horizon_bounded v hd hp⟩

end RadialKS.EndToEnd
