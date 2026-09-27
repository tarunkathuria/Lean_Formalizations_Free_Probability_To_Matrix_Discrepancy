import SeamlessKS.Probability
import SeamlessKS.RuntimeRun
import SeamlessKS.RuntimeEmpty
import MatrixSpencer.KSRuntimePolynomialRepresentation

/-! The complete independent seamless full-cube theorem. It names the
actual output, normalized finite sampling law, sequential execution, and
boundary-only rounding. Its state stores only the coefficient array; value
queries use the signed discrepancy center with zero debit, and boundary
preparation updates only those coefficients. The computational model consists of the fixed polynomial
affine-SDP solver and the exact-EVD rule in `ExactEVD.Executes`. No analytic or drift interface remains in the statement. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.EndToEnd
open MatrixSpencer MatrixSpencer.KSPolynomialConvexSolver
open MatrixSpencer.KSRuntimePolynomialRepresentation
open SeamlessKS.State SeamlessKS.StatePotential SeamlessKS.Parameters SeamlessKS.Walk
set_option maxRecDepth 16384
set_option maxHeartbeats 6400000

/-- The displayed all-path arithmetic bound is literally a polynomial with
natural coefficients in label count, physical dimension, and retry count.
Its degree and coefficients may depend only on the fixed SDP solver. -/
theorem costBound_polynomial (P : PolynomialSolver) :
    Represented (RuntimeRun.costBound P) := by
  change Represented (fun N d r => RuntimeRun.costBound P N d r)
  simp only [RuntimeRun.costBound,RuntimeRun.trialBound,RuntimeParameters.costBound,
    RuntimeWalk.initialBound,RuntimeWalk.stepBound,RuntimeWalk.rawStepBound,
    RuntimeWalk.directionBound,RuntimeWalk.liveOutputBound,RuntimeAcceptance.costBound,
    RuntimeFace.reportBound,RuntimeLiveCoordinates.faceBound,RuntimeLiveCoordinates.extensionBound,
    RuntimeSelection.selectionBound,RuntimeQueries.queryBound,
    RuntimeQueries.programSize,RuntimeStateData.costBound,RuntimeBudgets.horizonCap,
    RuntimeBudgets.entryCap,
    RuntimeBudgets.localAccuracyInverseCap,RuntimeBudgets.hessianAccuracyInverseCap,
    RuntimeBudgets.queryInverseSquareCap,RuntimeBudgets.movementInverseSquareCap,
    RuntimeBudgets.derivativeCap,RuntimeBudgets.jointDerivativeCap,RuntimeBudgets.radiusInverseCap]
  ks_poly_cert

theorem drawBound_polynomial : Represented (fun N d r => r*RuntimeBudgets.horizonCap N d) := by
  simp only [RuntimeBudgets.horizonCap,RuntimeBudgets.movementInverseSquareCap,
    RuntimeBudgets.derivativeCap,RuntimeBudgets.jointDerivativeCap,RuntimeBudgets.radiusInverseCap]
  ks_poly_cert

variable {N d : ℕ} [Nonempty (Fin d)]

/-- All newly fixed coordinates are assigned only by the explicit boundary
preparation, after a local movement with displacement at most rho/8. -/
def BoundaryOnly (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) : Prop :=
  (∀ s : WalkState N, ∀ b i, |(Walk.step O v hd hp s b).coeff i|≤1) ∧
  (∀ s : WalkState N, ∀ hs : ¬Walk.terminal s, ∀ b i,
    |(Walk.rawStep O v hd hp s hs b).coeff i-s.coeff i|≤rho N/8) ∧
  (∀ s : WalkState N, ∀ hs : ¬Walk.terminal s, ∀ b i,
    (Walk.step O v hd hp s b).coeff i≠(Walk.rawStep O v hd hp s hs b).coeff i →
      1-|(Walk.rawStep O v hd hp s hs b).coeff i|≤rho N) ∧
  (∀ s : WalkState N, ∀ b i, |s.coeff i|=1 → (Walk.step O v hd hp s b).coeff i=s.coeff i)

theorem boundaryOnly (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) : BoundaryOnly O v hd hp := by
  refine ⟨?_,WalkGeometry.rawStep_displacement O v hd hp,?_,WalkGeometry.step_preserves_frozen O v hd hp⟩
  · intro s b i
    exact coeff_abs_le (Walk.step O v hd hp s b).toCubeState i
  · intro s hs b i hi
    simp only [Walk.step,dif_neg hs] at hi
    exact State.prepare_rounds_only_near (rho_pos (Input.labels_pos v hd hp)).le
      (Walk.rawStep O v hd hp s hs b) i hi

/-- Complete positive-dimensional theorem for the actual defined output.
The polynomial identity for its explicit work bound is `costBound_polynomial`.
All prospective draw sequences have a finite sequential execution, including
failed trials and retry exhaustion. -/
theorem guarantee (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    {ε : ℝ} (hε : 0≤ε) (hsize : ∀ i, ‖KSRankOne.atom (v i)‖≤ε) (r : ℕ) :
    (∀ z : Run.Draws P.solver v hd hp r, 0≤Run.drawWeight P.solver v hd hp r z) ∧
    (∑ z : Run.Draws P.solver v hd hp r,Run.drawWeight P.solver v hd hp r z)=1 ∧
    1-(1/4:ℝ)^r≤Run.successProbability P.solver v hd hp r ∧
    (∀ z : Run.Draws P.solver v hd hp r, ∀ σ : Fin N → ℝ,
      Run.output P.solver v hd hp r z=some σ →
        (∀ i,IsSign (σ i)) ∧ ‖∑ i,σ i • KSRankOne.atom (v i)‖≤400*Real.sqrt ε) ∧
    (∀ z : Run.Draws P.solver v hd hp r, ∃ cost draws,
      RuntimeRun.Executes P v hd hp r z (Run.output P.solver v hd hp r z) cost draws ∧
      cost≤RuntimeRun.costBound P N d r ∧ draws≤r*RuntimeBudgets.horizonCap N d) ∧
    BoundaryOnly P.solver v hd hp :=
  ⟨Run.drawWeight_nonneg P.solver v hd hp r,Run.drawWeight_sum P.solver v hd hp r,
    Probability.successProbability_ge P.solver v hd hp r,
    Probability.output_sound P.solver v hd hp hε hsize r,
    RuntimeRun.all_paths P v hd hp r,boundaryOnly P.solver v hd hp⟩

/-- In dimension zero, the literal all-ones program has linear cost and uses
no numerical solver or random draw. -/
theorem empty_dimension_guarantee (v : Fin N → Fin 0 → ℂ) {ε : ℝ} (hε : 0≤ε) :
    (∀ i,IsSign (RuntimeEmpty.output N i)) ∧
      ‖∑ i,RuntimeEmpty.output N i • KSRankOne.atom (v i)‖≤400*Real.sqrt ε ∧
      ∃ k ≤ RuntimeEmpty.costBound N,
        RealRAM.Program.Executes (RuntimeEmpty.program N) (RuntimeEmpty.input N)
          (RuntimeEmpty.output N) k :=
  RuntimeEmpty.guarantee v hε

end SeamlessKS.EndToEnd
