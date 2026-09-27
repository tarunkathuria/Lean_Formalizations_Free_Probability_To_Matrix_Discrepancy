import FaithfulMS.RectangularDirectPolynomialRuntime
import MatrixSpencer.NatPolynomialBound

/-! Fixed polynomial majorants for the composed counted rectangular walk.
Local response and acceptance bounds are combined with the explicit cleanup,
preparation, retry and phase budgets. The final endpoint instantiates those
local bounds from concrete SDP and arithmetic routines. -/
namespace MatrixSpencer.RectangularDirectPolynomialMajorant
open NatPolynomialBound
set_option maxRecDepth 16384
set_option maxHeartbeats 1400000

open Lean Meta Elab Tactic in
private def polynomialProof : ℕ → Expr → MetaM Expr
  | 0, _ => throwError "Polynomial proof expression exceeds the structural depth bound"
  | fuel+1, f => lambdaTelescope f fun xs body => do
        if xs.size != 3 then throwError "Expected three natural inputs"
        if !xs.any (fun x => body.containsFVar x.fvarId!) then
          return ← mkAppM ``NatPolynomialBound.constant #[body]
        if body == xs[0]! then return mkConst ``NatPolynomialBound.first
        if body == xs[1]! then return mkConst ``NatPolynomialBound.second
        if body == xs[2]! then return mkConst ``NatPolynomialBound.third
        let args := body.getAppArgs
        let name := body.getAppFn.constName?
        if args.size < 2 then throwError "Unexpected polynomial node: {body}"
        if name == some ``RectangularDirectPrograms.Programs.responseBudget then
          return ← mkAppM ``RectangularDirectPrograms.Programs.response_polynomial #[args[1]!]
        if name == some ``RectangularDirectPrograms.Programs.acceptanceBudget then
          return ← mkAppM ``RectangularDirectPrograms.Programs.acceptance_polynomial #[args[1]!]
        let left := args[args.size-2]!
        let right := args[args.size-1]!
        let lf ← mkLambdaFVars xs left
        let lp ← polynomialProof fuel lf
        if name == some ``HPow.hPow || name == some ``Nat.pow then
          if xs.any (fun x => right.containsFVar x.fvarId!) then
            throwError "Input-dependent exponent is not a fixed polynomial"
          return ← mkAppM ``NatPolynomialBound.pow #[lp,right]
        let rf ← mkLambdaFVars xs right
        let rp ← polynomialProof fuel rf
        if name == some ``HAdd.hAdd || name == some ``Nat.add then
          return ← mkAppM ``NatPolynomialBound.add #[lp,rp]
        if name == some ``HMul.hMul || name == some ``Nat.mul then
          return ← mkAppM ``NatPolynomialBound.mul #[lp,rp]
        throwError "Unexpected polynomial operator: {body}"

open Lean Meta Elab Tactic in
elab "direct_ridge_polynomial_bound" : tactic => do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity ``NatPolynomialBound.Bounded 1 do
    throwError "Expected NatPolynomialBound.Bounded: {target.getAppFn.constName?} arity {target.getAppArgs.size}"
  let proof ← polynomialProof 2048 target.getAppArgs[0]!
  goal.assign proof
  replaceMainGoal []

/-- Every nested work expression in the actual full algorithm is polynomial
in its two original dimensions and confidence exponent k. -/
theorem budget_bounded (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) :
    NatPolynomialBound.Bounded (fun N d k => RectangularDirectPolynomialRuntime.budget S W N d k) := by
  dsimp only [RectangularDirectPolynomialRuntime.budget,
    RectangularDirectPolynomialRuntime.epochBudget,
    RectangularDirectCountedAcceptedEpoch.operations,
    RectangularRidgeRetryParameters.retries, RectangularRidgeRetryParameters.selected,
    RectangularDirectCompiledEpoch.budget, RectangularDirectCompiledEpoch.preparationBudget,
    RectangularDirectEpochWork.stepBudget, RectangularDirectPreparationWork.budget,
    RectangularDirectCountedPreparationRun.roundBudget,
    MSManuscriptPolynomialQueryCleanup.cleanupJacobi,
    MSManuscriptPolynomialQueryParameters.cleanupInv,
    KSJacobiPolynomialBounds.jacobi]
  direct_ridge_polynomial_bound

/-- The actual number of uniform-real draws has a fixed dimension/confidence
polynomial bound as well, including all rejected trials. -/
theorem randomDraws_bounded :
    NatPolynomialBound.Bounded (fun N d k => RectangularDirectPolynomialRuntime.randomDraws N d k) := by
  dsimp only [RectangularDirectPolynomialRuntime.randomDraws,
    RectangularDirectCountedAcceptedEpoch.randomDraws,
    RectangularRidgeRetryParameters.retries, RectangularRidgeRetryParameters.selected]
  direct_ridge_polynomial_bound

/-- Primitive quantifier order: the fixed solver determines one polynomial,
which simultaneously dominates work and randomness for every input size. -/
theorem exists_uniform_majorant (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) :
    ∃ C e : ℕ, 0 < C ∧ ∀ N d k : ℕ,
      RectangularDirectPolynomialRuntime.budget S W N d k ≤ C * (N + d + k + 2) ^ e ∧
      RectangularDirectPolynomialRuntime.randomDraws N d k ≤ C * (N + d + k + 2) ^ e := by
  obtain ⟨C,e,h⟩ := NatPolynomialBound.add (budget_bounded S W) randomDraws_bounded
  refine ⟨C+1,e,by omega,?_⟩
  intro N d k
  have hp := h N d k
  dsimp only at hp
  have hc : C * (N+d+k+2)^e ≤ (C+1) * (N+d+k+2)^e :=
    Nat.mul_le_mul_right _ (by omega)
  constructor <;> omega

end MatrixSpencer.RectangularDirectPolynomialMajorant
