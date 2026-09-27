import FaithfulKS.Main
import Lean

/-! Audit the actual declaration dependency graph, rather than the broader
graph of imported modules. Types and proof/definition values are followed,
including opaque values. The old signing endpoints must not be reachable.
This command contributes no premise to the mathematical theorem. -/
namespace FaithfulKS.Audit
open Lean Elab Command
open scoped BigOperators Matrix

private partial def closure (env : Environment) (todo : List Name)
    (seen : NameSet) (order : List Name) : NameSet × List Name :=
  match todo with
  | [] => (seen, order)
  | n :: rest =>
    if seen.contains n then closure env rest seen order
    else
      let seen := seen.insert n
      match env.find? n with
      | none => closure env rest seen (n :: order)
      | some info =>
        let next := info.type.foldConsts rest fun c cs => c :: cs
        let next := match info.value? true with
          | none => next
          | some v => v.foldConsts next fun c cs => c :: cs
        closure env next seen (n :: order)

private def forbiddenPrefixes : List String :=
  ["SeamlessKS.RuntimeRun.", "SeamlessKS.RuntimeWalk.rawStep", "SeamlessKS.RuntimeWalk.step",
   "SeamlessKS.EndToEnd.", "SeamlessKS.Run.", "SeamlessKS.Restart.",
   "SeamlessKS.Walk.step", "SeamlessKS.Walk.rawStep",
   "MatrixSpencer.matrix_spencer_square", "MatrixSpencer.matrix_spencer_rectangular",
   "MatrixSpencer.kadison_singer_spin_mixed", "MatrixSpencer.kadison_singer_eighth",
   "MatrixSpencer.OriginalConjecture.matrix_spencer_original",
   "KadisonSingerOriginal.weaver_KS2",
   "MatrixSpencer.KSFullManuscriptWeaver.weaver_KS2",
   "MatrixSpencer.KSEighthManuscriptWeaver.weaver_KS2",
   "MatrixSpencer.KSExplicitWeaver.weaver_KS2",
   "MatrixSpencer.KSEighthExplicitWeaver.weaver_KS2"]

run_cmd do
  let (deps, names) := closure (← getEnv) [``FaithfulKS.polynomial_runtime_and_correctness] {} []
  let forbidden := names.filter fun n =>
    n != ``SeamlessKS.Walk.step._proof_1 &&
      forbiddenPrefixes.any fun p => p.isPrefixOf n.toString
  unless forbidden.isEmpty do
    throwError "An old endpoint/transition occurs in the proof closure: {forbidden}"
  let required := [``RadialKS.Run.completed, ``RadialKS.Run.state_budget_le,
    ``RadialKS.Walk.step, ``RadialKS.WalkGeometry.step_energy,
    ``RadialKS.WalkDrift.step_budget,
    ``RadialKS.LiveHessian.exists_unit_raw_negative_of_none,
    ``RadialKS.RuntimeRun.compute_execution, ``RadialKS.RuntimeRun.execution_cost,
    ``RadialKS.RuntimeDirection.compute_value, ``RadialKS.RuntimeDirection.compute_cost,
    ``RadialKS.RuntimeFrame.compute_value, ``RadialKS.RuntimeFrame.compute_cost,
    ``RadialKS.RuntimeSafety.safe, ``RadialKS.RawNumerics.chosen_potential,
    ``RadialKS.RuntimePolynomial.eval_polynomial, ``FaithfulKS.compute,
    ``FaithfulKS.compute_executes, ``FaithfulKS.compute_cost,
    ``SeamlessKS.RuntimeEmpty.execution, ``SeamlessKS.RuntimeEmpty.writeOnes_value,
    ``RadialKS.RuntimeDirection.spectral_execution,
    ``SeamlessKS.ExactEVD.compute_execution, ``SeamlessKS.Value.report_accuracy,
    ``SeamlessKS.NumericalRegularityParseval.joint_bounds,
    ``SeamlessKS.NumericalRegularityEnvelope.curve_fourth_le]
  for n in required do
    unless deps.contains n do
      throwError "The new walk dependency is absent: {n}"
  logInfo m!"Audited {names.length} declaration dependencies: old endpoint and transition prefixes absent; all required new radial-walk and implementation dependencies present."

/- Lean shares this generated proof of nonnegativity with the old initial
preparation code. It is a scalar parameter lemma, not the old transition. -/
example {N d : ℕ} (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : ∑ i, MatrixSpencer.KSRankOne.atom (v i) = 1) :
    0 ≤ SeamlessKS.Parameters.rho N :=
  SeamlessKS.Walk.step._proof_1 v hd hp

end FaithfulKS.Audit

#print axioms FaithfulKS.polynomial_runtime_and_correctness
