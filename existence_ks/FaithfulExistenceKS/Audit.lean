import FaithfulExistenceKS.Main
import Lean

/-! Audit the actual declaration dependency graph, rather than the broader
graph of imported modules. Types and proof/definition values are followed,
including opaque values. The old signing endpoints must not be reachable.
This command contributes no premise to the mathematical theorem. -/
namespace FaithfulExistenceKS.Audit
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
  ["SeamlessKS.EndToEnd.", "SeamlessKS.Run.", "SeamlessKS.Restart.",
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
  let (deps, names) := closure (← getEnv) [``FaithfulExistenceKS.exists_signing] {} []
  let forbidden := names.filter fun n =>
    n != ``SeamlessKS.Walk.step._proof_1 &&
      forbiddenPrefixes.any fun p => p.isPrefixOf n.toString
  unless forbidden.isEmpty do
    throwError "An old endpoint/transition occurs in the proof closure: {forbidden}"
  let required := [``RadialKS.Run.completed, ``RadialKS.Run.state_budget_le,
    ``RadialKS.Walk.step, ``RadialKS.WalkGeometry.step_energy,
    ``RadialKS.WalkDrift.step_budget,
    ``RadialKS.LiveHessian.exists_unit_raw_negative_of_none,
    ``ExistenceKS.ExactValue.specification]
  for n in required do
    unless deps.contains n do
      throwError "The new walk dependency is absent: {n}"
  logInfo m!"Audited {names.length} declaration dependencies: old endpoint and transition prefixes absent; all required new radial-walk dependencies present."

/- Lean shares this generated proof of nonnegativity with the old initial
preparation code. It is a scalar parameter lemma, not the old transition. -/
example {N d : ℕ} (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : ∑ i, MatrixSpencer.KSRankOne.atom (v i) = 1) :
    0 ≤ SeamlessKS.Parameters.rho N :=
  SeamlessKS.Walk.step._proof_1 v hd hp

end FaithfulExistenceKS.Audit

#print axioms FaithfulExistenceKS.exists_signing
