import FaithfulMS.SquareDirectExplicit
import Lean

/-! Transitive declaration audit of the directly computed-density algorithm.
This is a build-time check; it introduces no mathematical assumption. -/
namespace FaithfulMS.SquareDirectAudit
open Lean Elab Command

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
  ["MatrixSpencer.MSConvexGammaMatrix.report",
   "MatrixSpencer.MSManuscriptGammaMatrix.report",
   "MatrixSpencer.MSConvexGammaDifference.report",
   "MatrixSpencer.MSManuscriptCertificateReport.tangentReport",
   "MatrixSpencer.MSManuscriptAnchorDensity.density",
   "MatrixSpencer.KSNumericalOwnerPotential.report",
   "MatrixSpencer.MSConvexCertificateReport.report",
   "MatrixSpencer.MSConvexNumericalExplicit.output",
   "MatrixSpencer.MSManuscriptNumericalExplicit.output",
   "MatrixSpencer.matrix_spencer_square"]

private def audit (target : Name) : CommandElabM Unit := do
  let (deps, names) := closure (← getEnv) [target] {} []
  let forbidden := names.filter fun n => forbiddenPrefixes.any fun p => p.isPrefixOf n.toString
  unless forbidden.isEmpty do
    throwError "Legacy finite-difference/report/endpoint dependency: {forbidden}"
  for n in [``DirectSDP.Service.squareSolution, ``DirectDensity.gamma,
    ``SquareDirectGamma.response, ``SquareDirectGamma.direction,
    ``SquareDirectEVD.output, ``SquareDirectPreparation.run,
    ``SquareDirectAcceptance.savedSolution, ``SquareDirectAcceptance.tangentReport,
    ``SquareDirectAcceptance.endpointValue,
    ``SimpleMS.flatCovariance, ``SimpleMS.UniformSampler.increment] do
    unless deps.contains n do
      throwError "Required direct-density walk dependency absent: {n}"
  logInfo m!"{target}: checked {names.length} declaration dependencies; direct SDP densities, direct Gamma, saved trace, exact top EVD, and uniform projection movement present; legacy value-difference/density iteration absent."

run_cmd audit ``SquareDirectExplicit.output
run_cmd audit ``SquareDirectExplicit.output_sound
run_cmd audit ``SquareDirectExplicit.constant_success

#print axioms SquareDirectExplicit.output_sound
#print axioms SquareDirectExplicit.constant_success
#print axioms SquareDirectExplicit.exists_full_signing

end FaithfulMS.SquareDirectAudit
