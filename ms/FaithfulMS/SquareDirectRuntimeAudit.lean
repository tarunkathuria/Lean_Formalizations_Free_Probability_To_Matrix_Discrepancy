import FaithfulMS.SquareDirectEndpoint
import Lean

/-! Transitive declaration audit of the directly computed-density algorithm.
This is a build-time check; it introduces no mathematical assumption. -/
namespace FaithfulMS.SquareDirectRuntimeAudit
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
  for n in [``DirectSDPArithmetic.square, ``DirectSDP.PolynomialService.run,
    ``DirectSDPDecode.density, ``DirectSDPDecode.affine,
    ``SquareDirectCountedResponse.compute, ``DirectGammaArithmetic.compute,
    ``DirectGammaArithmetic.transport, ``SquareDirectCountedTop.compute,
    ``SquareDirectEVD.direction, ``SquareDirectCountedPreparation.run,
    ``SquareDirectAcceptanceArithmetic.accepts, ``DirectMatrixArithmetic.tracePair,
    ``SimpleMS.flatCovariance, ``SimpleMS.UniformSampler.increment,
    ``SimpleMS.CountedSpectralSampler.increment, ``SimpleMS.CountedSpectralSampler.pick] do
    unless deps.contains n do
      throwError "Required direct-density walk dependency absent: {n}"
  logInfo m!"{target}: checked {names.length} declaration dependencies; the actual compiled primal SDP, density decoding, source transport, direct Gamma, two-trace acceptance, exact top EVD and uniform projection sampler are present; legacy finite-difference/report implementations are absent."

run_cmd audit ``SquareDirectRuntime.implementation
run_cmd audit ``SquareDirectRuntime.execution_bounded
run_cmd audit ``SquareDirectRuntime.execution_sound
run_cmd audit ``SquareDirectEndpoint.polynomial_algorithm

#print axioms SquareDirectRuntime.execution_bounded
#print axioms SquareDirectRuntime.execution_sound
#print axioms SquareDirectRuntime.constant_success
#print axioms SquareDirectEndpoint.polynomial_algorithm

end FaithfulMS.SquareDirectRuntimeAudit
