import FaithfulMS.Main
import FaithfulMS.DirectArithmeticAudit
import Lean

/-! Transitive audits of the public final theorems. These checks inspect
proof and implementation dependencies, rather than merely checking imports.
They introduce no assumptions and fail the build on legacy finite-difference
or solver-interface dependencies. -/
namespace FaithfulMS.MainAudit
open Lean Elab Command

private partial def closure (env : Environment) (todo : List Name)
    (seen : NameSet) (order : List Name) : NameSet × List Name :=
  match todo with
  | [] => (seen,order)
  | n::rest =>
    if seen.contains n then closure env rest seen order
    else
      let seen := seen.insert n
      match env.find? n with
      | none => closure env rest seen (n::order)
      | some info =>
        let next := info.type.foldConsts rest fun c cs => c::cs
        let next := match info.value? true with
          | none => next
          | some v => v.foldConsts next fun c cs => c::cs
        closure env next seen (n::order)

private def forbiddenPrefixes : List String :=
  ["MatrixSpencer.MSConvexOwnerValue.Oracle",
   "MatrixSpencer.KSPolynomialConvexSolver.PolynomialSolver",
   "MatrixSpencer.RectangularRidgeConvexValue.Solver",
   "MatrixSpencer.RectangularRidgeConvexValue.PolynomialSolver",
   "MatrixSpencer.MSConvexGammaMatrix.report",
   "MatrixSpencer.MSManuscriptGammaMatrix.report",
   "MatrixSpencer.MSConvexGammaDifference.report",
   "MatrixSpencer.MSManuscriptCertificateReport.tangentReport",
   "MatrixSpencer.MSManuscriptAnchorDensity.density",
   "MatrixSpencer.MSConvexCertificateReport.report",
   "MatrixSpencer.RectangularRidgeTangentValues.report",
   "MatrixSpencer.RectangularRidgeCountedResponse.response",
   "MatrixSpencer.MSConvexNumericalExplicit.output",
   "MatrixSpencer.MSManuscriptNumericalExplicit.output",
   "MatrixSpencer.RectangularRidgeOriginalAlgorithm.output"]

private def audit (target : Name) (required : List Name) : CommandElabM Unit := do
  let (deps,names) := closure (←getEnv) [target] {} []
  let forbidden := names.filter fun n => forbiddenPrefixes.any fun p => p.isPrefixOf n.toString
  unless forbidden.isEmpty do
    throwError "Legacy solver/report dependency: {forbidden}"
  for n in required do
    unless deps.contains n do
      throwError "Required implementation dependency absent: {n}"
  logInfo m!"{target}: checked {names.length} declarations; concrete direct-density implementation and counted conditional-uniform refinement are present, with no legacy solver or finite-difference implementation."

run_cmd (audit ``Main.matrix_spencer_square
  [``SquareDirectRuntime.implementation, ``SquareDirectSampling.Runtime.implementation,
   ``DirectSDPArithmetic.square, ``DirectSDP.PolynomialService.run,
   ``SquareDirectCountedResponse.compute, ``DirectGammaArithmetic.compute,
   ``SquareDirectAcceptanceArithmetic.accepts, ``DirectMatrixArithmetic.tracePair,
   ``SquareDirectCountedTop.compute, ``SquareDirectEVD.direction,
   ``SimpleMS.CountedSpectralSampler.pick])

run_cmd (audit ``Main.matrix_spencer_rectangular
  [``MatrixSpencer.RectangularDirectConcretePrograms.programs,
   ``MatrixSpencer.RectangularDirectConcreteResponse.response,
   ``MatrixSpencer.RectangularDirectConcreteAcceptance.accepts,
   ``DirectSDPArithmetic.rectangular, ``DirectSDP.PolynomialService.run,
   ``DirectGammaArithmetic.compute, ``DirectMatrixArithmetic.tracePair,
   ``MatrixSpencer.RectangularDirectCountedPreparationRun.direction,
   ``SquareDirectCountedTop.compute,
   ``RectangularDirectSampling.OriginalAlgorithm.implementation_refinement])

end FaithfulMS.MainAudit
