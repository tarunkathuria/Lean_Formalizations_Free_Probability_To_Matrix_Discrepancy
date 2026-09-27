import FaithfulExistenceMS.Main
import Lean

/-! Traverse declaration types and values, including opaque values, to
check that the actual revised movement lies in each proof dependency
closure and that no earlier signing endpoint supplies the conclusion. -/
namespace FaithfulExistenceMS.Audit
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
  ["MatrixSpencer.matrix_spencer_square", "MatrixSpencer.matrix_spencer_rectangular",
   "MatrixSpencer.kadison_singer_spin_mixed", "MatrixSpencer.kadison_singer_eighth",
   "MatrixSpencer.OriginalConjecture.matrix_spencer_original",
   "MatrixSpencer.MSManuscriptNumericalExplicit.exists_full_signing",
   "MatrixSpencer.MSManuscriptNumericalExplicit.matrix_spencer",
   "MatrixSpencer.RectangularRidgeOriginalAlgorithm.exists_signing",
   "MatrixSpencer.RectangularRidgeEndToEnd.",
   "MatrixSpencer.MSConvexGammaMatrix.report",
   "MatrixSpencer.MSManuscriptGammaMatrix.report",
   "MatrixSpencer.MSManuscriptAnchorDensity.density",
   "MatrixSpencer.KSNumericalOwnerPotential.report",
   "MatrixSpencer.MSManuscriptCertificateReport.tangentReport",
   "MatrixSpencer.RectangularRidgeConvexGamma."]

private def auditClosure (target : Name) (required : List Name) : CommandElabM Unit := do
  let (deps, names) := closure (← getEnv) [target] {} []
  let forbidden := names.filter fun n =>
    forbiddenPrefixes.any fun p => p.isPrefixOf n.toString
  unless forbidden.isEmpty do
    throwError "An old signing endpoint occurs in the proof closure: {forbidden}"
  for n in required do
    unless deps.contains n do
      throwError "A required new walk dependency is absent: {n}"
  logInfo m!"{target}: audited {names.length} declaration dependencies; old signing endpoints absent and required projection-walk dependencies present."

run_cmd do
  auditClosure ``FaithfulExistenceMS.exists_square
    [``SimpleMS.flatCovariance, ``SimpleMS.UniformSampler.increment,
     ``SimpleMS.SpectralFrame.vector, ``SimpleMS.SpectralFrame.eigenvalue_eq_one,
     ``SimpleMS.Movement.nextPoint,
     ``FaithfulMS.DirectSDP.exactService,
     ``FaithfulMS.DirectSDP.Service.squareSolution,
     ``FaithfulMS.SquareDirectGamma.response,
     ``FaithfulMS.SquareDirectAcceptance.savedDensity]

run_cmd do
  auditClosure ``FaithfulExistenceMS.exists_rectangular
    [``SimpleMS.flatCovariance, ``SimpleMS.UniformSampler.increment,
     ``SimpleMS.SpectralFrame.vector, ``SimpleMS.SpectralFrame.eigenvalue_eq_one,
     ``SimpleMS.RelativeLiveTrace.trace_positive_of_ledger,
     ``MatrixSpencer.RectangularDirectOriginal.output,
     ``FaithfulMS.DirectSDP.exactService,
     ``FaithfulMS.DirectSDP.Service.rectangularSolution,
     ``MatrixSpencer.RectangularDirectSolver.value,
     ``MatrixSpencer.RectangularDirectAcceptance.tangentReport]

end FaithfulExistenceMS.Audit

#print axioms FaithfulExistenceMS.exists_square
#print axioms FaithfulExistenceMS.exists_rectangular
