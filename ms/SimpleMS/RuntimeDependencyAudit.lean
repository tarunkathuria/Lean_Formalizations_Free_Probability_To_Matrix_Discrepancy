import SimpleMS.Audit
import Lean

/-! Check that both complete runtime proofs use the revised computed projection and uniform sampler. -/
namespace SimpleMS.RuntimeDependencyAudit
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

private def audit (target : Name) : CommandElabM Unit := do
  let (deps, names) := closure (← getEnv) [target] {} []
  let required := [``SimpleMS.flatCovariance, ``SimpleMS.UniformSampler.increment,
    ``SimpleMS.SpectralFrame.eigenvalue_eq_one, ``SimpleMS.CountedHighProjection.value,
    ``SimpleMS.CountedHighProjection.hermitianValue,
    ``SimpleMS.CountedSpectralSampler.pick,
    ``SimpleMS.CountedSpectralSampler.weights_value,
    ``SimpleMS.CountedSpectralSampler.increment_value,
    ``MatrixSpencer.RealRAM.MSCovariance.covariance_value]
  for n in required do
    unless deps.contains n do
      throwError "A required new projection implementation is absent: {n}"
  logInfo m!"{target}: {names.length} declaration dependencies; required new projection construction and uniform-sampling implementation present."

run_cmd audit ``SimpleMS.Square.polynomial_runtime_and_constant_success
run_cmd audit ``SimpleMS.Rectangular.polynomial_algorithm
end SimpleMS.RuntimeDependencyAudit
