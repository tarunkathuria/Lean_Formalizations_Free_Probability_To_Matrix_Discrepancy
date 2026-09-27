import ExistenceKS.FrozenStatement
import Lean

/-! Independent primitive type audit. An audit command accepts only a theorem
declaration whose complete type is definitionally the frozen target. No
implicit proof arguments are inserted. These commands do not themselves
claim the endpoint exists; invoke them on the final new theorem. -/
open Matrix
open scoped BigOperators Matrix
noncomputable section
namespace ExistenceKS.Audit

def expectedStatement (C : ℝ) : Prop :=
  ∀ (N d : ℕ) (ε : ℝ), 0 ≤ ε →
    ∀ v : Fin N → Fin d → ℂ,
      (∑ i, (fun a b => v i a * star (v i b) : Matrix (Fin d) (Fin d) ℂ)) =
        (1 : Matrix (Fin d) (Fin d) ℂ) →
      (∀ i, ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (fun a b => v i a * star (v i b) : Matrix (Fin d) (Fin d) ℂ)‖ ≤ ε) →
      ∃ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
          (∑ i, (s i : ℂ) •
            (fun a b => v i a * star (v i b) : Matrix (Fin d) (Fin d) ℂ))‖ ≤
          C * Real.sqrt ε

def expectedRadial : Prop := expectedStatement 35
def expectedManuscript : Prop := expectedStatement 400

example : Frozen.radialTarget = expectedRadial := rfl
example : Frozen.manuscriptTarget = expectedManuscript := rfl


open Lean Elab Command in
private def checkEndpoint (target : Name) (expected : Name) : CommandElabM Unit :=
  liftTermElabM do
    let info ← getConstInfo target
    match info with
    | .thmInfo _ => pure ()
    | _ => throwError "The endpoint must be a theorem declaration."
    unless (← Meta.isDefEq info.type (mkConst expected)) do
      throwError "The endpoint does not match the independently frozen matrix-only statement."

open Lean Elab Command in
elab "audit_ks_endpoint " target:ident : command =>
  checkEndpoint target.getId ``expectedRadial

open Lean Elab Command in
elab "audit_ks_manuscript_endpoint " target:ident : command =>
  checkEndpoint target.getId ``expectedManuscript

end ExistenceKS.Audit
