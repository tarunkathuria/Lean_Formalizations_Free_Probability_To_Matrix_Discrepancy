import ExistenceMS.FrozenStatement
import Lean

/-! Independent primitive type audit. An audit command accepts only a theorem
declaration whose complete type is definitionally the frozen target. No
implicit proof arguments are inserted. These commands do not themselves
claim the endpoint exists; invoke them on the final new theorem. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace ExistenceMS.Audit

def expectedSquare (C : ℝ) : Prop :=
  ∀ (N d : ℕ), d ≤ N →
    ∀ A : Fin N → Matrix (Fin d) (Fin d) ℝ,
      (∀ i, (A i)ᵀ = A i) →
      (∀ i, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A i)‖ ≤ 1) →
      ∃ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ i, s i • A i)‖ ≤
          C * Real.sqrt (N : ℝ)

def expectedRectangular (C : ℝ) : Prop :=
  ∀ (N d : ℕ), 1 ≤ N → N ≤ d →
    ∀ A : Fin N → Matrix (Fin d) (Fin d) ℝ,
      (∀ i, (A i)ᵀ = A i) →
      (∀ i, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A i)‖ ≤ 1) →
      ∃ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ i, s i • A i)‖ ≤
          C * Real.sqrt ((N : ℝ) * Real.log (2 * (d : ℝ) / (N : ℝ)))

def expectedCombined : Prop :=
  expectedSquare 100000000 ∧ expectedRectangular 100000000


def expectedSquareTarget : Prop := expectedSquare 100000000
def expectedRectangularTarget : Prop := expectedRectangular 100000000

example : Frozen.combinedTarget = expectedCombined := rfl
example : Frozen.squareStatement 100000000 = expectedSquareTarget := rfl
example : Frozen.rectangularStatement 100000000 = expectedRectangularTarget := rfl

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
elab "audit_ms_square_endpoint " target:ident : command =>
  checkEndpoint target.getId ``expectedSquareTarget

open Lean Elab Command in
elab "audit_ms_rectangular_endpoint " target:ident : command =>
  checkEndpoint target.getId ``expectedRectangularTarget

open Lean Elab Command in
elab "audit_ms_combined_endpoint " target:ident : command =>
  checkEndpoint target.getId ``expectedCombined

end ExistenceMS.Audit
