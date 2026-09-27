import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Real.Sqrt

/-! Independently stated mathematical targets, using primitive matrices,
literal signs and explicit Euclidean operator norms. These definitions are
specifications, not completed endpoint theorems. -/
open Matrix
open scoped BigOperators Matrix
noncomputable section
namespace ExistenceKS.Frozen

def statement (C : ℝ) : Prop :=
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

def radialTarget : Prop := statement 35
def manuscriptTarget : Prop := statement 400

end ExistenceKS.Frozen
