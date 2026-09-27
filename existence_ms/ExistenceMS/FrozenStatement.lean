import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

/-! Independent real symmetric input statements. N counts the matrices and
d is their dimension. Norms are explicitly Euclidean operator norms.
These are target definitions, not endpoint proof declarations. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace ExistenceMS.Frozen

def squareStatement (C : ℝ) : Prop :=
  ∀ (N d : ℕ), d ≤ N →
    ∀ A : Fin N → Matrix (Fin d) (Fin d) ℝ,
      (∀ i, (A i)ᵀ = A i) →
      (∀ i, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A i)‖ ≤ 1) →
      ∃ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ i, s i • A i)‖ ≤
          C * Real.sqrt (N : ℝ)

def rectangularStatement (C : ℝ) : Prop :=
  ∀ (N d : ℕ), 1 ≤ N → N ≤ d →
    ∀ A : Fin N → Matrix (Fin d) (Fin d) ℝ,
      (∀ i, (A i)ᵀ = A i) →
      (∀ i, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A i)‖ ≤ 1) →
      ∃ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ i, s i • A i)‖ ≤
          C * Real.sqrt ((N : ℝ) * Real.log (2 * (d : ℝ) / (N : ℝ)))

def combinedTarget : Prop :=
  squareStatement 100000000 ∧ rectangularStatement 100000000

end ExistenceMS.Frozen

