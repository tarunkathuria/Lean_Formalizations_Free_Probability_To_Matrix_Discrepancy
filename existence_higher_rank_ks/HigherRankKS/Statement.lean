import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Frozen target for the Part III existence theorem

This file states the intended theorem using only matrix input assumptions.
ExistenceStatement is a proposition to be proved, not a theorem, axiom,
or hypothesis supplied to the eventual proof. No solver, potential,
curvature certificate, favorable direction, or termination witness is an input.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

/-- The matrix sum uses one scalar sign per original matrix. -/
def signedSum {N d : ℕ} (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (σ : Fin N → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ i, (σ i : ℂ) • A i

/-- Literal formulation of the pure existence statement in Part III.
The operator norm is written through the Euclidean continuous linear map. -/
def ExistenceStatement : Prop :=
  ∀ (N d r : ℕ) (ε : ℝ), 1 ≤ r → 0 ≤ ε →
    ∀ A : Fin N → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, (A i).PosSemidef) →
      (∑ i, A i) = 1 →
      (∀ i, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A i)‖ ≤ ε) →
      (∀ i, Matrix.rank (A i) ≤ r) →
      ∃ σ : Fin N → ℝ,
        (∀ i, σ i = 1 ∨ σ i = -1) ∧
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (signedSum A σ)‖ ≤
          min 1 (250 * Real.sqrt ε * Real.log (2 * (r : ℝ)))

end HigherRankKS
