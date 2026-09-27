import HigherRankKS.Statement

/-! Public targets for the new existence proof. These definitions introduce
no assumptions beyond the matrix input hypotheses and no computational model. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS

def SubisotropicExistenceStatement : Prop :=
  ∀ (N d r : ℕ) (ε : ℝ), 1 ≤ r → 0 ≤ ε →
    ∀ A : Fin N → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, (A i).PosSemidef) → (∑ i, A i) ≤ 1 →
      (∀ i, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A i)‖ ≤ ε) →
      (∀ i, Matrix.rank (A i) ≤ r) →
      ∃ σ : Fin N → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (HigherRankKS.signedSum A σ)‖ ≤
          min 1 (10000 * Real.sqrt (ε * Real.log (2 * (r : ℝ))))

def ExistenceStatement : Prop :=
  ∀ (N d r : ℕ) (ε : ℝ), 1 ≤ r → 0 ≤ ε →
    ∀ A : Fin N → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, (A i).PosSemidef) → (∑ i, A i) = 1 →
      (∀ i, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A i)‖ ≤ ε) →
      (∀ i, Matrix.rank (A i) ≤ r) →
      ∃ σ : Fin N → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (HigherRankKS.signedSum A σ)‖ ≤
          min 1 (10000 * Real.sqrt (ε * Real.log (2 * (r : ℝ))))

theorem existenceStatement_of_subisotropic (h : SubisotropicExistenceStatement) :
    ExistenceStatement := by
  intro N d r ε hr hε A hA hsum hnorm hrank
  exact h N d r ε hr hε A hA hsum.le hnorm hrank

end AugmentedHigherRankKS
