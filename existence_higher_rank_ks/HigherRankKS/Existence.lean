import HigherRankKS.LocalAlternative
import HigherRankKS.SubisotropicStatementAdapter

/-! Pure existence via the actual nonlinear carrier potential, endpoint
certificate, negative curvature, and compact-minimum argument. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

/-- The full subisotropic target, with the local analytic obligation discharged. -/
theorem subisotropic_existence : SubisotropicExistenceStatement := by
  apply subisotropicExistenceStatement_of_dyadic_local_alternatives
  intro N d hd A hA _ k hk
  letI : NeZero d := ⟨hd.ne'⟩
  exact local_alternative_at_minima A hA k hk

/-- The original isotropic target. -/
theorem existence : ExistenceStatement :=
  existenceStatement_of_subisotropic subisotropic_existence

/-- One sign per original PSD matrix, with no analytic, solver, or runtime
certificate among the hypotheses. The norm is the Euclidean operator norm. -/
theorem exists_signing {N d r : ℕ} {ε : ℝ} (hr : 1 ≤ r) (hε : 0 ≤ ε)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hsum : (∑ i, A i) ≤ 1)
    (hnorm : ∀ i, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A i)‖ ≤ ε)
    (hrank : ∀ i, Matrix.rank (A i) ≤ r) :
    ∃ σ : Fin N → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (signedSum A σ)‖ ≤
        min 1 (250 * Real.sqrt ε * Real.log (2 * (r : ℝ))) :=
  subisotropic_existence N d r ε hr hε A hA hsum hnorm hrank

end HigherRankKS
