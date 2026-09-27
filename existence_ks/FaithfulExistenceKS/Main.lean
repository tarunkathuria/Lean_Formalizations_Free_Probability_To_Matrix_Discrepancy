import ExistenceKS.Verified

/-! The existence-only statement in literal vector notation. Its proof uses
the exact variational value constructed in this package and the radial walk;
it quantifies no computational primitive or polynomial-work contract. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulExistenceKS

theorem exists_signing (N d : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (v : Fin N → Fin d → ℂ)
    (hp : (∑ i, (fun a b => v i a * star (v i b) : Matrix (Fin d) (Fin d) ℂ)) = (1 : Matrix (Fin d) (Fin d) ℂ))
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖^2 ≤ ε) :
    ∃ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (∑ i, (s i : ℂ) •
          (fun a b => v i a * star (v i b) : Matrix (Fin d) (Fin d) ℂ))‖ ≤
        35 * Real.sqrt ε := by
  apply ExistenceKS.exists_signing N d ε hε v hp
  intro i
  change ‖MatrixSpencer.KSRankOne.atom (v i)‖ ≤ ε
  simpa only [MatrixSpencer.KSRankOne.atom_norm,
    MatrixSpencer.KSRankOne.realTrace_atom_eq_norm_sq] using hsize i

end FaithfulExistenceKS
