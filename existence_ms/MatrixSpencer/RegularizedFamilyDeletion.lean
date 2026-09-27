import MatrixSpencer.RegularizedOwnerPotential
import MatrixSpencer.FamilyDeletion

/-!
# Family restriction with the same physical density regularizer

Changing coefficient coordinates preserves the actual objective. Deleting
labels decreases the owner covariance and hence its optimized potential.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section

variable {ι κ n : Type*} [Fintype ι] [Fintype κ] [Fintype n]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq n]

omit [DecidableEq ι] [DecidableEq κ] in
theorem regularizedOwnerObjective_covarianceLift (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (U : Matrix ι κ ℝ) (K : Matrix κ κ ℝ)
    (R : Matrix n n ℂ → ℝ) (S : Matrix n n ℂ) :
    regularizedOwnerObjective H A (covarianceLift U K) R S =
      regularizedOwnerObjective H (mixFamily A U) K R S := by
  unfold regularizedOwnerObjective
  rw [covarianceSource_rectangular_mixing]

omit [DecidableEq ι] [DecidableEq κ] in
theorem regularizedOwnerPotential_covarianceLift (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (U : Matrix ι κ ℝ) (K : Matrix κ κ ℝ)
    (R : Matrix n n ℂ → ℝ) :
    regularizedOwnerPotential H A (covarianceLift U K) R =
      regularizedOwnerPotential H (mixFamily A U) K R := by
  unfold regularizedOwnerPotential
  congr 2
  funext S
  exact regularizedOwnerObjective_covarianceLift H A U K R S

theorem regularizedOwnerPotential_subfamily_le [Nonempty n] (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (e : κ ↪ ι)
    (R : Matrix n n ℂ → ℝ) (hR : ContinuousOn R densitySet) :
    regularizedOwnerPotential H (fun j => A (e j)) 1 R ≤ regularizedOwnerPotential H A 1 R := by
  rw [← mixFamily_familyInclusion A e, ← regularizedOwnerPotential_covarianceLift]
  exact regularizedOwnerPotential_mono_covariance H A hA
    (covarianceLift_posSemidef _ Matrix.PosSemidef.one) Matrix.PosSemidef.one
    (covarianceLift_le_one _ (familyInclusion_isometry e) le_rfl) R hR

end
end MatrixSpencer
