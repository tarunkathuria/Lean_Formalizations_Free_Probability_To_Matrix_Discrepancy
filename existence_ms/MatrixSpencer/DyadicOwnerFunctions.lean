import MatrixSpencer.DyadicDensityOptimizer
import MatrixSpencer.RegularizedFamilyDeletion

/-! Short names for the actual dyadic owner objective and its density supremum. -/
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section
variable {ι κ n : Type*} [Fintype ι] [Fintype κ] [Fintype n]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq n]

abbrev dyadicOwnerObjective (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (m : ℕ) (θ : ℝ) (S : Matrix n n ℂ) : ℝ :=
  regularizedOwnerObjective H A C (dyadicTsallisRegularizer m θ) S

abbrev dyadicOwnerPotential (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (m : ℕ) (θ : ℝ) : ℝ :=
  regularizedOwnerPotential H A C (dyadicTsallisRegularizer m θ)

omit [DecidableEq ι] [DecidableEq κ] in
theorem dyadicOwnerObjective_covarianceLift (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (U : Matrix ι κ ℝ) (K : Matrix κ κ ℝ)
    (m : ℕ) (θ : ℝ) (S : Matrix n n ℂ) :
    dyadicOwnerObjective H A (covarianceLift U K) m θ S =
      dyadicOwnerObjective H (mixFamily A U) K m θ S :=
  regularizedOwnerObjective_covarianceLift H A U K (dyadicTsallisRegularizer m θ) S

omit [DecidableEq ι] [DecidableEq κ] in
theorem dyadicOwnerPotential_covarianceLift (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (U : Matrix ι κ ℝ) (K : Matrix κ κ ℝ) (m : ℕ) (θ : ℝ) :
    dyadicOwnerPotential H A (covarianceLift U K) m θ =
      dyadicOwnerPotential H (mixFamily A U) K m θ :=
  regularizedOwnerPotential_covarianceLift H A U K (dyadicTsallisRegularizer m θ)

end
end MatrixSpencer
