import MatrixSpencer.RectangularSigningPotential
import MatrixSpencer.SmallLiveRounding

/-! Actual boundary rounding for the fixed global dyadic regularizer. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
namespace DyadicSmallLiveRounding
noncomputable section
open PhaseRestriction SmallLiveRounding
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance dyadicSmallLiveCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicSmallLiveSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

theorem complete_remainingPotential_le (m : ℕ) (θ : ℝ)
    (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {x : EuclideanSpace ℝ ι} (hx : ∀ i, |x i| ≤ 1) :
    rectangularRemainingPotential m θ offset A hA (complete x) ≤
      rectangularRemainingPotential m θ offset A hA x + Fintype.card (Live x) := by
  have hsub : frozenCoordinates x ⊆ frozenCoordinates (complete x) := by
    rw [complete_frozen_eq_univ]
    exact Finset.subset_univ _
  have hdrop := rectangularRemainingPotential_le_oldFamily m θ offset A hA hsub
  have hcost := regularizedOwnerPotential_sub_le_norm
    (epochCenter offset A hA x).property (epochCenter offset A hA (complete x)).property
    (restrictedFamily A x) (restrictedFamily_hermitian A hA x) Matrix.PosSemidef.one
    (dyadicTsallisRegularizer m θ) (continuousOn_density_dyadicTsallisRegularizer m θ)
  have hnorm := complete_center_norm_le offset A hA hN hx
  unfold rectangularRemainingPotential at *
  linarith

theorem complete_remainingPotential_le_small_sqrt (m : ℕ) (θ : ℝ)
    (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {x : EuclideanSpace ℝ ι} (hx : ∀ i, |x i| ≤ 1) (hsmall : Fintype.card (Live x) < 32) :
    rectangularRemainingPotential m θ offset A hA (complete x) ≤
      rectangularRemainingPotential m θ offset A hA x +
        64 * Real.sqrt (Fintype.card (Live x) : ℝ) :=
  (complete_remainingPotential_le m θ offset A hA hN hx).trans
    (add_le_add_left (small_nat_le_sqrt hsmall) _)

/-- Concrete completion preserves the existing signs and the fixed physical regularizer. -/
theorem exists_small_live_completion (m : ℕ) (θ : ℝ)
    (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {x : EuclideanSpace ℝ ι} (hx : ∀ i, |x i| ≤ 1) (hsmall : Fintype.card (Live x) < 32) :
    ∃ z : EuclideanSpace ℝ ι,
      (∀ i, IsSign (z i)) ∧ (∀ i ∈ frozenCoordinates x, z i = x i) ∧
      ‖x‖ ^ 2 ≤ ‖z‖ ^ 2 ∧ Fintype.card (Live z) = 0 ∧
      rectangularRemainingPotential m θ offset A hA z ≤
        rectangularRemainingPotential m θ offset A hA x +
          64 * Real.sqrt (Fintype.card (Live x) : ℝ) :=
  ⟨complete x, complete_isSign x, fun _ hi => complete_frozen x hi,
    complete_norm_sq_ge hx, complete_live_card x,
    complete_remainingPotential_le_small_sqrt m θ offset A hA hN hx hsmall⟩

end
end DyadicSmallLiveRounding
end MatrixSpencer
