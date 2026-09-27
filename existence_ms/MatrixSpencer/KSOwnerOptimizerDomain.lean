import MatrixSpencer.KSOwnerInputBounds
import MatrixSpencer.KSFullHermitianChart
import MatrixSpencer.OwnerPotential

/-!
# An explicit optimizer domain derived from the original owner inputs

The floor is an arithmetic expression in the input-entry center and Kraus
budgets. A scalar cap ensures feasibility of the maximally mixed initial
state. The actual canonical optimizer is used only as the mathematical target;
its membership, maximality, and equality with the original owner potential are
proved from the owner input assumptions.
-/

open Matrix Set
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace MatrixSpencer.KSOwnerOptimizerDomain

open KSOwnerInputBounds KSFullHermitianChart KSObjectiveChart
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance

/-- The actual positive optimizer floor, capped to leave an explicit initial density. -/
def optimizerFloor (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) : ℝ :=
  min ((θ / KSOptimizerFloor.inputDenominator (n := Fin d) (centerBound H) (krausBudget A C) θ) ^ 2)
    (1 / (2 * ((d : ℝ) + 1)))

omit [DecidableEq ι] in
theorem optimizerFloor_pos (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) {θ : ℝ} (hθ : 0 < θ) (hd : 0 < d) : 0 < optimizerFloor H A C θ := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  apply lt_min
  · exact KSOptimizerFloor.inputFloor_pos (matrixBound_pos H).le hθ
  · positivity

omit [DecidableEq ι] in
/-- The capped floor satisfies the trace-one feasibility constraint. -/
theorem optimizerFloor_scaled_le_one (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ) :
    (d : ℝ) * optimizerFloor H A C θ ≤ 1 := by
  have hcap : optimizerFloor H A C θ ≤ 1 / (2 * ((d : ℝ) + 1)) := min_le_right _ _
  have hden : 0 < 2 * ((d : ℝ) + 1) := by positivity
  calc
    (d : ℝ) * optimizerFloor H A C θ ≤ (d : ℝ) * (1 / (2 * ((d : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hcap (Nat.cast_nonneg _)
    _ ≤ 1 := by rw [mul_one_div, div_le_one hden]; nlinarith [Nat.cast_nonneg (α := ℝ) d]

omit [DecidableEq ι] in
theorem optimizerFloor_le_inverse_dimension (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ) (hd : 0 < d) :
    optimizerFloor H A C θ ≤ (d : ℝ)⁻¹ := by
  have hdp : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  rw [← one_div, le_div_iff₀ hdp]
  simpa only [mul_comm] using optimizerFloor_scaled_le_one H A C θ

/-- The physically computed initial density is the maximally mixed matrix. -/
def initialDensity (hd : 0 < d) : selfAdjoint (Matrix (Fin d) (Fin d) ℂ) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact ⟨maximallyMixed, maximallyMixed_posDef.isHermitian⟩

def initialCoordinates (hd : 0 < d) : Coordinates (Fin d) :=
  (chartEquiv (Fin d)).symm (initialDensity hd)

/-- The actual canonical optimizer of the full covariance-Kraus objective. -/
def optimizer (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) (hd : 0 < d) : selfAdjoint (Matrix (Fin d) (Fin d) ℂ) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact hermitianDensityOptimizer H (covarianceKraus A C) θ

def optimizerCoordinates (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) (hd : 0 < d) : Coordinates (Fin d) :=
  (chartEquiv (Fin d)).symm (optimizer H A C θ hd)

omit [DecidableEq ι] in
/-- Maximally mixed initialization belongs to the input-derived physical floor domain. -/
theorem initialDensity_mem_floor (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ) (hd : 0 < d) :
    optimizerFloor H A C θ • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ (initialDensity hd : Matrix _ _ _) ∧
      realTrace (initialDensity hd : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  refine ⟨?_, maximallyMixed_mem_densitySet.2⟩
  change optimizerFloor H A C θ • (1 : Matrix (Fin d) (Fin d) ℂ) ≤
    (Fintype.card (Fin d) : ℝ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ)
  simp only [Fintype.card_fin]
  exact smul_le_smul_of_nonneg_right (optimizerFloor_le_inverse_dimension H A C θ hd) zero_le_one

omit [DecidableEq ι] in
theorem initialCoordinates_mem_floor (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ) (hd : 0 < d) :
    initialCoordinates hd ∈ densityFloor (chart (Fin d)) (optimizerFloor H A C θ) := by
  have he : chart (Fin d) (initialCoordinates hd) = initialDensity hd :=
    (chartEquiv (Fin d)).apply_symm_apply _
  change _ ∧ _
  rw [he]
  exact initialDensity_mem_floor H A C θ hd

/-- Quantitative membership of the actual optimizer follows from the entry budgets. -/
theorem optimizer_mem_floor (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ : ℝ} (hθ : 0 < θ) (hd : 0 < d) :
    optimizerFloor H A C θ • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ (optimizer H A C θ hd : Matrix _ _ _) ∧
      realTrace (optimizer H A C θ hd : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  refine ⟨?_, hermitianDensityOptimizer_trace H (covarianceKraus A C) θ⟩
  have hfloor := KSOptimizerFloor.densityOptimizer_floor H hH (covarianceKraus A C) hθ
    (centerBound_spec H hH).2 (covarianceKraus_budget A hA hC)
  exact (smul_le_smul_of_nonneg_right (min_le_left _ _) zero_le_one).trans hfloor

theorem optimizerCoordinates_mem_floor (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ : ℝ} (hθ : 0 < θ) (hd : 0 < d) :
    optimizerCoordinates H A C θ hd ∈ densityFloor (chart (Fin d)) (optimizerFloor H A C θ) := by
  have he : chart (Fin d) (optimizerCoordinates H A C θ hd) = optimizer H A C θ hd :=
    (chartEquiv (Fin d)).apply_symm_apply _
  change _ ∧ _
  rw [he]
  exact optimizer_mem_floor H hH A hA hC hθ hd

/-- The actual optimizer maximizes the original owner objective on the entire coordinate domain. -/
theorem optimizer_isMaxOn_owner (H : Matrix (Fin d) (Fin d) ℂ) (_hH : H.IsHermitian)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ : ℝ} (hθ : 0 < θ) (hd : 0 < d) :
    IsMaxOn (fun x : Coordinates (Fin d) => ownerObjective H A C θ (chart (Fin d) x))
      (densityFloor (chart (Fin d)) (optimizerFloor H A C θ)) (optimizerCoordinates H A C θ hd) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  intro y hy
  have hyS : (chart (Fin d) y : Matrix (Fin d) (Fin d) ℂ) ∈ densitySet :=
    ⟨(densityFloor_posDef (chart (Fin d)) (optimizerFloor_pos H A C hθ hd) hy).posSemidef, hy.2⟩
  change ownerObjective H A C θ (chart (Fin d) y) ≤
    ownerObjective H A C θ (chart (Fin d) (optimizerCoordinates H A C θ hd))
  rw [ownerObjective_eq_densityObjective H A hA hC, ownerObjective_eq_densityObjective H A hA hC]
  have he : chart (Fin d) (optimizerCoordinates H A C θ hd) = optimizer H A C θ hd :=
    (chartEquiv (Fin d)).apply_symm_apply _
  rw [he]
  exact densityOptimizer_isMaxOn H (covarianceKraus A C) θ _ hyS

/-- The equivalent objective form consumed by the quantitative chart iteration. -/
theorem optimizer_isMaxOn_objective (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ : ℝ} (hθ : 0 < θ) (hd : 0 < d) :
    IsMaxOn (objective H (covarianceKraus A C) θ (chart (Fin d)))
      (densityFloor (chart (Fin d)) (optimizerFloor H A C θ)) (optimizerCoordinates H A C θ hd) := by
  intro y hy
  have h := optimizer_isMaxOn_owner H hH A hA hC hθ hd hy
  simpa only [ownerObjective_eq_densityObjective H A hA hC, objective,
    Function.comp_apply, hermitianDensityObjective] using h

/-- The maximum over the chosen floor domain still equals the original owner potential. -/
theorem ownerPotential_eq_optimizer (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ : ℝ) (hd : 0 < d) :
    ownerPotential H A C θ = ownerObjective H A C θ (optimizer H A C θ hd) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [ownerPotential_eq_densityPotential H A hA hC,
    ownerObjective_eq_densityObjective H A hA hC]
  exact densityPotential_eq_of_maximizer H (covarianceKraus A C) θ
    (densityOptimizer_mem H (covarianceKraus A C) θ) (densityOptimizer_isMaxOn H (covarianceKraus A C) θ)

end MatrixSpencer.KSOwnerOptimizerDomain
