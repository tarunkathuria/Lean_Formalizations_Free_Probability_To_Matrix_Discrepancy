import MatrixSpencer.CovarianceCalculus
import MatrixSpencer.CovariancePreparation

/-!
# Compact coefficient charts with a positive spectral floor

These are compact subsets of the actual real self-adjoint coefficient space.
Physical center and direction balls use Euclidean matrix operator norms.
Compactness alone is asserted; no differentiability of an optimizer is assumed.
-/

open Matrix Set
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace MatrixSpencer
namespace CovarianceCompactChart

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

local instance compactChartCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance compactChartCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) :=
  inferInstance
local instance compactChartPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstance
local instance compactChartCoeffFinite : FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℝ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℝ)))
local instance compactChartPhysicalFinite : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

/-- Arbitrary upper owner, with a scalar lower spectral floor. -/
def coefficientChart (a : ℝ) (upper : Matrix ι ι ℝ) : Set (selfAdjoint (Matrix ι ι ℝ)) :=
  {C | a • (1 : Matrix ι ι ℝ) ≤ (C : Matrix ι ι ℝ) ∧ (C : Matrix ι ι ℝ) ≤ upper}

lemma isClosed_coefficientChart (a : ℝ) (upper : Matrix ι ι ℝ) :
    IsClosed (coefficientChart a upper) := by
  have hlo : IsClosed {C : selfAdjoint (Matrix ι ι ℝ) |
      ((C : Matrix ι ι ℝ) - a • (1 : Matrix ι ι ℝ)).PosSemidef} :=
    isClosed_posSemidef_real.preimage
      ((realHermitianInclusion (ι := ι)).continuous.sub continuous_const)
  have hhi : IsClosed {C : selfAdjoint (Matrix ι ι ℝ) |
      (upper - (C : Matrix ι ι ℝ)).PosSemidef} :=
    isClosed_posSemidef_real.preimage
      (continuous_const.sub (realHermitianInclusion (ι := ι)).continuous)
  simpa only [coefficientChart, Matrix.le_iff, Set.setOf_and] using hlo.inter hhi

/-- Pull back the compact positive interval through the closed self-adjoint inclusion. -/
lemma isCompact_nonnegative_interval (upper : Matrix ι ι ℝ) :
    IsCompact {C : selfAdjoint (Matrix ι ι ℝ) |
      (0 : Matrix ι ι ℝ) ≤ (C : Matrix ι ι ℝ) ∧ (C : Matrix ι ι ℝ) ≤ upper} := by
  have hc : IsClosed {A : Matrix ι ι ℝ | IsSelfAdjoint A} :=
    isClosed_eq continuous_star continuous_id
  exact hc.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_covarianceInterval upper)

lemma isCompact_coefficientChart {a : ℝ} (ha : 0 ≤ a) (upper : Matrix ι ι ℝ) :
    IsCompact (coefficientChart a upper) := by
  apply (isCompact_nonnegative_interval upper).of_isClosed_subset
    (isClosed_coefficientChart a upper)
  intro C hC
  exact ⟨((Matrix.PosSemidef.one.smul ha).nonneg).trans hC.1, hC.2⟩

/-- A strict scalar floor implies actual positive definiteness, also in dimension zero. -/
lemma posDef_of_scalar_floor {a : ℝ} (ha : 0 < a) {C : Matrix ι ι ℝ}
    (hC : a • (1 : Matrix ι ι ℝ) ≤ C) : C.PosDef := by
  have hp := (Matrix.PosDef.one.smul ha).add_posSemidef (Matrix.le_iff.mp hC)
  simpa only [add_sub_cancel] using hp

lemma coefficientChart_posDef {a : ℝ} (ha : 0 < a) {upper : Matrix ι ι ℝ}
    {C : selfAdjoint (Matrix ι ι ℝ)} (hC : C ∈ coefficientChart a upper) :
    (C : Matrix ι ι ℝ).PosDef := posDef_of_scalar_floor ha hC.1

/-- The coefficient chart used in a fixed-support epoch. -/
lemma isCompact_unit_coefficientChart {a : ℝ} (ha : 0 ≤ a) :
    IsCompact {C : selfAdjoint (Matrix ι ι ℝ) |
      a • (1 : Matrix ι ι ℝ) ≤ (C : Matrix ι ι ℝ) ∧ (C : Matrix ι ι ℝ) ≤ 1} :=
  isCompact_coefficientChart ha 1

lemma unit_coefficientChart_posDef {a : ℝ} (ha : 0 < a)
    {C : selfAdjoint (Matrix ι ι ℝ)}
    (hC : a • (1 : Matrix ι ι ℝ) ≤ (C : Matrix ι ι ℝ) ∧ (C : Matrix ι ι ℝ) ≤ 1) :
    (C : Matrix ι ι ℝ).PosDef := posDef_of_scalar_floor ha hC.1

/-- Bounded physical center paired with the coefficient chart. -/
def stateChart (R a : ℝ) (upper : Matrix ι ι ℝ) :
    Set (selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) :=
  Metric.closedBall 0 R ×ˢ coefficientChart a upper

lemma isCompact_stateChart (R : ℝ) {a : ℝ} (ha : 0 ≤ a) (upper : Matrix ι ι ℝ) :
    IsCompact (stateChart (n := n) R a upper) :=
  (isCompact_closedBall _ _).prod (isCompact_coefficientChart ha upper)

lemma mem_stateChart_iff (R a : ℝ) (upper : Matrix ι ι ℝ)
    (p : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) :
    p ∈ stateChart R a upper ↔ ‖p.1‖ ≤ R ∧ p.2 ∈ coefficientChart a upper := by
  simp only [stateChart, Set.mem_prod, Metric.mem_closedBall, dist_zero_right]

lemma stateChart_posDef {R a : ℝ} (ha : 0 < a) {upper : Matrix ι ι ℝ}
    {p : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)}
    (hp : p ∈ stateChart R a upper) : (p.2 : Matrix ι ι ℝ).PosDef :=
  coefficientChart_posDef ha hp.2

/-- Compact parameters grouped as `(state, (physical direction, covariance direction))`. -/
def parameterChart (R a V Q : ℝ) (upper : Matrix ι ι ℝ) :
    Set ((selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) ×
      (selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ))) :=
  stateChart R a upper ×ˢ (Metric.closedBall 0 V ×ˢ Metric.closedBall 0 Q)

lemma isCompact_parameterChart (R V Q : ℝ) {a : ℝ} (ha : 0 ≤ a)
    (upper : Matrix ι ι ℝ) : IsCompact (parameterChart (n := n) R a V Q upper) :=
  (isCompact_stateChart (n := n) R ha upper).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))

lemma parameterChart_posDef {R a V Q : ℝ} (ha : 0 < a) {upper : Matrix ι ι ℝ}
    {p : (selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) ×
      (selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ))}
    (hp : p ∈ parameterChart R a V Q upper) : (p.1.2 : Matrix ι ι ℝ).PosDef :=
  stateChart_posDef ha hp.1

/-- Arbitrary compact direction sets can replace balls without selecting eigenvectors continuously. -/
lemma isCompact_parameters_of_directions (R : ℝ) {a : ℝ} (ha : 0 ≤ a)
    (upper : Matrix ι ι ℝ) {K : Set (selfAdjoint (Matrix n n ℂ))}
    {L : Set (selfAdjoint (Matrix ι ι ℝ))} (hK : IsCompact K) (hL : IsCompact L) :
    IsCompact (stateChart (n := n) R a upper ×ˢ (K ×ˢ L)) :=
  (isCompact_stateChart (n := n) R ha upper).prod (hK.prod hL)

end CovarianceCompactChart
end MatrixSpencer
