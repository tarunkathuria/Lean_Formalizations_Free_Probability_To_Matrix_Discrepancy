import MatrixSpencer.MSManuscriptAffineJointBounds
import MatrixSpencer.MSManuscriptComplexValueBoundScaled

/-! Actual affine joint derivative bounds with arbitrary input matrix scale L. -/
open Matrix Set Filter Metric
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.MSManuscriptAffineJointBoundsScaled
open KSFrobeniusTangent MSManuscriptComplexSourceDomain MSManuscriptAffineJointBounds
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
local instance : NormedAddCommGroup (Coordinates n) := inferInstance
local instance : NormedSpace ℝ (Coordinates n) := inferInstance
local instance : NormedAddCommGroup (RealSpace n) := inferInstance
local instance : NormedSpace ℝ (RealSpace n) := inferInstance
set_option maxHeartbeats 1000000

def jointCap (ι n : Type*) [Fintype ι] [Fintype n] (R θ γ μ L : ℝ) : ℝ :=
  MSManuscriptComplexValueBoundScaled.valueCap ι n R θ L*(10/radius γ μ)^4

/-- Actual multilinear derivative bounds, on the original real objective. -/
theorem iterated_bounds (H : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian) {L : ℝ} (hL : 0 ≤ L) (hAnorm : ∀i, ‖A i‖ ≤ L)
    (C D : selfAdjoint (Matrix ι ι ℝ)) (hD : ‖realMatrixEmbedding (D : Matrix ι ι ℝ)‖ ≤ 1)
    {θ R γ μ : ℝ} (hθ : 0 ≤ θ) (hR : 0 ≤ R) (hH : ‖(H : Matrix n n ℂ)‖ ≤ R)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1) {p : RealSpace n}
    (hC : γ • (1 : Matrix ι ι ℝ) ≤ (covariance C D p.1 : Matrix ι ι ℝ))
    (hC1 : (covariance C D p.1 : Matrix ι ι ℝ) ≤ 1)
    (hS : μ • (1 : Matrix n n ℂ) ≤ (chart n p.2 : Matrix n n ℂ))
    (hS1 : ‖(chart n p.2 : Matrix n n ℂ)‖ ≤ 1) :
    ∀ k : ℕ, 2 ≤ k → k ≤ 4 →
      ‖iteratedFDeriv ℝ k (KSActualEnvelope.objective A θ (fun _ => H) (covariance C D)) p‖ ≤
        jointCap ι n R θ γ μ L := by
  have hCp : (covariance C D p.1 : Matrix ι ι ℝ).PosDef := by
    simpa only [add_sub_cancel] using (Matrix.PosDef.one.smul hγ).add_posSemidef (Matrix.le_iff.mp hC)
  have hSp : (chart n p.2 : Matrix n n ℂ).PosDef := by
    simpa only [add_sub_cancel] using (Matrix.PosDef.one.smul hμ).add_posSemidef (Matrix.le_iff.mp hS)
  have hcont := MSManuscriptComplexObjective.contDiffOn_objective (H : Matrix n n ℂ) A hA θ
    hγ hγ1 hμ hμ1 hC hS
  have hb := MSManuscriptComplexValueBoundScaled.objective_norm_le_on_ball (H : Matrix n n ℂ) A hA hL hAnorm
    hθ hR hH hγ hγ1 hμ hμ1 hC hC1 hS hS1
  rw [← base_add_jointEmbedding C D p] at hcont hb
  have hh := chart_derivatives_le_common_cap
    (MSManuscriptComplexObjective.objective (H : Matrix n n ℂ) A θ) C D hD
    (radius_pos hγ hμ) (MSManuscriptComplexValueBoundScaled.radius_le_one hγ hγ1 hμ hμ1)
    (MSManuscriptComplexValueBoundScaled.valueCap_nonneg (ι := ι) (n := n) hR hθ) hcont hb
  have he := eventuallyEq_objective H A hA θ C D hCp hSp
  intro k hk2 hk4
  rw [← (he.iteratedFDeriv ℝ k).self_of_nhds]
  exact hh k hk2 hk4

/-- The nested Fréchet derivative norms consumed by the actual optimizer
response and fourth-order envelope theorems. Every bound is discharged. -/
theorem joint_bounds (H : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian) {L : ℝ} (hL : 0 ≤ L) (hAnorm : ∀i, ‖A i‖ ≤ L)
    (C D : selfAdjoint (Matrix ι ι ℝ)) (hD : ‖realMatrixEmbedding (D : Matrix ι ι ℝ)‖ ≤ 1)
    {θ R γ μ : ℝ} (hθ : 0 ≤ θ) (hR : 0 ≤ R) (hH : ‖(H : Matrix n n ℂ)‖ ≤ R)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1) {p : RealSpace n}
    (hC : γ • (1 : Matrix ι ι ℝ) ≤ (covariance C D p.1 : Matrix ι ι ℝ))
    (hC1 : (covariance C D p.1 : Matrix ι ι ℝ) ≤ 1)
    (hS : μ • (1 : Matrix n n ℂ) ≤ (chart n p.2 : Matrix n n ℂ))
    (hS1 : ‖(chart n p.2 : Matrix n n ℂ)‖ ≤ 1) :
    let F := KSActualEnvelope.objective A θ (fun _ => H) (covariance C D)
    KSActualEnvelope.secondNorm F p ≤ jointCap ι n R θ γ μ L ∧
    KSActualEnvelope.thirdNorm F p ≤ jointCap ι n R θ γ μ L ∧
    KSActualEnvelope.fourthNorm F p ≤ jointCap ι n R θ γ μ L := by
  have hb := iterated_bounds H A hA hL hAnorm C D hD hθ hR hH hγ hγ1 hμ hμ1 hC hC1 hS hS1
  exact nested_bounds hb

end MatrixSpencer.MSManuscriptAffineJointBoundsScaled
