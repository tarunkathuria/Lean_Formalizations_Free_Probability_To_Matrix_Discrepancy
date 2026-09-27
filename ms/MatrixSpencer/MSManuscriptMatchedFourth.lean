import MatrixSpencer.MSManuscriptMatchedJointBounds
import MatrixSpencer.MSManuscriptOptimizerFloorScaled

/-!
# Input-derived fourth derivative for actual matched covariance withdrawal

Every density floor, source domain, objective derivative bound, and optimizer
response is discharged. The remaining interval hypotheses are primitive bounds
on the actual matrices H+tB and C−t²Q; no derivative, Taylor, or optimizer
certificate is assumed. All matrix norms are Euclidean operator norms.
-/
open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.MSManuscriptMatchedFourth
open KSFrobeniusTangent KSActualEnvelope MSManuscriptMatchedJointBounds
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
set_option maxHeartbeats 1000000
local instance : NormedAddCommGroup (Coordinates n) := inferInstance
local instance : NormedSpace ℝ (Coordinates n) := inferInstance
local instance : NormedAddCommGroup (ℝ × Coordinates n) := inferInstance
local instance : NormedSpace ℝ (ℝ × Coordinates n) := inferInstance
local instance : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance : NormedAddCommGroup (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance

def densityFloor (ι n : Type*) [Fintype ι] [Fintype n] (R θ L : ℝ) : ℝ :=
  MSManuscriptOptimizerFloorScaled.floor (Fintype.card ι) (Fintype.card n) R θ L

def jointBudget (ι n : Type*) [Fintype ι] [Fintype n] (R b θ γ L : ℝ) : ℝ :=
  jointCap ι n R b θ γ (densityFloor ι n R θ L) L

def fourthBudget (ι n : Type*) [Fintype ι] [Fintype n] (R b θ γ L : ℝ) : ℝ :=
  let B := jointBudget ι n R b θ γ L
  (B+3*B^2/(θ/2))*(1+B/(θ/2))^4

theorem jointBudget_nonneg {R b θ γ L : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b) (hθ : 0 ≤ θ) :
    0 ≤ jointBudget ι n R b θ γ L := by
  have hv := MSManuscriptComplexValueBoundScaled.valueCap_nonneg (ι := ι) (n := n) (L := L) (add_nonneg hR hb) hθ
  unfold jointBudget jointCap
  positivity

theorem fourthBudget_nonneg {R b θ γ L : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b) (hθ : 0 < θ) :
    0 ≤ fourthBudget ι n R b θ γ L := by
  have hB := jointBudget_nonneg (ι := ι) (n := n) (γ := γ) (L := L) hR hb hθ.le
  unfold fourthBudget
  positivity

theorem covariance_posDef {C Q : selfAdjoint (Matrix ι ι ℝ)} {γ t : ℝ}
    (hγ : 0 < γ) (hC : γ•(1 : Matrix ι ι ℝ) ≤ (covariance C Q t : Matrix ι ι ℝ)) :
    (covariance C Q t : Matrix ι ι ℝ).PosDef := by
  simpa only [add_sub_cancel] using (Matrix.PosDef.one.smul hγ).add_posSemidef (Matrix.le_iff.mp hC)

/-- Smoothness of the actual optimized potential, from positivity on the
stated interval and the already-proved canonical optimizer response. -/
theorem potential_contDiffOn (H B : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    (C Q : selfAdjoint (Matrix ι ι ℝ)) {θ γ : ℝ} (hθ : 0 < θ) (hγ : 0 < γ)
    {I : Set ℝ} (hC : ∀t∈I, γ•(1 : Matrix ι ι ℝ) ≤ (covariance C Q t : Matrix ι ι ℝ)) :
    ContDiffOn ℝ ∞ (fun t => ownerPotential (center H B t) A (covariance C Q t) θ) I := by
  intro t ht
  exact ((contDiffAt_jointHermitianOwnerPotential A hA hθ (center H B t) (covariance C Q t)
    (covariance_posDef hγ (hC t ht))).comp t
    ((contDiff_center H B).contDiffAt.prodMk (contDiff_covariance C Q).contDiffAt)).contDiffWithinAt


theorem potential_fourth_le (H B : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian) {L : ℝ}
    (hL : 0 ≤ L) (hAnorm : ∀i, ‖A i‖ ≤ L)
    (C Q : selfAdjoint (Matrix ι ι ℝ)) (hQ : ‖realMatrixEmbedding (Q : Matrix ι ι ℝ)‖ ≤ 1)
    {θ R b γ : ℝ} (hθ : 0 < θ) (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hB : ‖(B : Matrix n n ℂ)‖ ≤ b) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {I : Set ℝ} (hI : IsOpen I)
    (hC : ∀t∈I, γ•(1 : Matrix ι ι ℝ) ≤ (covariance C Q t : Matrix ι ι ℝ))
    (hC1 : ∀t∈I, (covariance C Q t : Matrix ι ι ℝ) ≤ 1)
    (hcenter : ∀t∈I, ‖(center H B t : Matrix n n ℂ)‖ ≤ R)
    (htime : ∀t∈I, |t| ≤ 1) {t : ℝ} (ht : t∈I) :
    |iteratedDeriv 4 (fun z => ownerPotential (center H B z) A (covariance C Q z) θ) t| ≤
      fourthBudget ι n R b θ γ L := by
  have hμ : 0 < densityFloor ι n R θ L :=
    MSManuscriptOptimizerFloorScaled.floor_pos Fintype.card_pos hL hR hθ
  have hμ1 : densityFloor ι n R θ L ≤ 1 := MSManuscriptOptimizerFloorScaled.floor_le_one _ _ _ _ _
  have hpositive : ∀z∈I, (covariance C Q z : Matrix ι ι ℝ).PosDef :=
    fun z hz => covariance_posDef hγ (hC z hz)
  have hfloor := MSManuscriptOptimizerFloorScaled.branch_floor A hA hL hAnorm hθ
    (center H B) (covariance C Q) t (hpositive t ht).posSemidef (hC1 t ht) (hcenter t ht)
  have hSnorm : ‖(chart n (branch A θ (center H B) (covariance C Q) t) : Matrix n n ℂ)‖ ≤ 1 := by
    rw [chart_branch]
    exact density_norm_le_one ⟨(hermitianDensityOptimizer_posDef _ _ hθ).posSemidef,
      hermitianDensityOptimizer_trace _ _ θ⟩
  have hj := joint_bounds
    (p := (t,branch A θ (center H B) (covariance C Q) t))
    (γ := γ) (μ := densityFloor ι n R θ L) (R := R) (b := b) (L := L)
    H B A hA hL hAnorm C Q hQ hθ.le hR hb hB hγ hγ1 hμ hμ1
    (htime t ht) (hcenter t ht) (hC t ht) (hC1 t ht) hfloor hSnorm
  exact KSActualEnvelope.potential_fourth_le (B := jointBudget ι n R b θ γ L) A hA hθ (center H B) (covariance C Q)
    (contDiff_center H B) (contDiff_covariance C Q) hI hpositive ht
    (jointBudget_nonneg hR hb hθ.le) hj.1 hj.2.1 hj.2.2

end MatrixSpencer.MSManuscriptMatchedFourth
