import MatrixSpencer.RectangularRidgeActualEnvelope
import MatrixSpencer.RectangularRidgeMixedRegularizerNorms
import MatrixSpencer.MSManuscriptMatchedJointBounds

/-! Actual mixed joint derivatives along H+tB and C-t²Q. The source Cauchy
bounds and the actual dyadic-plus-ridge derivative bounds are added at the
same density, including singular physical sources. -/
open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.RectangularRidgeMatchedJointBounds
open KSFrobeniusTangent
open MSManuscriptMatchedJointBounds (center covariance contDiff_center contDiff_covariance)
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance ridgeMatchedJointCStar {j : Type*} [Fintype j] [DecidableEq j] : CStarAlgebra (Matrix j j ℂ) := {}
local instance ridgeMatchedJointPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeMatchedJointCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance ridgeMatchedJointCoordGroup : NormedAddCommGroup (Coordinates n) := inferInstance
local instance ridgeMatchedJointCoordSpace : NormedSpace ℝ (Coordinates n) := inferInstance
local instance ridgeMatchedJointJointGroup : NormedAddCommGroup (ℝ × Coordinates n) := inferInstance
local instance ridgeMatchedJointJointSpace : NormedSpace ℝ (ℝ × Coordinates n) := inferInstance
local instance ridgeMatchedJointMap2Group {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance ridgeMatchedJointMap2Space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance ridgeMatchedJointMap3Group {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance ridgeMatchedJointMap3Space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance ridgeMatchedJointMap4Group {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance ridgeMatchedJointMap4Space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
set_option maxHeartbeats 300000

omit [DecidableEq ι] in
/-- Exact decomposition in joint physical Frobenius coordinates. -/
theorem objective_eq_source_add (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ)
    (H : ℝ → selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ)) :
    RectangularRidgeActualEnvelope.objective A m θ κ H C = fun p =>
      KSActualEnvelope.objective A 0 H C p +
        RectangularRidgeMixedRegularizerJets.regularizer m θ κ (chart n p.2) := by
  funext p
  unfold RectangularRidgeActualEnvelope.objective RectangularRidgeCovarianceCalculus.ownerObjective
    RectangularRidgeCovarianceCalculus.regularizer regularizedOwnerObjective
    KSActualEnvelope.objective MatrixSpencer.ownerObjective
    RectangularRidgeMixedRegularizerJets.regularizer dyadicTsallisPotential tsallisPotential traceSqrt
  ring

def jointCap (ι n : Type*) [Fintype ι] [Fintype n] (m : ℕ) (R b θ κ γ μ L : ℝ) : ℝ :=
  MSManuscriptMatchedJointBounds.jointCap ι n R b 0 γ μ L +
    RectangularRidgeMixedRegularizerNorms.budget (n := n) m θ κ μ

/-- The actual mixed second-through-fourth joint derivative norms. -/
theorem joint_bounds (H B : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian) {L : ℝ}
    (hL : 0 ≤ L) (hAnorm : ∀i, ‖A i‖ ≤ L)
    (C Q : selfAdjoint (Matrix ι ι ℝ)) (hQ : ‖realMatrixEmbedding (Q : Matrix ι ι ℝ)‖ ≤ 1)
    (m : ℕ) (hm : 1 ≤ m) {θ κ R b γ μ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ)
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hB : ‖(B : Matrix n n ℂ)‖ ≤ b)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1) {p : ℝ × Coordinates n}
    (ht : |p.1| ≤ 1) (hH : ‖(center H B p.1 : Matrix n n ℂ)‖ ≤ R)
    (hC : γ•(1 : Matrix ι ι ℝ) ≤ (covariance C Q p.1 : Matrix ι ι ℝ))
    (hC1 : (covariance C Q p.1 : Matrix ι ι ℝ) ≤ 1)
    (hS : μ•(1 : Matrix n n ℂ) ≤ (chart n p.2 : Matrix n n ℂ))
    (hS1 : ‖(chart n p.2 : Matrix n n ℂ)‖ ≤ 1) :
    let F := RectangularRidgeActualEnvelope.objective A m θ κ (center H B) (covariance C Q)
    KSActualEnvelope.secondNorm F p ≤ jointCap ι n m R b θ κ γ μ L ∧
    KSActualEnvelope.thirdNorm F p ≤ jointCap ι n m R b θ κ γ μ L ∧
    KSActualEnvelope.fourthNorm F p ≤ jointCap ι n m R b θ κ γ μ L := by
  have hCp : (covariance C Q p.1 : Matrix ι ι ℝ).PosDef := by
    simpa only [add_sub_cancel] using (Matrix.PosDef.one.smul hγ).add_posSemidef (Matrix.le_iff.mp hC)
  have hSp : (chart n p.2 : Matrix n n ℂ).PosDef := by
    simpa only [add_sub_cancel] using (Matrix.PosDef.one.smul hμ).add_posSemidef (Matrix.le_iff.mp hS)
  have hSle : (chart n p.2 : Matrix n n ℂ) ≤ 1 := by
    have hh := (CStarAlgebra.norm_le_iff_le_algebraMap _ zero_le_one hSp.posSemidef.nonneg).mp hS1
    simpa only [map_one] using hh
  let G := KSActualEnvelope.objective A 0 (center H B) (covariance C Q)
  let T := fun y : ℝ × Coordinates n => RectangularRidgeMixedRegularizerJets.regularizer m θ κ (chart n y.2)
  have hg : ContDiffAt ℝ ∞ G p := KSActualEnvelope.objective_contDiffAt A hA
    (center H B) (covariance C Q) (contDiff_center H B) (contDiff_covariance C Q) hCp hSp
  have htr : ContDiffAt ℝ ∞ T p :=
    ContDiffAt.comp (g := RectangularRidgeMixedRegularizerJets.regularizer m θ κ)
      (f := fun y : ℝ × Coordinates n => chart n y.2) p
      (RectangularRidgeMixedRegularizerJets.contDiffAt_regularizer m θ κ (chart n p.2) hSp)
      ((contDiff_chart n).contDiffAt.comp p contDiffAt_snd)
  have hsrc := MSManuscriptMatchedJointBounds.iterated_bounds H B A hA hL hAnorm C Q hQ
    (θ := 0) (by norm_num) hR hb hB hγ hγ1 hμ hμ1 ht hH hC hC1 hS hS1
  have hreg := RectangularRidgeMixedRegularizerNorms.joint_chart_norm_bounds m hm hθ hκ p hSp hSle hμ hμ1 hS
  have hregI : ∀ r : ℕ, 2 ≤ r → r ≤ 4 →
      ‖iteratedFDeriv ℝ r T p‖ ≤ RectangularRidgeMixedRegularizerNorms.budget (n := n) m θ κ μ := by
    intro r hr2 hr4
    interval_cases r
    · rw [← norm_iteratedFDeriv_fderiv (n := 1), ← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero]
      exact hreg.1
    · rw [← norm_iteratedFDeriv_fderiv (n := 2), ← norm_iteratedFDeriv_fderiv (n := 1),
        ← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero]
      exact hreg.2.1
    · rw [← norm_iteratedFDeriv_fderiv (n := 3), ← norm_iteratedFDeriv_fderiv (n := 2),
        ← norm_iteratedFDeriv_fderiv (n := 1), ← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero]
      exact hreg.2.2
  apply MSManuscriptAffineJointBounds.nested_bounds
  intro r hr2 hr4
  rw [objective_eq_source_add]
  rw [iteratedFDeriv_add_apply' (hg.of_le (WithTop.coe_le_coe.mpr le_top))
    (htr.of_le (WithTop.coe_le_coe.mpr le_top))]
  exact (norm_add_le _ _).trans (add_le_add (hsrc r hr2 hr4) (hregI r hr2 hr4))

end MatrixSpencer.RectangularRidgeMatchedJointBounds
