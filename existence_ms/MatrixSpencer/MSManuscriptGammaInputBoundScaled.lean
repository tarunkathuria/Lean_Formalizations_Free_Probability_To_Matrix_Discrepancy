import MatrixSpencer.MSManuscriptAffineJointBoundsScaled
import MatrixSpencer.MSManuscriptOptimizerFloorScaled
import MatrixSpencer.MSManuscriptCovarianceCurvature

/-!
# Input-derived accuracy of the numerical MS covariance-gradient report

The actual finite differences use a uniform second-derivative cap derived
from coefficient floors, unit matrix norms, the bounded center and θ. The
canonical optimizer floor and joint Hessian bound are supplied internally.
No derivative or numerical-accuracy hypothesis remains in the final report.
-/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.MSManuscriptGammaInputBoundScaled
open MSManuscriptGammaDifference MSManuscriptGammaMatrix MSManuscriptGammaSmoothness
variable {k d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance : NormedAddCommGroup (KSFrobeniusTangent.Coordinates (Fin d)) := inferInstance
local instance : NormedSpace ℝ (KSFrobeniusTangent.Coordinates (Fin d)) := inferInstance
set_option maxHeartbeats 1400000

def jointCap (k d : ℕ) (R θ δ L : ℝ) : ℝ :=
  MSManuscriptAffineJointBoundsScaled.jointCap (Fin k) (Fin d) R θ (δ/2)
    (MSManuscriptOptimizerFloorScaled.floor k d R θ L) L

def secondCap (k d : ℕ) (R θ δ L : ℝ) : ℝ :=
  jointCap k d R θ δ L*(1+jointCap k d R θ δ L/(θ/2))

theorem jointCap_nonneg {R θ δ L : ℝ} (hR : 0 ≤ R) (hθ : 0 ≤ θ) :
    0 ≤ jointCap k d R θ δ L := by
  unfold jointCap MSManuscriptAffineJointBoundsScaled.jointCap
  exact mul_nonneg (MSManuscriptComplexValueBoundScaled.valueCap_nonneg hR hθ) (by positivity)

theorem secondCap_nonneg {R θ δ L : ℝ} (hR : 0 ≤ R) (hθ : 0 < θ) :
    0 ≤ secondCap k d R θ δ L := by
  have hb := jointCap_nonneg (k := k) (d := d) (δ := δ) (L := L) hR hθ.le
  unfold secondCap
  positivity

private theorem scalar_mono {a b : ℝ} (h : a ≤ b) :
    a • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ b • 1 := by
  apply Matrix.le_iff.mpr
  rw [← sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr h)

/-- Uniform bound for every unit-vector finite-difference query. -/
theorem query_second_le [Nonempty (Fin d)]
    (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i, (A i).IsHermitian)
    {L : ℝ} (hL : 0 ≤ L) (hAn : ∀i, ‖A i‖ ≤ L) {C : Matrix (Fin k) (Fin k) ℝ}
    {R θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hR : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖ ≤ R)
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C) (hC1 : C ≤ 1)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1) {a : ℝ} (ha : a ∈ Ioo 0 (δ/2)) :
    |iteratedDeriv 2 (curve (H : Matrix (Fin d) (Fin d) ℂ) A C θ u) a| ≤
      secondCap k d R θ δ L := by
  have hC := posDef_of_floor hδ hfloor
  let Cs : selfAdjoint (Matrix (Fin k) (Fin k) ℝ) := ⟨C,hC.isHermitian⟩
  let Ds : selfAdjoint (Matrix (Fin k) (Fin k) ℝ) := -hermitianRankOne (WithLp.ofLp u)
  let path := MSManuscriptAffineJointBounds.covariance Cs Ds
  have he (t : ℝ) : (path t : Matrix (Fin k) (Fin k) ℝ) = C-t • realRankOne (WithLp.ofLp u) := by
    simp [path,MSManuscriptAffineJointBounds.covariance,Cs,Ds,sub_eq_add_neg,hermitianRankOne]
  have hpositive : ∀t ∈ Ioo 0 (δ/2), (path t : Matrix (Fin k) (Fin k) ℝ).PosDef := by
    intro t ht
    rw [he]
    exact query_posDef hfloor ht.1.le (by linarith [ht.2]) u hu
  have hac : a < δ := by linarith [ha.2]
  have hpa := hpositive a ha
  have hpa1 : (path a : Matrix (Fin k) (Fin k) ℝ) ≤ 1 := by
    rw [he]
    exact (sub_le_self C ((realRankOne_posSemidef (WithLp.ofLp u)).smul ha.1.le).nonneg).trans hC1
  have hpg : (δ/2) • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ path a := by
    rw [he]
    exact (scalar_mono (by linarith [ha.2] : δ/2 ≤ δ-a)).trans (query_floor hfloor ha.1.le u hu)
  have hDn : ‖realMatrixEmbedding (Ds : Matrix (Fin k) (Fin k) ℝ)‖ ≤ 1 := by
    have hh := MSManuscriptComplexSourceNorm.real_coefficient_norm_le_one
      (realRankOne_posSemidef (WithLp.ofLp u)) (unit_rank_le_one u hu)
    change ‖realMatrixEmbedding (-realRankOne (WithLp.ofLp u))‖ ≤ 1
    simpa only [map_neg,norm_neg] using hh
  have hR0 := (norm_nonneg (H : Matrix (Fin d) (Fin d) ℂ)).trans hR
  have hd : 0 < d := by simpa only [Fintype.card_fin] using (Fintype.card_pos (α := Fin d))
  let μ := MSManuscriptOptimizerFloorScaled.floor k d R θ L
  have hμ := MSManuscriptOptimizerFloorScaled.floor_pos hd hL hR0 hθ (k := k)
  have hμ1 := MSManuscriptOptimizerFloorScaled.floor_le_one k d R θ L
  let q := KSActualEnvelope.branch A θ (fun _ => H) path a
  have hSq : μ • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ (KSFrobeniusTangent.chart (Fin d) q : Matrix (Fin d) (Fin d) ℂ) := by
    simpa only [Fintype.card_fin] using MSManuscriptOptimizerFloorScaled.branch_floor A hA hL hAn hθ
      (fun _ => H) path a hpa.posSemidef hpa1 hR
  have hSn : ‖(KSFrobeniusTangent.chart (Fin d) q : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1 := by
    rw [KSActualEnvelope.chart_branch]
    exact density_norm_le_one (densityOptimizer_mem _ _ _)
  have hb := MSManuscriptAffineJointBoundsScaled.joint_bounds H A hA hL hAn Cs Ds hDn
    (p := (a,q)) (θ := θ) (R := R) (γ := δ/2) (μ := μ) hθ.le hR0 hR
    (by positivity : 0 < δ/2) (by linarith : δ/2 ≤ 1) hμ hμ1 hpg hpa1 hSq hSn
  have hh := MSManuscriptCovarianceCurvature.potential_second_le A hA hθ (fun _ => H) path
    contDiff_const (MSManuscriptAffineJointBounds.contDiff_covariance Cs Ds) isOpen_Ioo hpositive ha
    (B := jointCap k d R θ δ L) (jointCap_nonneg hR0 hθ.le) hb.1
  simpa only [curve,secondCap,he] using hh

/-- Actual report accuracy from matrix inputs and coefficient floor only. -/
theorem report_accuracy [Nonempty (Fin d)]
    (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i, (A i).IsHermitian)
    {L : ℝ} (hL : 0 ≤ L) (hAn : ∀i, ‖A i‖ ≤ L) {C : Matrix (Fin k) (Fin k) ℝ}
    {R θ δ η : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (hR : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖ ≤ R) (hd : 0 < d)
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C) (hC1 : C ≤ 1) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (observedOwnedGram H A C θ-
      MSManuscriptGammaMatrix.report H A C θ hd δ (secondCap k d R θ δ L) η)‖ ≤ (k : ℝ)*(2*η) := by
  apply report_accuracy_of_floor H A hA hθ hδ
    (secondCap_nonneg ((norm_nonneg _).trans hR) hθ) hη hd hfloor
  intro u hu a ha
  apply query_second_le H A hA hL hAn hθ hδ hδ1 hR hfloor hC1 u hu
  exact ⟨ha.1,(ha.2.trans_le (min_le_left _ _)).trans (by linarith : δ/4 < δ/2)⟩

end MatrixSpencer.MSManuscriptGammaInputBoundScaled
