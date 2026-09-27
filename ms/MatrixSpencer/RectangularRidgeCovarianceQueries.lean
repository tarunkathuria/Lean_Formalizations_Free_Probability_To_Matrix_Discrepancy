import MatrixSpencer.RectangularRidgeCovarianceCurvature
import MatrixSpencer.RectangularRidgeOwnerShavingDerivative
import MatrixSpencer.MSManuscriptGammaSmoothness

/-! Actual covariance-query curvature from coefficient and optimizer floors.
The optimizer in the floor hypothesis is the optimizer of the same mixed SDP;
primitive tuning supplies that matrix inequality separately. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeCovarianceQueries
open MSManuscriptGammaSmoothness
variable {k d : ℕ}
local instance ridgeCovQueryCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeCovQueryPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
local instance ridgeCovQueryCoordGroup : NormedAddCommGroup (KSFrobeniusTangent.Coordinates (Fin d)) := inferInstance
local instance ridgeCovQueryCoordSpace : NormedSpace ℝ (KSFrobeniusTangent.Coordinates (Fin d)) := inferInstance
attribute [local irreducible] RectangularRidgePotential.optimizer
set_option maxHeartbeats 300000

def jointCap (k d : ℕ) (R δ μ L : ℝ) : ℝ :=
  MSManuscriptAffineJointBoundsScaled.jointCap (Fin k) (Fin d) R 0 (δ/2) μ L

def secondCap (k d : ℕ) (R κ δ μ L : ℝ) : ℝ :=
  jointCap k d R δ μ L*(1+jointCap k d R δ μ L/(κ/2))

theorem jointCap_nonneg {R δ μ L : ℝ} (hR : 0 ≤ R) :
    0 ≤ jointCap k d R δ μ L := by
  unfold jointCap MSManuscriptAffineJointBoundsScaled.jointCap
  exact mul_nonneg (MSManuscriptComplexValueBoundScaled.valueCap_nonneg hR (by norm_num)) (by positivity)

theorem secondCap_nonneg {R κ δ μ L : ℝ} (hR : 0 ≤ R) (hκ : 0 < κ) :
    0 ≤ secondCap k d R κ δ μ L := by
  have hb := jointCap_nonneg (k := k) (d := d) (δ := δ) (μ := μ) (L := L) hR
  unfold secondCap
  positivity

def curve (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix (Fin k) (Fin k) ℝ) (m : ℕ) (θ κ : ℝ)
    (u : EuclideanSpace ℝ (Fin k)) (a : ℝ) : ℝ :=
  RectangularRidgeCovarianceCalculus.ownerPotential m H A
    (C-a • realRankOne (WithLp.ofLp u)) θ κ

theorem curve_contDiffAt [Nonempty (Fin d)]
    (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix (Fin k) (Fin k) ℝ}
    (hC : C.IsHermitian) (m : ℕ) (hm : 1 ≤ m) {θ κ a : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (u : EuclideanSpace ℝ (Fin k)) (hCa : (C-a • realRankOne (WithLp.ofLp u)).PosDef) :
    ContDiffAt ℝ ∞ (curve H A C m θ κ u) a := by
  let Cs : selfAdjoint (Matrix (Fin k) (Fin k) ℝ) := ⟨C,hC⟩
  let R := hermitianRankOne (WithLp.ofLp u)
  have hpath : ContDiff ℝ ∞ (fun t : ℝ => Cs-t • R) := contDiff_const.sub (contDiff_id.smul contDiff_const)
  have hp := contDiffAt_hermitianRidgeOwnerPotential H A hA m hm θ κ hθ hκ (Cs-a • R) hCa
  exact ContDiffAt.comp (g := hermitianRidgeOwnerPotential H A m θ κ)
    (f := fun t : ℝ => Cs-t • R) a hp hpath.contDiffAt

theorem query_contDiffOn [Nonempty (Fin d)]
    (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix (Fin k) (Fin k) ℝ}
    (m : ℕ) (hm : 1 ≤ m) {θ κ δ s : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) (hδ : 0 < δ)
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C) (hsδ : s < δ)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1) :
    ContDiffOn ℝ 2 (curve H A C m θ κ u) (Icc 0 s) := by
  intro a ha
  exact ((curve_contDiffAt H A hA (posDef_of_floor hδ hfloor).isHermitian m hm hθ hκ u
    (query_posDef hfloor ha.1 (ha.2.trans_lt hsδ) u hu)).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).contDiffWithinAt


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
    (m : ℕ) (hm : 1 ≤ m) {R θ κ δ μ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hR : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖ ≤ R)
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C) (hC1 : C ≤ 1)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1) {a : ℝ} (ha : a ∈ Ioo 0 (δ/2))
    (hoptimizer : μ • (1 : Matrix (Fin d) (Fin d) ℂ) ≤
      RectangularRidgePotential.optimizer (H : Matrix (Fin d) (Fin d) ℂ)
        (covarianceKraus A (C-a • realRankOne (WithLp.ofLp u))) m θ κ) :
    |iteratedDeriv 2 (curve (H : Matrix (Fin d) (Fin d) ℂ) A C m θ κ u) a| ≤
      secondCap k d R κ δ μ L := by
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
  let q := RectangularRidgeCovarianceEnvelope.branch A m θ κ H path a
  have hSq : μ • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ (KSFrobeniusTangent.chart (Fin d) q : Matrix (Fin d) (Fin d) ℂ) := by
    rw [RectangularRidgeCovarianceEnvelope.chart_branch]
    change μ • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ RectangularRidgePotential.optimizer
      (H : Matrix (Fin d) (Fin d) ℂ) (covarianceKraus A (path a)) m θ κ
    rw [he]
    exact hoptimizer
  have hSn : ‖(KSFrobeniusTangent.chart (Fin d) q : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1 := by
    rw [RectangularRidgeCovarianceEnvelope.chart_branch]
    exact density_norm_le_one (RectangularRidgePotential.optimizer_mem _ _ m θ κ)
  have hb := MSManuscriptAffineJointBoundsScaled.joint_bounds H A hA hL hAn Cs Ds hDn
    (p := (a,q)) (θ := 0) (R := R) (γ := δ/2) (μ := μ) (by norm_num) hR0 hR
    (by positivity : 0 < δ/2) (by linarith : δ/2 ≤ 1) hμ hμ1 hpg hpa1 hSq hSn
  have hh := RectangularRidgeCovarianceCurvature.potential_second_le_source A hA m hm hθ hκ H path (MSManuscriptAffineJointBounds.contDiff_covariance Cs Ds) isOpen_Ioo hpositive ha
    (B := jointCap k d R δ μ L) (jointCap_nonneg hR0) hb.1
  simpa only [curve,secondCap,he] using hh


end MatrixSpencer.RectangularRidgeCovarianceQueries
