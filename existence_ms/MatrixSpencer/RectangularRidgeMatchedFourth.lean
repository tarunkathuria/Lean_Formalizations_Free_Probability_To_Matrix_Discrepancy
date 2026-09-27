import MatrixSpencer.RectangularRidgeMatchedJointBounds
import MatrixSpencer.RectangularRidgeMatchedBudget
import MatrixSpencer.RectangularRidgePrimitiveMagnitude
import MatrixSpencer.RectangularRidgeOffCenterFloor
import MatrixSpencer.MSManuscriptFrameFamily

/-!
# Polynomial fourth derivative of the actual mixed matched path

The inputs are the original Hermitian contractions, a stored coefficient
isometry, and bounds on the real matrices H+tB and C-t²Q. The density floor,
all source and mixed-regularizer derivatives, and the optimizer branch are
proved internally. Physical sources and the lifted coefficient owner may be
singular. No derivative, optimizer, or response certificate is assumed.
-/
open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.RectangularRidgeMatchedFourth
open KSFrobeniusTangent
open RectangularRidgePrimitiveParameters RectangularRidgeNumericalOptimizerFloor
open MSManuscriptMatchedJointBounds (center covariance contDiff_center contDiff_covariance)
variable {N k d : ℕ} [Nonempty (Fin d)]
local instance ridgeMatchedFourthCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeMatchedFourthPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
local instance ridgeMatchedFourthCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin k) (Fin k) ℝ)) := inferInstance
local instance ridgeMatchedFourthCoordGroup : NormedAddCommGroup (Coordinates (Fin d)) := inferInstance
local instance ridgeMatchedFourthCoordSpace : NormedSpace ℝ (Coordinates (Fin d)) := inferInstance
local instance ridgeMatchedFourthJointGroup : NormedAddCommGroup (ℝ × Coordinates (Fin d)) := inferInstance
local instance ridgeMatchedFourthJointSpace : NormedSpace ℝ (ℝ × Coordinates (Fin d)) := inferInstance
attribute [local irreducible] RectangularRidgePotential.optimizer
set_option maxHeartbeats 300000

/-- The primitive-tuned actual matched potential has the explicit polynomial
fourth-derivative cap used by the numerical walk. -/
theorem potential_fourth_le (H B : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (U : Matrix (Fin N) (Fin k) ℝ) (hU : Uᵀ*U=1)
    (hN : 1 ≤ N) (hND : N ≤ d) (hkN : k ≤ N)
    (C Q : selfAdjoint (Matrix (Fin k) (Fin k) ℝ))
    (hQ : ‖realMatrixEmbedding (Q : Matrix (Fin k) (Fin k) ℝ)‖ ≤ 1)
    (hB : ‖(B : Matrix (Fin d) (Fin d) ℂ)‖ ≤ (size d N)^2)
    {γ : ℝ} (hγlow : ((2:ℝ)^15)⁻¹ ≤ γ) (hγ1 : γ ≤ 1)
    {I : Set ℝ} (hI : IsOpen I)
    (hC : ∀ t∈I, γ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ (covariance C Q t : Matrix (Fin k) (Fin k) ℝ))
    (hC1 : ∀ t∈I, (covariance C Q t : Matrix (Fin k) (Fin k) ℝ) ≤ 1)
    (hphysical : ∀ t∈I, covarianceLift U (covariance C Q t) ≤ 1)
    (hcenter : ∀ t∈I, ‖(center H B t : Matrix (Fin d) (Fin d) ℂ)‖ ≤ (N : ℝ)+1)
    (htime : ∀ t∈I, |t| ≤ 1) {t : ℝ} (ht : t∈I) :
    |iteratedDeriv 4 (fun z => RectangularRidgeCovarianceCalculus.ownerPotential
      (RectangularRidgeTuning.depth N d hN) (center H B z) (mixFamily A U)
      (covariance C Q z) (weight N d hN) (1/(d : ℝ))) t| ≤
      RectangularRidgeNumericalParameters.fourthCap (size d N) := by
  let P := size d N
  let μ := RectangularRidgeNumericalParameters.densityFloor P
  let m := RectangularRidgeTuning.depth N d hN
  let θ := weight N d hN
  let κ : ℝ := 1/(d : ℝ)
  let J := RectangularRidgeMatchedBudget.commonJointCap P
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hP : 1 ≤ P := by dsimp [P,size]; linarith
  have hPN : (N : ℝ) ≤ P := by dsimp [P,size]; linarith
  have hPd : (d : ℝ) ≤ P := by dsimp [P,size]; linarith
  have hPk : (k : ℝ) ≤ P := (Nat.cast_le.mpr hkN).trans hPN
  have hR : (N : ℝ)+1 ≤ P^2 := by
    have hp : (N : ℝ)+1 ≤ P := by dsimp [P,size]; linarith
    nlinarith
  have hγ : 0 < γ := lt_of_lt_of_le (by positivity) hγlow
  have hμ : 0 < μ := RectangularRidgeNumericalParameters.small_pos (by linarith) 10 6
  have hμ1 : μ ≤ 1 := RectangularRidgeNumericalParameters.small_le_one hP 10 6
  have hm : 1 ≤ m := RectangularRidgeTuning.depth_positive N d hN
  have hθ : 0 < θ := weight_positive hN hND
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hpos : ∀ z∈I, (covariance C Q z : Matrix (Fin k) (Fin k) ℝ).PosDef := by
    intro z hz
    simpa only [add_sub_cancel] using (Matrix.PosDef.one.smul hγ).add_posSemidef (Matrix.le_iff.mp (hC z hz))
  have hb := mixed_covariance_budget A hA hAn U (hpos t ht).posSemidef (hphysical t ht)
  have hfloor := RectangularRidgeOffCenterFloor.optimizer_numerical_floor
    (center H B t : Matrix (Fin d) (Fin d) ℂ) (center H B t).property
    (covarianceKraus (mixFamily A U) (covariance C Q t)) hN
    (by simpa only [Fintype.card_fin] using hND) (hcenter t ht) hb
  let x := RectangularRidgeActualEnvelope.branch (mixFamily A U) m θ κ (center H B) (covariance C Q) t
  have hSF : μ • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ (chart (Fin d) x : Matrix (Fin d) (Fin d) ℂ) := by
    dsimp only [x]
    rw [RectangularRidgeActualEnvelope.chart_branch]
    have he : (N : ℝ)+(d : ℝ)+2 = P := by dsimp [P,size]; ring
    simpa only [Fintype.card_fin,he] using hfloor
  have hSnorm : ‖(chart (Fin d) x : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1 := by
    dsimp only [x]
    rw [RectangularRidgeActualEnvelope.chart_branch]
    exact density_norm_le_one (RectangularRidgePotential.optimizer_mem _ _ m θ κ)
  have hj := RectangularRidgeMatchedJointBounds.joint_bounds
    (p := (t,x)) (γ := γ) (μ := μ) (R := (N : ℝ)+1) (b := P^2) (L := (N : ℝ))
    H B (mixFamily A U) (mixFamily_isHermitian A U hA)
    (Nat.cast_nonneg N) (MSManuscriptFrameFamily.family_norm_le A hAn U hU)
    C Q hQ m hm hθ.le hκ.le (by positivity) (sq_nonneg P) hB
    hγ hγ1 hμ hμ1 (htime t ht) (hcenter t ht) (hC t ht) (hC1 t ht) hSF hSnorm
  have hsource := RectangularRidgeMatchedBudget.source_jointCap_le (ι := Fin k) (n := Fin d)
    hP (by simpa only [Fintype.card_fin] using hPk) (by simpa only [Fintype.card_fin] using hPd)
    (by positivity : 0 ≤ (N : ℝ)+1) hR (sq_nonneg P) (le_refl (P^2))
    (Nat.cast_nonneg N) hPN hγlow (le_refl μ)
  have hreg := RectangularRidgeMatchedBudget.regularizer_budget_le hP
    (RectangularRidgePrimitiveMagnitude.weight_add_ridge_le hN hND)
    (Nat.cast_nonneg d) hPd (by positivity : 0 ≤ (2 : ℝ)^m)
    (RectangularRidgePrimitiveMagnitude.order_le_eight_size hN hND) (le_refl μ)
  have hcap : RectangularRidgeMatchedJointBounds.jointCap (Fin k) (Fin d) m ((N : ℝ)+1) (P^2) θ κ γ μ N ≤ J := by
    apply RectangularRidgeMatchedBudget.source_add_regularizer_le hP hsource
    simpa only [RectangularRidgeMixedRegularizerNorms.budget,Fintype.card_fin] using hreg
  have hJ : 0 ≤ J := (RectangularRidgeNumericalParameters.big_pos (by linarith) 160 32).le
  have hh := RectangularRidgeActualEnvelope.potential_fourth_le (B := J)
    (mixFamily A U) (mixFamily_isHermitian A U hA) m hm hθ hκ
    (center H B) (covariance C Q) (contDiff_center H B) (contDiff_covariance C Q)
    hI hpos ht hJ (hj.1.trans hcap) (hj.2.1.trans hcap) (hj.2.2.trans hcap)
  apply hh.trans
  have hiκ : P⁻¹ ≤ κ := by
    dsimp [κ]
    rw [one_div]
    exact inv_anti₀ (by linarith) hPd
  exact RectangularRidgeMatchedBudget.envelope_fourth_le hP hJ (le_refl J) hiκ

end MatrixSpencer.RectangularRidgeMatchedFourth
