import MatrixSpencer.KSFullManuscriptController
import MatrixSpencer.KSFullManuscriptTaylor
import MatrixSpencer.KSPreparedNegativeCurvature



open Matrix Set
open scoped BigOperators Topology
noncomputable section
namespace MatrixSpencer.KSFullManuscriptRayleigh

open KSFullManuscriptLiveCoordinates KSFullManuscriptQueries KSFullManuscriptParameters
open KSNumericalHessian (Space hessian)
variable {N d : ℕ}


theorem weighted_rayleigh (x : Fin N → ℝ)
    (A : Matrix (Fin (KSLiveEnumeration.count x)) (Fin (KSLiveEnumeration.count x)) ℝ)
    (w : Space (KSLiveEnumeration.count x)) :
    KSRayleighAccuracy.realRayleigh (KSFullManuscriptHessian.weighted (weight x) A) w =
      KSRayleighAccuracy.realRayleigh A (diagonalMap x w) / 2 := by
  simp only [KSRayleighAccuracy.realRayleigh_eq_quadratic, dotProduct, Matrix.mulVec,
    Finset.mul_sum, Finset.sum_div, diagonalMap_apply, KSFullManuscriptHessian.weighted]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change w i * (weight x i * A i j * weight x j / 2 * w j) =
    (diagonalMap x w i * (A i j * diagonalMap x w j)) / 2
  rw [diagonalMap_apply, diagonalMap_apply]
  ring

theorem weighted_hessian_rayleigh (x : Fin N → ℝ)
    (f : Space (KSLiveEnumeration.count x) → ℝ) (z w : Space (KSLiveEnumeration.count x)) :
    KSRayleighAccuracy.realRayleigh (KSFullManuscriptHessian.weighted (weight x) (hessian f z)) w =
      fderiv ℝ (fderiv ℝ f) z (diagonalMap x w) (diagonalMap x w) / 2 := by
  rw [weighted_rayleigh, KSNumericalHessian.hessian_rayleigh]

variable [Nonempty (Fin d)]
open KSFullManuscriptController KSDebitWalkRun

/-- The original local descent theorem applies to this controller's actual
exhausted ellipsoid-based retirement tests. -/
theorem leastRayleigh_neg (v : Fin N → Fin d → ℂ) (hN : 0 < N) {δ η θ M : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (hM : 0 < M) (hd : 0 < d)
    (s : Prepared v δ η θ hd) (hs : ¬terminal s) :
    KSRayleighAccuracy.leastRayleigh (KSFullManuscriptHessian.weighted (weight s.coeff)
      (hessian (facePotential v δ η θ s.coeff) 0)) < 0 := by
  let C := controller v hN hδ hη hθ hM hd
  let f := facePotential v δ η θ s.coeff
  have hf : ContDiffAt ℝ 2 f 0 :=
    (KSFullManuscriptFaceSmoothness.contDiffAt_statePotential_face v hδ.le hη.le hθ s.cube).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  obtain ⟨w,hw,_,hneg⟩ := KSPreparedNegativeCurvature.exists_negative_second C s hs
  have he : (fun t : ℝ => KSDebitPreparation.statePotential v δ η θ
      (KSWeightedLiveCoordinates.face s.coeff (t • w))) =
      (fun t => f (0 + t • diagonalMap s.coeff w)) := by
    funext t
    rw [zero_add, ← map_smul]
    exact congrArg (KSDebitPreparation.statePotential v δ η θ) (face_diagonalMap s.coeff (t • w)).symm
  change iteratedDeriv 2 (fun t : ℝ => KSDebitPreparation.statePotential v δ η θ
    (KSWeightedLiveCoordinates.face s.coeff (t • w))) 0 < 0 at hneg
  rw [he, KSFourthDifference.line_second f 0 _ hf] at hneg
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hi : 0 < ‖w‖⁻¹ := inv_pos.mpr hn
  let u : Space (KSLiveEnumeration.count s.coeff) := ‖w‖⁻¹ • w
  have hu : ‖u‖ = 1 := by
    rw [show u = ‖w‖⁻¹ • w from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos hi, inv_mul_cancel₀ (ne_of_gt hn)]
  have hq : KSRayleighAccuracy.realRayleigh
      (KSFullManuscriptHessian.weighted (weight s.coeff) (hessian f 0)) u < 0 := by
    rw [weighted_hessian_rayleigh]
    change fderiv ℝ (fderiv ℝ f) 0 (diagonalMap s.coeff (‖w‖⁻¹ • w))
      (diagonalMap s.coeff (‖w‖⁻¹ • w)) / 2 < 0
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hi (mul_neg_of_pos_of_neg hi hneg))
      (by norm_num)
  exact (KSRayleighAccuracy.leastRayleigh_le _ u hu).trans_lt hq


theorem liveDirection_hessian_le (v : Fin N → Fin d → ℂ) (hN : 0 < N) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (hd : 0 < d)
    (s : Prepared v δ η θ hd) (hs : ¬terminal s) :
    let M := KSFullManuscriptTaylor.budget v δ η θ
    let w := liveDirection v δ η θ M hd s hs
    fderiv ℝ (fderiv ℝ (facePotential v δ η θ s.coeff)) 0
      (diagonalMap s.coeff w) (diagonalMap s.coeff w) ≤ 6 * curvatureTolerance N δ := by
  let M := KSFullManuscriptTaylor.budget v δ η θ
  have hM := KSFullManuscriptTaylor.budget_pos v hδ hη.le hθ
  have hf : ContDiffAt ℝ 2 (facePotential v δ η θ s.coeff) 0 :=
    (KSFullManuscriptFaceSmoothness.contDiffAt_statePotential_face v hδ.le hη.le hθ s.cube).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hnegative := leastRayleigh_neg v hN hδ hη hθ hM hd s hs
  have hl := KSFullManuscriptTaylor.lineBounds v hN hδ hη.le hθ s.cube
    (fun i => (s.margin i i.property).le)
  have hq := query_accuracy v η hN hδ hθ.le hM hd s.cube (fun i hi => (s.margin i hi).le)
  have ho := KSFullManuscriptHessian.output_accuracy (facePotential v δ η θ s.coeff)
    (faceReport v δ η θ hd M s.coeff) 0 (weight s.coeff) (weight_le_one s.coeff)
    (KSLiveEnumeration.count_pos_of_not_vertex s.cube hs) (count_le s.coeff)
    hδ hM hf hl hq
  have hh := ho.2
  rw [weighted_hessian_rayleigh] at hh
  change fderiv ℝ (fderiv ℝ (facePotential v δ η θ s.coeff)) 0
    (diagonalMap s.coeff (liveDirection v δ η θ M hd s hs))
    (diagonalMap s.coeff (liveDirection v δ η θ M hd s hs)) / 2 ≤ _ at hh
  dsimp only
  linarith

end MatrixSpencer.KSFullManuscriptRayleigh
