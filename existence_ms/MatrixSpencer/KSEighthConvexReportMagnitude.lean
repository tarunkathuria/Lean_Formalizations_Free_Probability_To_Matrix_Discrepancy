import MatrixSpencer.KSEighthConvexValue

/-! Magnitudes of actual direct-SDP reports at every eighth-cube query point. -/
open Matrix Set
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthConvexReportMagnitude
open KSManuscriptPolynomialTaylorBounds KSManuscriptReportMagnitudeBounds KSPotentialModels
variable {N d : ℕ}

theorem retainedReport_abs (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1)
    {x : Fin N → ℝ} (hx : x∈ksCube 1) (L : Finset (Fin N)) {ν : ℝ} (hν : 0<ν) :
    |KSEighthConvexValue.retainedReport O v
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) hd L ν x|≤sizeBase N d+ν := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hθ := ksRegularizerScale_pos (n := Fin d) (KSEighthManuscriptPreprocess.epsilon_pos v hd hp)
  have hc := maskedOwners_nonneg (by norm_num : (0:ℝ)≤64) le_rfl hx L
  have hc64 : ∀i,maskedOwners 64 L x i≤64 := by
    intro i
    unfold maskedOwners naturalOwners
    split_ifs <;> nlinarith [sq_nonneg (x i)]
  exact abs_report_le (KSEighthConvexValue.retainedReport_accuracy O v hθ hν hd L le_rfl hx)
    (eighth_commonPotential_abs v hd hp hx _ hc hc64)

theorem queryTolerance_le_one (v : Fin N → Fin d → ℂ)
    {θ κ : ℝ} (hθ : 0<θ) (hκ : 0<κ) (hκ1 : κ≤1) (hd : 0<d)
    (x : Fin N → ℝ) (hk : 0<KSEighthLiveEnumeration.count x) :
    KSEighthHessianQueries.queryTolerance v θ κ x≤1 := by
  have hkn : (1:ℝ)≤KSEighthLiveEnumeration.count x := by exact_mod_cast hk
  have ht0 := (KSEighthHessianQueries.queryMesh_pos v hθ hκ hd x hk).le
  have ht := KSEighthHessianQueries.queryMesh_le v θ κ x
  have ht2 : (KSEighthHessianQueries.queryMesh v θ κ x)^2≤1 := by nlinarith
  have hm := mul_le_mul hκ1 ht2 (sq_nonneg (KSEighthHessianQueries.queryMesh v θ κ x)) (by norm_num : (0:ℝ)≤1)
  unfold KSEighthHessianQueries.queryTolerance KSNumericalHessian.valueTolerance
  apply (div_le_one (by linarith : (0:ℝ)<4*KSEighthLiveEnumeration.count x)).mpr
  change κ*(KSEighthHessianQueries.queryMesh v θ κ x)^2≤_
  nlinarith

theorem faceReport_abs (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1)
    {x : Fin N → ℝ} (hx : x∈ksCube (1/8)) (hk : 0<KSEighthLiveEnumeration.count x)
    {κ : ℝ} (hκ : 0<κ) (hκ1 : κ≤1) (z : KSEighthFacePotential.Space x) (hz : ‖z‖≤1/16) :
    |KSEighthConvexValue.faceReport O v
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) κ hd x z|≤sizeBase N d+1 := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hθ := ksRegularizerScale_pos (n := Fin d) (KSEighthManuscriptPreprocess.epsilon_pos v hd hp)
  have hyq := KSEighthHessianQueries.query_ball_cube hx z hz
  have hy : KSEighthLiveCoordinates.face x z∈ksCube 1 := by
    constructor <;> intro i
    · linarith [hyq.1 i]
    · linarith [hyq.2 i]
  have hν := KSEighthHessianQueries.queryTolerance_pos v hθ hκ hd x hk
  exact (retainedReport_abs O v hd hp hy _ hν).trans
    (add_le_add_left (queryTolerance_le_one v hθ hκ hκ1 hd x hk) _)

end MatrixSpencer.KSEighthConvexReportMagnitude
