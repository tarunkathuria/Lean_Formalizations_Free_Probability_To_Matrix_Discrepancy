import MatrixSpencer.KSManuscriptReportMagnitudeBounds
import MatrixSpencer.KSFullConvexOracleQueries

/-! Polynomial magnitudes for the permitted convex-solver full-cube controller. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullConvexOracleReportBounds
open KSManuscriptReportMagnitudeBounds KSManuscriptPolynomialTaylorBounds
variable {N d : ℕ}
theorem full_stateReport_abs (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) {x : Fin N → ℝ} (hx : x∈ksCube 1)
    {ν : ℝ} (hν : 0<ν) :
    |KSFullConvexOracleValue.stateReport O v
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/(N:ℝ))
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) hd ν x|≤sizeBase N d+ν := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hθ := ksRegularizerScale_pos (n := Fin d) (KSEighthManuscriptPreprocess.epsilon_pos v hd hp)
  exact abs_report_le (KSFullConvexOracleValue.stateReport_accuracy O v _ _ hθ hν hd hx)
    (full_statePotential_abs v hd hp hx)

private theorem full_valueTolerance_le_one {N : ℕ} (hN : 0<N) {δ M : ℝ}
    (hδ : 0<δ) (hδ1 : δ≤1) (hM : 0<M) :
    KSFullManuscriptParameters.valueTolerance N δ M≤1 := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hk0 := (KSFullManuscriptParameters.curvatureTolerance_pos hN hδ).le
  have hk : KSFullManuscriptParameters.curvatureTolerance N δ≤1 := by
    unfold KSFullManuscriptParameters.curvatureTolerance
    apply (div_le_one (by linarith : (0:ℝ)<100*N)).mpr
    linarith
  have ht0 := (KSFullManuscriptParameters.queryStep_pos hN hδ hM).le
  have ht := KSFullManuscriptQueries.queryStep_le_quarter N (M := M) hδ.le
  have ht2 : (KSFullManuscriptParameters.queryStep N δ M)^2≤1 := by nlinarith
  have hm := mul_le_mul hk ht2 (sq_nonneg (KSFullManuscriptParameters.queryStep N δ M)) (by norm_num : (0:ℝ)≤1)
  unfold KSFullManuscriptParameters.valueTolerance
  apply (div_le_one (by linarith : (0:ℝ)<16*N)).mpr
  nlinarith

/-- This covers all full-cube diagonal and mixed stencil queries at once.
Any positive mesh budget is allowed; the actual one is already proved positive. -/
theorem full_faceReport_abs (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) {x : Fin N → ℝ} (hx : x∈ksCube 1)
    (hmargin : ∀i,|x i|<1 → Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)≤1-|x i|)
    {M : ℝ} (hM : 0<M) (z : KSNumericalHessian.Space (KSLiveEnumeration.count x))
    (hz : ‖z‖≤Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/2) :
    |KSFullConvexOracleQueries.faceReport O v
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/(N:ℝ))
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) hd M x z|≤sizeBase N d+1 := by
  have hn := (KSEighthManuscriptPreprocess.count_pos v hd hp).trans_le (KSEighthManuscriptPreprocess.count_le v)
  have hδ := Real.sqrt_pos.mpr (KSEighthManuscriptPreprocess.epsilon_pos v hd hp)
  have hδ1 : Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)≤1 := by
    simpa using Real.sqrt_le_sqrt (KSEighthManuscriptPreprocess.epsilon_le_one v hd hp)
  have hy := KSFullManuscriptLiveCoordinates.face_mem_cube hx z hmargin (by linarith)
  have hν := KSFullManuscriptParameters.valueTolerance_pos hn hδ hM
  exact (full_stateReport_abs O v hd hp hy hν).trans
    (add_le_add_left (full_valueTolerance_le_one hn hδ hδ1 hM) _)


end MatrixSpencer.KSFullConvexOracleReportBounds
