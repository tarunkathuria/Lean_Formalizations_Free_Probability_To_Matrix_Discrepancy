import MatrixSpencer.KSNumericalHessian
import MatrixSpencer.KSDebitNumericalValue
import MatrixSpencer.KSWeightedLiveCoordinates
import MatrixSpencer.KSDebitWalkRun
import MatrixSpencer.KSControllerParameters

/-!
# Actual numerical Hessian queries on the prepared live face

The queried function is the original full-label debit state potential on the
explicit weighted live-coordinate face. The value procedure is the finite
numerical density optimization and objective evaluation, at the selected
positive tolerance. The function is used only in correctness statements;
the report definition does not evaluate it.

Prepared margin `δ` and query mesh at most `δ/16` keep all four-query stencil
points in the cube. Consequently their value accuracy follows from the
proved numerical state report, without an oracle or fourth derivative premise.
The latter is still needed separately for the Hessian approximation theorem.
-/

open Matrix Set
open scoped BigOperators Topology
noncomputable section
namespace MatrixSpencer.KSDebitHessianQueries

variable {N d : ℕ}
open KSControllerParameters

def queryMesh (x : Fin N → ℝ) (δ M : ℝ) : ℝ :=
  KSNumericalHessian.mesh (KSLiveEnumeration.count x) (hessianRadius δ) M
    (curvatureTolerance N δ)

def queryTolerance (x : Fin N → ℝ) (δ M : ℝ) : ℝ :=
  KSNumericalHessian.valueTolerance (KSLiveEnumeration.count x) (hessianRadius δ) M
    (curvatureTolerance N δ)

def facePotential (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (x : Fin N → ℝ) :
    EuclideanSpace ℝ (Fin (KSLiveEnumeration.count x)) → ℝ :=
  fun z => KSDebitPreparation.statePotential v δ η θ (KSWeightedLiveCoordinates.face x z)

/-- The actual finite value routine used at all the matrix-stencil queries. -/
def faceReport (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0 < d)
    (M : ℝ) (x : Fin N → ℝ) :
    EuclideanSpace ℝ (Fin (KSLiveEnumeration.count x)) → ℝ :=
  fun z => KSDebitNumericalValue.stateReport v δ η θ hd (queryTolerance x δ M)
    (KSWeightedLiveCoordinates.face x z)

theorem queryMesh_pos (x : Fin N → ℝ) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hlive : 0 < KSLiveEnumeration.count x) : 0 < queryMesh x δ M := by
  exact KSNumericalHessian.mesh_pos hlive (by unfold hessianRadius; positivity) hM
    (by unfold curvatureTolerance; positivity)

theorem queryMesh_le (x : Fin N → ℝ) (δ M : ℝ) : queryMesh x δ M ≤ δ / 16 :=
  KSNumericalHessian.mesh_le_radius _ _ _ _

theorem queryTolerance_pos (x : Fin N → ℝ) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hlive : 0 < KSLiveEnumeration.count x) : 0 < queryTolerance x δ M := by
  exact KSNumericalHessian.valueTolerance_pos hlive (by unfold hessianRadius; positivity) hM
    (by unfold curvatureTolerance; positivity)

theorem coordinate_norm {m : ℕ} (i : Fin m) : ‖KSNumericalHessian.coordinate i‖ = 1 := by
  simp [KSNumericalHessian.coordinate, EuclideanSpace.norm_single]

theorem coordinate_add_norm_le_two {m : ℕ} (i j : Fin m) :
    ‖KSNumericalHessian.coordinate i + KSNumericalHessian.coordinate j‖ ≤ 2 := by
  simpa only [coordinate_norm, one_add_one_eq_two] using norm_add_le (KSNumericalHessian.coordinate i)
    (KSNumericalHessian.coordinate j)

theorem coordinate_sub_norm_le_two {m : ℕ} (i j : Fin m) :
    ‖KSNumericalHessian.coordinate i - KSNumericalHessian.coordinate j‖ ≤ 2 := by
  simpa only [coordinate_norm, one_add_one_eq_two] using norm_sub_le (KSNumericalHessian.coordinate i)
    (KSNumericalHessian.coordinate j)

theorem scaled_query_norm_le (x : Fin N → ℝ) {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hlive : 0 < KSLiveEnumeration.count x)
    (z : EuclideanSpace ℝ (Fin (KSLiveEnumeration.count x))) (hz : ‖z‖ ≤ 2) :
    ‖queryMesh x δ M • z‖ ≤ δ / 8 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (queryMesh_pos x hδ hM hlive)]
  calc
    _ ≤ queryMesh x δ M * 2 :=
      mul_le_mul_of_nonneg_left hz (queryMesh_pos x hδ hM hlive).le
    _ ≤ δ / 8 := by linarith [queryMesh_le x δ M]

/-- Every point in this explicit query ball retains a legal full-label state. -/
theorem query_ball_mem_cube {x : Fin N → ℝ} (hx : x ∈ ksCube 1) {δ : ℝ}
    (hδ : 0 < δ) (hmargin : ∀ i, |x i| < 1 → δ ≤ 1 - |x i|)
    (z : EuclideanSpace ℝ (Fin (KSLiveEnumeration.count x))) (hz : ‖z‖ ≤ δ / 8) :
    KSWeightedLiveCoordinates.face x z ∈ ksCube 1 :=
  KSWeightedLiveCoordinates.face_mem_cube hx z hmargin (by linarith)

/-- Accuracy follows from the actual finite numerical report on legal query
states. The report error is not an input assumption. -/
theorem faceReport_accuracy (v : Fin N → Fin d → ℂ) {δ η θ M : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hθ : 0 < θ) (hM : 0 ≤ M) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (hmargin : ∀ i, |x i| < 1 → δ ≤ 1 - |x i|)
    (hlive : 0 < KSLiveEnumeration.count x)
    (z : EuclideanSpace ℝ (Fin (KSLiveEnumeration.count x))) (hz : ‖z‖ ≤ δ / 8) :
    |faceReport v δ η θ hd M x z - facePotential v δ η θ x z| ≤ queryTolerance x δ M :=
  KSDebitNumericalValue.stateReport_accuracy v hδ.le hη hθ
    (queryTolerance_pos x hδ hM hlive) hd (query_ball_mem_cube hx hδ hmargin z hz)

/-- All four actual reports in every entry, including repeated diagonal
queries, satisfy the generic numerical Hessian's exact accuracy interface. -/
theorem query_accuracy (v : Fin N → Fin d → ℂ) {δ η θ M : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hθ : 0 < θ) (hM : 0 ≤ M) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (hmargin : ∀ i, |x i| < 1 → δ ≤ 1 - |x i|)
    (hlive : 0 < KSLiveEnumeration.count x) :
    KSNumericalHessian.QueryAccuracy (facePotential v δ η θ x)
      (faceReport v δ η θ hd M x) 0 (queryMesh x δ M) (queryTolerance x δ M) := by
  intro i j
  have hp := scaled_query_norm_le x hδ hM hlive _ (coordinate_add_norm_le_two i j)
  have hm := scaled_query_norm_le x hδ hM hlive _ (coordinate_sub_norm_le_two i j)
  have ha := faceReport_accuracy v hδ hη hθ hM hd hx hmargin hlive
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [zero_add] using ha _ hp
  · simpa only [zero_add] using ha _ hm
  · simpa only [zero_sub] using ha (- (queryMesh x δ M •
      (KSNumericalHessian.coordinate i - KSNumericalHessian.coordinate j))) (by rw [norm_neg]; exact hm)
  · simpa only [zero_sub] using ha (- (queryMesh x δ M •
      (KSNumericalHessian.coordinate i + KSNumericalHessian.coordinate j))) (by rw [norm_neg]; exact hp)

/-- An actual active prepared state supplies the cube, margin, and positive
live dimension internally. Its preparation report need not equal the higher
accuracy report used for the Hessian's finite queries. -/
theorem prepared_query_accuracy (v : Fin N → Fin d → ℂ) {δ η θ M : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hθ : 0 < θ) (hM : 0 ≤ M) (hd : 0 < d)
    {report : (Fin N → ℝ) → ℝ} (s : KSDebitWalkRun.PreparedState N δ η report)
    (hactive : ¬KSDebitWalkRun.terminal s) :
    KSNumericalHessian.QueryAccuracy (facePotential v δ η θ s.coeff)
      (faceReport v δ η θ hd M s.coeff) 0 (queryMesh s.coeff δ M)
      (queryTolerance s.coeff δ M) :=
  query_accuracy v hδ hη hθ hM hd s.cube (fun i hi => (s.margin i hi).le)
    (KSLiveEnumeration.count_pos_of_not_vertex s.cube hactive)

end MatrixSpencer.KSDebitHessianQueries
