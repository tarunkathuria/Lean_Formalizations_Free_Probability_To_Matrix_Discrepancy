import MatrixSpencer.KSEighthNegativeRayleigh
import MatrixSpencer.KSEighthInputTaylorBound

/-!
# Finite eighth-cube Hessian queries with input-only guarantees

The query radius is fixed at 1/32. The retained owners are evaluated even
outside the current face. Every query lies inside the quarter cube, so the
actual finite value routine is accurate there. The actual fourth derivative
bound comes from the original input, not from a Taylor oracle.
-/

open Matrix Set
open scoped BigOperators ContDiff Topology Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthHessianQueries
open KSEighthFacePotential KSEighthLiveCoordinates KSEighthLiveEnumeration
variable {N d : ℕ}
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
local instance {k : Type*} [Fintype k] [DecidableEq k] :
    NormedAddCommGroup (selfAdjoint (Matrix k k ℝ)) := inferInstance
local instance {k : Type*} [Fintype k] [DecidableEq k] :
    NormedSpace ℝ (selfAdjoint (Matrix k k ℝ)) := inferInstance

def queryMesh (v : Fin N → Fin d → ℂ) (θ κ : ℝ) (x : Fin N → ℝ) : ℝ :=
  KSNumericalHessian.mesh (count x) (1/32) (KSEighthInputTaylorBound.fourthBudget v θ) κ

def queryTolerance (v : Fin N → Fin d → ℂ) (θ κ : ℝ) (x : Fin N → ℝ) : ℝ :=
  KSNumericalHessian.valueTolerance (count x) (1/32) (KSEighthInputTaylorBound.fourthBudget v θ) κ

def faceReport (v : Fin N → Fin d → ℂ) (θ κ : ℝ) (hd : 0 < d) (x : Fin N → ℝ) : Space x → ℝ :=
  fun z => KSEighthNumericalValue.retainedReport v θ hd (KSPotentialModels.live (1/8) x)
    (queryTolerance v θ κ x) (face x z)

theorem queryMesh_pos (v : Fin N → Fin d → ℂ) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (hd : 0 < d) (x : Fin N → ℝ) (hlive : 0 < count x) : 0 < queryMesh v θ κ x := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact KSNumericalHessian.mesh_pos hlive (by norm_num) (KSEighthInputTaylorBound.fourthBudget_pos v hθ).le hκ

theorem queryMesh_le (v : Fin N → Fin d → ℂ) (θ κ : ℝ) (x : Fin N → ℝ) :
    queryMesh v θ κ x ≤ 1/32 := KSNumericalHessian.mesh_le_radius _ _ _ _

theorem queryTolerance_pos (v : Fin N → Fin d → ℂ) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (hd : 0 < d) (x : Fin N → ℝ) (hlive : 0 < count x) : 0 < queryTolerance v θ κ x := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact KSNumericalHessian.valueTolerance_pos hlive (by norm_num) (KSEighthInputTaylorBound.fourthBudget_pos v hθ).le hκ

theorem coordinate_norm {m : ℕ} (i : Fin m) : ‖KSNumericalHessian.coordinate i‖ = 1 := by
  simp [KSNumericalHessian.coordinate, EuclideanSpace.norm_single]

theorem coordinate_add_norm {m : ℕ} (i j : Fin m) :
    ‖KSNumericalHessian.coordinate i+KSNumericalHessian.coordinate j‖ ≤ 2 := by
  simpa only [coordinate_norm, one_add_one_eq_two] using norm_add_le (KSNumericalHessian.coordinate i) (KSNumericalHessian.coordinate j)

theorem coordinate_sub_norm {m : ℕ} (i j : Fin m) :
    ‖KSNumericalHessian.coordinate i-KSNumericalHessian.coordinate j‖ ≤ 2 := by
  simpa only [coordinate_norm, one_add_one_eq_two] using norm_sub_le (KSNumericalHessian.coordinate i) (KSNumericalHessian.coordinate j)

theorem lineDirection_le (x : Fin N → ℝ) (w : Space x) (hw : ‖w‖ ≤ 2) :
    ∀ i, |lineDirection x w i| ≤ 2 := by
  intro i
  exact (PiLp.norm_apply_le (weightedMap x w) i).trans ((weightedMap_norm x w).trans hw)

theorem query_ball_cube {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8))
    (z : Space x) (hz : ‖z‖ ≤ 1/16) : face x z ∈ ksCube (1/4) := by
  have hi (i : Fin N) := face_displacement x z i
  constructor <;> intro i
  · have h := (abs_le.mp (hi i)).1
    linarith [hx.1 i]
  · have h := (abs_le.mp (hi i)).2
    linarith [hx.2 i]

theorem faceReport_accuracy (v : Fin N → Fin d → ℂ) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (hd : 0 < d) {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) (hlive : 0 < count x)
    (z : Space x) (hz : ‖z‖ ≤ 1/16) :
    |faceReport v θ κ hd x z-potential v θ x z| ≤ queryTolerance v θ κ x := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  rw [potential_eq_retained v hθ x z (by norm_num : (1/4 : ℝ) ≤ 1) (query_ball_cube hx z hz)]
  exact KSEighthNumericalValue.retainedReport_accuracy v hθ
    (queryTolerance_pos v hθ hκ hd x hlive) hd _ (by norm_num) (query_ball_cube hx z hz)

theorem scaled_query_norm (v : Fin N → Fin d → ℂ) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (hd : 0 < d) (x : Fin N → ℝ) (hlive : 0 < count x) (w : Space x) (hw : ‖w‖ ≤ 2) :
    ‖queryMesh v θ κ x • w‖ ≤ 1/16 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (queryMesh_pos v hθ hκ hd x hlive)]
  have h := mul_le_mul_of_nonneg_left hw (queryMesh_pos v hθ hκ hd x hlive).le
  linarith [queryMesh_le v θ κ x]

theorem query_accuracy (v : Fin N → Fin d → ℂ) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (hd : 0 < d) {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) (hlive : 0 < count x) :
    KSNumericalHessian.QueryAccuracy (potential v θ x) (faceReport v θ κ hd x)
      0 (queryMesh v θ κ x) (queryTolerance v θ κ x) := by
  intro i j
  have hp := scaled_query_norm v hθ hκ hd x hlive _ (coordinate_add_norm i j)
  have hm := scaled_query_norm v hθ hκ hd x hlive _ (coordinate_sub_norm i j)
  have ha := faceReport_accuracy v hθ hκ hd hx hlive
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [zero_add] using ha _ hp
  · simpa only [zero_add] using ha _ hm
  · simpa only [zero_sub] using ha (-(queryMesh v θ κ x •
      (KSNumericalHessian.coordinate i-KSNumericalHessian.coordinate j))) (by rwa [norm_neg])
  · simpa only [zero_sub] using ha (-(queryMesh v θ κ x •
      (KSNumericalHessian.coordinate i+KSNumericalHessian.coordinate j))) (by rwa [norm_neg])

/-- Actual smoothness on every stencil line, including doubled diagonal directions. -/
theorem line_contDiffOn (v : Fin N → Fin d → ℂ) {θ : ℝ} (hθ : 0 < θ)
    (hd : 0 < d) {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8))
    (w : Space x) (hw : ‖w‖ ≤ 2) :
    ContDiffOn ℝ 4 (fun t : ℝ => potential v θ x (t • w)) (Icc (-(1/32)) (1/32)) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let vr := fun i : KSLiveCurve.Live (1/8) x => v i
  let xl := fun i : KSLiveCurve.Live (1/8) x => x i
  let h := lineDirection x w
  let Q := KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x
  have hQ := KSPotentialModels.center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) x
  have he : (fun t : ℝ => potential v θ x (t • w)) = KSEighthLocalState.curvePotential Q vr θ xl h := by
    funext t
    exact potential_line_eq v θ x w t
  rw [he]
  intro t ht
  have hpos : ∀ i, |xl i+t*h i| < 1 := by
    intro i
    have hxi : |xl i| ≤ (1/8 : ℝ) := abs_le.mpr ⟨hx.1 i,hx.2 i⟩
    have hta : |t| ≤ (1/32 : ℝ) := abs_le.mpr ht
    have hh := lineDirection_le x w hw i
    have hm := mul_le_mul hta hh (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/32)
    rw [← abs_mul] at hm
    have ha := abs_add_le (xl i) (t*h i)
    dsimp only [h] at *
    linarith
  have hC := KSEighthTraceSource.coefficient_posDef xl h t hpos
  have hj := contDiffAt_jointHermitianOwnerPotential (KSEighthActualState.family vr)
    (KSEighthActualState.family_isHermitian vr) hθ
    (KSEighthAnalyticCurve.H Q hQ vr h t) (KSEighthAnalyticCurve.C xl h t) hC
  have hc := hj.comp t ((KSEighthAnalyticCurve.contDiff_H Q hQ vr h).contDiffAt.prodMk
    (KSEighthAnalyticCurve.contDiff_C xl h).contDiffAt)
  exact hc.contDiffWithinAt.of_le (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))

theorem line_fourth_bound (v : Fin N → Fin d → ℂ) {θ : ℝ} (hθ : 0 < θ)
    (hd : 0 < d) {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8))
    (w : Space x) (hw : ‖w‖ ≤ 2) {t : ℝ} (ht : |t| ≤ 1/32) :
    |iteratedDeriv 4 (fun s : ℝ => potential v θ x (s • w)) t| ≤ KSEighthInputTaylorBound.fourthBudget v θ := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have he : (fun s : ℝ => potential v θ x (s • w)) =
      KSEighthLocalState.curvePotential (KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x)
        (fun i : KSLiveCurve.Live (1/8) x => v i) θ (fun i => x i) (lineDirection x w) := by
    funext s
    exact potential_line_eq v θ x w s
  rw [he]
  exact KSEighthInputTaylorBound.curve_fourth_bound v hθ x hx _ (lineDirection_le x w hw) ht

theorem line_bounds (v : Fin N → Fin d → ℂ) {θ : ℝ} (hθ : 0 < θ)
    (hd : 0 < d) {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) :
    KSNumericalHessian.LineBounds (potential v θ x) 0 (1/32) (KSEighthInputTaylorBound.fourthBudget v θ) := by
  intro i j
  simp only [zero_add]
  exact ⟨line_contDiffOn v hθ hd hx _ (coordinate_add_norm i j),
    line_contDiffOn v hθ hd hx _ (coordinate_sub_norm i j),
    fun _ ht => line_fourth_bound v hθ hd hx _ (coordinate_add_norm i j) (abs_le.mpr ht),
    fun _ ht => line_fourth_bound v hθ hd hx _ (coordinate_sub_norm i j) (abs_le.mpr ht)⟩

end MatrixSpencer.KSEighthHessianQueries
