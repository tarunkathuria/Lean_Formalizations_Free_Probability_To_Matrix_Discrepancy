import MatrixSpencer.KSFullManuscriptDebitValue
import MatrixSpencer.KSFullManuscriptFaceSmoothness
import MatrixSpencer.KSFullManuscriptHessian



open Set Matrix
open scoped BigOperators Topology
noncomputable section
namespace MatrixSpencer.KSFullManuscriptQueries

open KSFullManuscriptParameters KSFullManuscriptLiveCoordinates
open KSNumericalHessian (Space coordinate)
variable {N d : ℕ}

def facePotential (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (x : Fin N → ℝ) :
    Space (KSLiveEnumeration.count x) → ℝ :=
  fun z => KSDebitPreparation.statePotential v δ η θ (face x z)

def faceReport (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0 < d)
    (M : ℝ) (x : Fin N → ℝ) : Space (KSLiveEnumeration.count x) → ℝ :=
  fun z => KSFullManuscriptDebitValue.stateReport v δ η θ hd (valueTolerance N δ M) (face x z)

theorem count_le (x : Fin N → ℝ) : KSLiveEnumeration.count x ≤ N := by
  simpa only [KSLiveEnumeration.count, KSLiveEnumeration.labels, List.length_finRange] using
    (List.length_filter_le (fun i : Fin N => decide (|x i| < 1)) (List.finRange N))

theorem queryStep_le_quarter (N : ℕ) {δ M : ℝ} (hδ : 0 ≤ δ) :
    queryStep N δ M ≤ δ / 4 := by
  have hs : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hp : 0 < Real.sqrt 2 := lt_of_lt_of_le (by norm_num) hs
  apply (min_le_left _ _).trans
  apply (div_le_iff₀ (by positivity : 0 < 4 * Real.sqrt 2)).mpr
  nlinarith

theorem coordinate_norm {m : ℕ} (i : Fin m) : ‖coordinate i‖ = 1 := by
  simp [coordinate, EuclideanSpace.norm_single]

theorem coordinate_add_norm_le_two {m : ℕ} (i j : Fin m) :
    ‖coordinate i + coordinate j‖ ≤ 2 := by
  simpa only [coordinate_norm, one_add_one_eq_two] using norm_add_le (coordinate i) (coordinate j)

theorem coordinate_sub_norm_le_two {m : ℕ} (i j : Fin m) :
    ‖coordinate i - coordinate j‖ ≤ 2 := by
  simpa only [coordinate_norm, one_add_one_eq_two] using norm_sub_le (coordinate i) (coordinate j)

theorem query_norm_le {m : ℕ} (hN : 0 < N) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 < M)
    (w : Space m) (hw : ‖w‖ ≤ 2) : ‖queryStep N δ M • w‖ ≤ δ / 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (queryStep_pos hN hδ hM)]
  have ht := queryStep_le_quarter N (M := M) hδ.le
  nlinarith [mul_le_mul_of_nonneg_left hw (queryStep_pos hN hδ hM).le]

theorem faceReport_accuracy (v : Fin N → Fin d → ℂ) (η : ℝ)
    (hN : 0 < N) {δ θ M : ℝ} (hδ : 0 < δ) (hθ : 0 ≤ θ) (hM : 0 < M) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (hmargin : ∀ i, |x i| < 1 → δ ≤ 1 - |x i|)
    (z : Space (KSLiveEnumeration.count x)) (hz : ‖z‖ ≤ δ / 2) :
    |faceReport v δ η θ hd M x z - facePotential v δ η θ x z| ≤ valueTolerance N δ M :=
  KSFullManuscriptDebitValue.stateReport_accuracy v δ η hθ (valueTolerance_pos hN hδ hM)
    hd (face_mem_cube hx z hmargin (by linarith))


theorem query_accuracy (v : Fin N → Fin d → ℂ) (η : ℝ)
    (hN : 0 < N) {δ θ M : ℝ} (hδ : 0 < δ) (hθ : 0 ≤ θ) (hM : 0 < M) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (hmargin : ∀ i, |x i| < 1 → δ ≤ 1 - |x i|) :
    KSFullManuscriptHessian.QueryAccuracy (facePotential v δ η θ x)
      (faceReport v δ η θ hd M x) 0 (queryStep N δ M) (valueTolerance N δ M) := by
  have ha := faceReport_accuracy v η hN hδ hθ hM hd hx hmargin
  refine ⟨ha 0 (by simp; positivity), ?_, ?_⟩
  · intro i
    have hi : ‖coordinate i‖ ≤ 2 := by rw [coordinate_norm]; norm_num
    have hb := query_norm_le hN hδ hM (coordinate i) hi
    constructor
    · simpa only [zero_add] using ha _ hb
    · simpa only [zero_sub] using ha (-(queryStep N δ M • coordinate i)) (by rwa [norm_neg])
  · intro i j _
    have hp := query_norm_le hN hδ hM _ (coordinate_add_norm_le_two i j)
    have hm := query_norm_le hN hδ hM _ (coordinate_sub_norm_le_two i j)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [zero_add] using ha _ hp
    · simpa only [zero_add] using ha _ hm
    · simpa only [zero_sub] using ha (-(queryStep N δ M • (coordinate i - coordinate j)))
        (by rwa [norm_neg])
    · simpa only [zero_sub] using ha (-(queryStep N δ M • (coordinate i + coordinate j)))
        (by rwa [norm_neg])

end MatrixSpencer.KSFullManuscriptQueries
