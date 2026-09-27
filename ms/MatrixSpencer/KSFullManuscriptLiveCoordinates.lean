import MatrixSpencer.KSWeightedLiveCoordinates



open Matrix Set Filter
open scoped BigOperators Topology
noncomputable section
namespace MatrixSpencer.KSFullManuscriptLiveCoordinates

open KSLiveEnumeration
variable {N : ℕ}

def linear (x : Fin N → ℝ) :
    EuclideanSpace ℝ (Fin (count x)) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  (KSWeightedLiveCoordinates.extensionLinear x).toContinuousLinearMap

theorem linear_apply (x : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin (count x))) :
    linear x z = extend x z := rfl

theorem linear_norm (x : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin (count x))) :
    ‖linear x z‖ = ‖z‖ := extend_norm x z

def face (x : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin (count x))) : Fin N → ℝ :=
  fun i => x i + linear x z i

theorem face_zero (x : Fin N → ℝ) : face x 0 = x := by
  funext i
  simp [face]

theorem face_continuous (x : Fin N → ℝ) : Continuous (face x) := by
  unfold face
  fun_prop

theorem face_displacement (x : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin (count x))) (i : Fin N) :
    |face x z i - x i| ≤ ‖z‖ := by
  have hi := PiLp.norm_apply_le (linear x z) i
  rw [Real.norm_eq_abs, linear_norm] at hi
  simpa only [face, add_sub_cancel_left] using hi

theorem face_dead (x : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin (count x)))
    (i : Fin N) (hi : ¬ |x i| < 1) : face x z i = x i := by
  rw [face, linear_apply, extend_dead x z i hi, add_zero]

theorem face_frozen (x : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin (count x)))
    (i : Fin N) (hi : |x i| = 1) : face x z i = x i :=
  face_dead x z i (by rw [hi]; exact lt_irrefl _)

theorem face_live (x : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin (count x))) {δ : ℝ}
    (hmargin : ∀ i, |x i| < 1 → δ ≤ 1 - |x i|) (hz : ‖z‖ < δ)
    (i : Fin N) (hi : |x i| < 1) : |face x z i| < 1 := by
  have hb := (abs_sub_abs_le_abs_sub (face x z i) (x i)).trans (face_displacement x z i)
  linarith [hmargin i hi]

theorem face_mem_cube {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (z : EuclideanSpace ℝ (Fin (count x))) {δ : ℝ}
    (hmargin : ∀ i, |x i| < 1 → δ ≤ 1 - |x i|) (hz : ‖z‖ < δ) : face x z ∈ ksCube 1 := by
  have hb (i : Fin N) : |face x z i| ≤ 1 := by
    by_cases hi : |x i| < 1
    · exact (face_live x z hmargin hz i hi).le
    · rw [face_dead x z i hi]
      exact abs_le.mpr ⟨hx.1 i, hx.2 i⟩
  exact ⟨fun i => (abs_le.mp (hb i)).1, fun i => (abs_le.mp (hb i)).2⟩

theorem eventually_same_frozen (x : Fin N → ℝ) :
    ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin (count x))), ksFrozen 1 (face x z) = ksFrozen 1 x := by
  have hl : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin (count x))),
      ∀ i : KSLiveCurve.Live 1 x, |face x z i| < 1 := by
    rw [Filter.eventually_all]
    intro i
    have hc : Continuous (fun z => |face x z i|) :=
      ((continuous_apply i.val).comp (face_continuous x)).abs
    have hi : |face x 0 i| < 1 := by rw [face_zero]; exact i.property
    exact hc.continuousAt.eventually (isOpen_Iio.mem_nhds hi)
  filter_upwards [hl] with z hz
  ext i
  simp only [ksFrozen, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : |x i| < 1
  · exact iff_of_false (ne_of_lt (hz ⟨i, hi⟩)) (ne_of_lt hi)
  · rw [face_dead x z i hi]

def coefficientDirection (x : Fin N → ℝ)
    (w : EuclideanSpace ℝ (Fin (count x))) : KSLiveCurve.Live 1 x → ℝ :=
  fun i => w ((liveEquiv x).symm i)

theorem coefficientDirection_le_two (x : Fin N → ℝ)
    (w : EuclideanSpace ℝ (Fin (count x))) (hw : ‖w‖ ≤ 2)
    (i : KSLiveCurve.Live 1 x) : |coefficientDirection x w i| ≤ 2 := by
  have hi := PiLp.norm_apply_le w ((liveEquiv x).symm i)
  rw [Real.norm_eq_abs] at hi
  exact hi.trans hw

theorem face_smul_eq_path (x : Fin N → ℝ)
    (w : EuclideanSpace ℝ (Fin (count x))) (t : ℝ) :
    face x (t • w) = KSLiveCurve.path 1 x (coefficientDirection x w) t := by
  funext i
  rw [face, map_smul]
  rfl

/-- The square roots are taken only on scalar diagonal owner weights. -/
def weight (x : Fin N → ℝ) (i : Fin (count x)) : ℝ :=
  Real.sqrt (1 - x (liveEquiv x i) ^ 2)

def diagonalMap (x : Fin N → ℝ) :
    EuclideanSpace ℝ (Fin (count x)) →L[ℝ] EuclideanSpace ℝ (Fin (count x)) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (weight x))

theorem diagonalMap_apply (x : Fin N → ℝ)
    (w : EuclideanSpace ℝ (Fin (count x))) (i : Fin (count x)) :
    diagonalMap x w i = weight x i * w i := by
  change (Matrix.diagonal (weight x) *ᵥ WithLp.ofLp w) i = _
  simp [Matrix.mulVec_diagonal]

theorem weight_le_one (x : Fin N → ℝ) (i : Fin (count x)) : |weight x i| ≤ 1 := by
  rw [weight, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg (x (liveEquiv x i))])

theorem face_diagonalMap (x : Fin N → ℝ)
    (w : EuclideanSpace ℝ (Fin (count x))) :
    face x (diagonalMap x w) = KSWeightedLiveCoordinates.face x w := by
  funext i
  rw [face, KSWeightedLiveCoordinates.face, linear_apply, KSWeightedLiveCoordinates.weightedMap_apply]
  by_cases hi : |x i| < 1
  · rw [extend_live x (diagonalMap x w) ⟨i,hi⟩, diagonalMap_apply, weight,
      Equiv.apply_symm_apply, extend_live x w ⟨i,hi⟩]
  · rw [extend_dead x (diagonalMap x w) i hi, extend_dead x w i hi, mul_zero]

end MatrixSpencer.KSFullManuscriptLiveCoordinates
