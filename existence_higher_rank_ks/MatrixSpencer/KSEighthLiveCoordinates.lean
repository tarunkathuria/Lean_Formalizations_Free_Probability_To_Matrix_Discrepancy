import MatrixSpencer.KSEighthLiveEnumeration
import MatrixSpencer.KSEighthWalkRun

/-!
# The normalized live-coordinate chart of the actual eighth-cube walk

The map is the explicitly enumerated zero extension followed by the
diagonal weights `sqrt(1-x_i²)`. It has operator norm at most one,
preserves frozen labels, and agrees exactly with the implemented proposal.
-/

open Matrix Set Filter
open scoped BigOperators Topology
noncomputable section
namespace MatrixSpencer.KSEighthLiveCoordinates

variable {N : ℕ}
open KSEighthLiveEnumeration

def extensionLinear (x : Fin N → ℝ) :
    EuclideanSpace ℝ (Fin (count x)) →ₗ[ℝ] EuclideanSpace ℝ (Fin N) where
  toFun := extend x
  map_add' := by
    intro v w
    ext i
    by_cases hi : |x i| < (8 : ℝ)⁻¹
    · simp [extend, KSLiveCurve.extend, hi]
    · simp [extend, KSLiveCurve.extend, hi]
  map_smul' := by
    intro c v
    ext i
    by_cases hi : |x i| < (8 : ℝ)⁻¹
    · simp [extend, KSLiveCurve.extend, hi]
    · simp [extend, KSLiveCurve.extend, hi]

def weightedMap (x : Fin N → ℝ) :
    EuclideanSpace ℝ (Fin (count x)) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (fun i => Real.sqrt (1 - x i ^ 2)))).comp
    (extensionLinear x).toContinuousLinearMap

theorem weightedMap_apply (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin (count x))) (i : Fin N) :
    weightedMap x v i = Real.sqrt (1 - x i ^ 2) * extend x v i := by
  change (Matrix.diagonal (fun i => Real.sqrt (1 - x i ^ 2)) *ᵥ WithLp.ofLp (extend x v)) i = _
  simp [Matrix.mulVec_diagonal]

theorem weightedMap_norm (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin (count x))) :
    ‖weightedMap x v‖ ≤ ‖v‖ := by
  rw [← extend_norm x v]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  apply Finset.sum_le_sum
  intro i _
  rw [weightedMap_apply, mul_pow]
  have hs : Real.sqrt (1 - x i ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg (x i)])
  have hs' : Real.sqrt (1 - x i ^ 2) ^ 2 ≤ 1 := by nlinarith [Real.sqrt_nonneg (1 - x i ^ 2)]
  nlinarith [mul_le_mul_of_nonneg_right hs' (sq_nonneg (extend x v i))]

theorem weightedMap_opNorm (x : Fin N → ℝ) : ‖weightedMap x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  simpa only [one_mul] using weightedMap_norm x v

def face (x : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin (count x))) : Fin N → ℝ :=
  fun i => x i + weightedMap x z i

theorem face_zero (x : Fin N → ℝ) : face x 0 = x := by
  funext i
  simp [face]

theorem face_continuous (x : Fin N → ℝ) : Continuous (face x) := by
  unfold face
  fun_prop

theorem face_displacement (x : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin (count x))) (i : Fin N) :
    |face x z i - x i| ≤ ‖z‖ := by
  have hi := PiLp.norm_apply_le (weightedMap x z) i
  rw [Real.norm_eq_abs] at hi
  simpa only [face, add_sub_cancel_left] using hi.trans (weightedMap_norm x z)

theorem face_dead (x : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin (count x)))
    (i : Fin N) (hi : ¬ |x i| < (1/8 : ℝ)) : face x z i = x i := by
  rw [face, weightedMap_apply, extend_dead x z i hi, mul_zero, add_zero]

theorem face_frozen (x : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin (count x)))
    (i : Fin N) (hi : |x i| = (1/8 : ℝ)) : face x z i = x i :=
  face_dead x z i (by rw [hi]; exact lt_irrefl _)

theorem face_live (x : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin (count x))) {δ : ℝ}
    (hmargin : ∀ i, |x i| < (1/8 : ℝ) → δ ≤ 1/8 - |x i|) (hz : ‖z‖ < δ)
    (i : Fin N) (hi : |x i| < (1/8 : ℝ)) : |face x z i| < (1/8 : ℝ) := by
  have hb := (abs_sub_abs_le_abs_sub (face x z i) (x i)).trans (face_displacement x z i)
  linarith [hmargin i hi]

theorem face_mem_cube {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8))
    (z : EuclideanSpace ℝ (Fin (count x))) {δ : ℝ}
    (hmargin : ∀ i, |x i| < (1/8 : ℝ) → δ ≤ 1/8 - |x i|) (hz : ‖z‖ < δ) : face x z ∈ ksCube (1/8) := by
  have hb (i : Fin N) : |face x z i| ≤ (1/8 : ℝ) := by
    by_cases hi : |x i| < (1/8 : ℝ)
    · exact (face_live x z hmargin hz i hi).le
    · rw [face_dead x z i hi]
      exact abs_le.mpr ⟨hx.1 i, hx.2 i⟩
  exact ⟨fun i => (abs_le.mp (hb i)).1, fun i => (abs_le.mp (hb i)).2⟩

theorem eventually_same_frozen (x : Fin N → ℝ) :
    ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin (count x))), ksFrozen (1/8) (face x z) = ksFrozen (1/8) x := by
  have hl : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin (count x))),
      ∀ i : KSLiveCurve.Live (1/8) x, |face x z i| < (1/8 : ℝ) := by
    rw [Filter.eventually_all]
    intro i
    have hc : Continuous (fun z => |face x z i|) :=
      ((continuous_apply i.val).comp (face_continuous x)).abs
    have hi : |face x 0 i| < (1/8 : ℝ) := by rw [face_zero]; exact i.property
    exact hc.continuousAt.eventually (isOpen_Iio.mem_nhds hi)
  filter_upwards [hl] with z hz
  ext i
  simp only [ksFrozen, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : |x i| < (1/8 : ℝ)
  · exact iff_of_false (ne_of_lt (hz ⟨i, hi⟩)) (ne_of_lt hi)
  · rw [face_dead x z i hi]

/-- Exact agreement with the actual normalized symmetric proposal. -/
theorem face_smul_eq_proposal (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin (count x))) (t : ℝ) :
    face x (t • v) = KSEighthWalkRun.proposal x (extend x v) t := by
  funext i
  rw [face, map_smul, KSEighthWalkRun.proposal]
  change x i + t * weightedMap x v i = _
  rw [weightedMap_apply]

end MatrixSpencer.KSEighthLiveCoordinates
