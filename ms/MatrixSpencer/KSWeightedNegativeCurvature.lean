import MatrixSpencer.KSWeightedLiveCoordinates
import MatrixSpencer.KSDebitPreparedCurvature

/-!
# Actual descent curvature in the computed normalized live coordinates

Every live weight is strictly positive. Dividing a live direction by its
weight therefore gives its explicit coordinates in the normalized chart.
The known actual negative second derivative transfers to precisely that
chart, including the original labels and the state-dependent debit.
-/

open Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSWeightedNegativeCurvature

open KSLiveEnumeration KSWeightedLiveCoordinates KSLiveCurve KSDebitPreparation
variable {N : ℕ}

def inverseDirection (x : Fin N → ℝ) (h : Live 1 x → ℝ) : EuclideanSpace ℝ (Fin (count x)) :=
  WithLp.toLp 2 (fun j => h (liveEquiv x j) / Real.sqrt (1 - x (liveEquiv x j) ^ 2))

theorem liveWeight_pos (x : Fin N → ℝ) (i : Live 1 x) : 0 < Real.sqrt (1 - x i ^ 2) := by
  apply Real.sqrt_pos.mpr
  have hi := i.property
  nlinarith [sq_abs (x i), abs_nonneg (x i)]

theorem weighted_inverse (x : Fin N → ℝ) (h : Live 1 x → ℝ) (i : Fin N) :
    weightedMap x (inverseDirection x h) i = KSLiveCurve.extend 1 x h i := by
  rw [weightedMap_apply]
  by_cases hi : |x i| < 1
  · let j : Live 1 x := ⟨i, hi⟩
    change Real.sqrt (1 - x j ^ 2) * KSLiveEnumeration.extend x (inverseDirection x h) j = _
    rw [KSLiveEnumeration.extend_live]
    change Real.sqrt (1 - x j ^ 2) *
      (h (liveEquiv x ((liveEquiv x).symm j)) /
        Real.sqrt (1 - x (liveEquiv x ((liveEquiv x).symm j)) ^ 2)) = _
    rw [(liveEquiv x).apply_symm_apply, mul_div_cancel₀ _ (liveWeight_pos x j).ne']
    exact (KSLiveCurve.extend_live 1 x h j).symm
  · rw [KSLiveEnumeration.extend_dead x _ i hi, KSLiveCurve.extend_dead 1 x h i hi, mul_zero]

theorem inverseDirection_ne_zero (x : Fin N → ℝ) {h : Live 1 x → ℝ} (hh : h ≠ 0) :
    inverseDirection x h ≠ 0 := by
  intro hz
  apply KSLiveCurve.extend_ne_zero 1 x hh
  funext i
  rw [← weighted_inverse x h i, hz, map_zero]

/-- The coefficient paths agree exactly, not just through a derivative. -/
theorem face_inverse_smul (x : Fin N → ℝ) (h : Live 1 x → ℝ) (t : ℝ) :
    face x (t • inverseDirection x h) = path 1 x h t := by
  funext i
  rw [face, map_smul]
  change x i + t * weightedMap x (inverseDirection x h) i = _
  rw [weighted_inverse]
  rfl

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Preparation forces a genuinely negative second derivative in the
actual normalized coordinate system used by the numerical Hessian report. -/
theorem exists_negative_second_after_prepare
    (v : Fin N → n → ℂ) {δ η θ : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hθ : 0 < θ)
    (report : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ x ∈ ksCube 1, |report x - statePotential v δ η θ x| ≤ η / 8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    [Nonempty (Live 1 (prepare η report x))] :
    let y := prepare η report x
    ∃ w : EuclideanSpace ℝ (Fin (count y)), w ≠ 0 ∧
      deriv (fun t : ℝ => statePotential v δ η θ (face y (t • w))) 0 = 0 ∧
      iteratedDeriv 2 (fun t : ℝ => statePotential v δ η θ (face y (t • w))) 0 < 0 := by
  obtain ⟨h, hh, _, hfirst, hsecond⟩ :=
    KSDebitPreparedCurvature.exists_negative_second_after_prepare v hδ hη hθ report haccuracy hx
  refine ⟨inverseDirection _ h, inverseDirection_ne_zero _ hh, ?_, ?_⟩
  · simpa only [face_inverse_smul] using hfirst
  · simpa only [face_inverse_smul] using hsecond

end MatrixSpencer.KSWeightedNegativeCurvature
