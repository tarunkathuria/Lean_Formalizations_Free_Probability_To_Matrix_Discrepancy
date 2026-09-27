import MatrixSpencer.KSJacobiRayleigh
import Mathlib.Analysis.Matrix.Order



open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptGammaTop
open KSRayleighAccuracy KSJacobiRayleigh
variable {k : ℕ}

theorem rayleigh_neg (G : Matrix (Fin k) (Fin k) ℝ) (v : EuclideanSpace ℝ (Fin k)) :
    realRayleigh (-G) v = -realRayleigh G v := by
  simp [realRayleigh, map_neg, inner_neg_right]

theorem rayleigh_smul_vector (G : Matrix (Fin k) (Fin k) ℝ)
    (v : EuclideanSpace ℝ (Fin k)) (a : ℝ) :
    realRayleigh G (a • v) = a^2 * realRayleigh G v := by
  simp [realRayleigh, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

theorem le_scalar_of_unitRayleigh (G : Matrix (Fin k) (Fin k) ℝ) (hG : G.IsSymm)
    (t : ℝ) (hunit : ∀ v : EuclideanSpace ℝ (Fin k), ‖v‖ = 1 → realRayleigh G v ≤ t) :
    G ≤ t • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  have hall (v : EuclideanSpace ℝ (Fin k)) : realRayleigh G v ≤ t * ‖v‖^2 := by
    by_cases hv : v = 0
    · simp [hv, realRayleigh]
    · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hu : ‖‖v‖⁻¹ • v‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]
      have h := hunit (‖v‖⁻¹ • v) hu
      rw [rayleigh_smul_vector] at h
      have hh := mul_le_mul_of_nonneg_left h (sq_nonneg ‖v‖)
      have he : ‖v‖^2 * (‖v‖⁻¹^2 * realRayleigh G v) = realRayleigh G v := by
        field_simp
      rw [he] at hh
      nlinarith
  apply Matrix.le_iff.mpr
  have hGH : G.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] using hG
  have htH : (t • (1 : Matrix (Fin k) (Fin k) ℝ)).IsHermitian := by
    simp [Matrix.IsHermitian]
  refine ⟨htH.sub hGH, ?_⟩
  intro x
  have h := hall (WithLp.toLp 2 x)
  have he : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k))‖^2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, pow_two, Real.norm_eq_abs]
  rw [realRayleigh_eq_quadratic, he] at h
  simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, star_trivial,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] using sub_nonneg.mpr h

def vector (Ghat : Matrix (Fin k) (Fin k) ℝ) (t : ℝ) (hk : 0 < k) :
    EuclideanSpace ℝ (Fin k) := outputVector (-Ghat) (t/64) hk

def value (Ghat : Matrix (Fin k) (Fin k) ℝ) (t : ℝ) (hk : 0 < k) : ℝ :=
  realRayleigh Ghat (vector Ghat t hk)

def stop (Ghat : Matrix (Fin k) (Fin k) ℝ) (t : ℝ) (hk : 0 < k) : Bool :=
  decide (value Ghat t hk ≤ 15*t/16)

theorem vector_norm (Ghat : Matrix (Fin k) (Fin k) ℝ) (t : ℝ) (hk : 0 < k) :
    ‖vector Ghat t hk‖ = 1 := outputVector_norm _ _ _

theorem competitor_bound (Ghat : Matrix (Fin k) (Fin k) ℝ) (hGhat : Ghat.IsSymm)
    {t : ℝ} (ht : 0 < t) (hk : 0 < k) (v : EuclideanSpace ℝ (Fin k)) (hv : ‖v‖ = 1) :
    realRayleigh Ghat v ≤ value Ghat t hk + t/64 := by
  have h := outputVector_competitor_accuracy (-Ghat) hGhat.neg (by linarith : 0<t/64) hk v hv
  simp only [rayleigh_neg] at h
  change -value Ghat t hk ≤ -realRayleigh Ghat v + t/64 at h
  linarith

/-- The actual stopping decision certifies the true Loewner response cap. -/
theorem stop_sound (G Ghat : Matrix (Fin k) (Fin k) ℝ) (hG : G.IsSymm) (hGhat : Ghat.IsSymm)
    {t : ℝ} (ht : 0 < t) (hk : 0 < k)
    (herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (G-Ghat)‖ ≤ t/64)
    (hs : stop Ghat t hk = true) : G ≤ t • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  have hv : value Ghat t hk ≤ 15*t/16 := of_decide_eq_true hs
  apply le_scalar_of_unitRayleigh G hG t
  intro v hn
  have he := (abs_le.mp (realRayleigh_error G Ghat herr v hn)).2
  have hc := competitor_bound Ghat hGhat ht hk v hn
  linarith

/-- Every continuation returns a genuine unit direction with the required true response. -/
theorem continue_sound (G Ghat : Matrix (Fin k) (Fin k) ℝ)
    {t : ℝ} (ht : 0 < t) (hk : 0 < k)
    (herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (G-Ghat)‖ ≤ t/64)
    (hs : stop Ghat t hk = false) :
    ‖vector Ghat t hk‖ = 1 ∧ 7*t/8 < realRayleigh G (vector Ghat t hk) := by
  refine ⟨vector_norm _ _ _, ?_⟩
  have hv : ¬value Ghat t hk ≤ 15*t/16 := of_decide_eq_false hs
  have he := (abs_le.mp (realRayleigh_error G Ghat herr (vector Ghat t hk) (vector_norm _ _ _))).1
  change -(t/64) ≤ realRayleigh G (vector Ghat t hk) - value Ghat t hk at he
  linarith

end MatrixSpencer.MSManuscriptGammaTop
