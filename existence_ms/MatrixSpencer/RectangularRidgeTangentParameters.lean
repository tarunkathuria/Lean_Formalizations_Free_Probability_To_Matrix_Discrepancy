import MatrixSpencer.RectangularRidgeTangentValues

/-! Explicit polynomial inverse accuracies for the two convex-value supporting
tangent queries. The fixed absolute report error is small enough for every
nonempty epoch's scaled acceptance margin. -/

noncomputable section
namespace MatrixSpencer.RectangularRidgeTangentParameters
open RectangularRidgeTangentValues

def tolerance : ℝ := 1/10000
def radius (s : ℝ) : ℝ := 3*s^2

theorem curvature_le {s κ R : ℝ} (hs : 1≤s) (hκ : 0<κ) (hki : κ⁻¹≤s)
    (hR : 0≤R) (hRs : R≤radius s) : curvature κ R≤18*s^5 := by
  have hR2 := pow_le_pow_left₀ hR hRs 2
  have hk2 : 2/κ≤2*s := by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hki (by norm_num : (0:ℝ)≤2)
  have h := mul_le_mul hk2 hR2 (sq_nonneg R) (by linarith : (0:ℝ)≤2*s)
  exact h.trans_eq (by unfold radius; ring)

theorem inverse_spacing_le {s κ R ε E : ℝ} (hs : 1≤s) (hκ : 0<κ) (hki : κ⁻¹≤s)
    (hR : 0≤R) (hRs : R≤radius s) (hε : 0<ε) (hE : ε⁻¹≤E) :
    (spacing κ R ε)⁻¹≤114*E*s^5 := by
  have hc := curvature_le hs hκ hki hR hRs
  have hs5 : 1≤s^5 := one_le_pow₀ hs
  have hc1 : curvature κ R+1≤19*s^5 := by linarith
  have hE0 : 0≤E := (inv_pos.mpr hε).le.trans hE
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hc1 (by norm_num : (0:ℝ)≤6)) hE
    (inv_nonneg.mpr hε.le) (by positivity : (0:ℝ)≤6*(19*s^5))
  unfold spacing
  rw [inv_div, div_eq_mul_inv]
  exact h.trans_eq (by ring)

theorem inverse_precision_le {s κ R ε E : ℝ} (hs : 1≤s) (hκ : 0<κ) (hki : κ⁻¹≤s)
    (hR : 0≤R) (hRs : R≤radius s) (hε : 0<ε) (hE : ε⁻¹≤E) :
    (precision κ R ε)⁻¹≤684*E^2*s^5 := by
  have hb := inverse_spacing_le hs hκ hki hR hRs hε hE
  have hE0 : 0≤E := (inv_pos.mpr hε).le.trans hE
  have hstep := spacing_pos (R:=R) hκ hε
  have h := mul_le_mul hE hb (inv_nonneg.mpr hstep.le) hE0
  have h6 := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤6)
  unfold precision
  rw [inv_div, div_eq_mul_inv, mul_inv_rev]
  convert h6 using 1 <;> ring

theorem fixed_inverse_bounds {s D : ℝ} (hs : 1≤s) (hD : 1≤D) (hDs : D≤s) :
    (spacing (1/D) (radius s) tolerance)⁻¹≤1140000*s^5 ∧
    (precision (1/D) (radius s) tolerance)⁻¹≤68400000000*s^5 := by
  have hκ : 0<(1/D:ℝ) := by positivity
  have hki : (1/D:ℝ)⁻¹≤s := by simpa using hDs
  have hR : 0≤radius s := by unfold radius; positivity
  have ht : 0<tolerance := by norm_num [tolerance]
  have he : tolerance⁻¹≤(10000:ℝ) := by norm_num [tolerance]
  constructor
  · convert inverse_spacing_le hs hκ hki hR le_rfl ht he using 1 <;> ring
  · convert inverse_precision_le hs hκ hki hR le_rfl ht he using 1 <;> ring

theorem tolerance_le_scaled_margin {ℓ : ℕ} (hℓ : 1≤ℓ) :
    tolerance≤Real.sqrt (ℓ:ℝ)/100 := by
  have h : (1:ℝ)≤ℓ := by exact_mod_cast hℓ
  have hr : (1:ℝ)≤Real.sqrt (ℓ:ℝ) := by
    exact Real.le_sqrt_of_sq_le (by simpa using h)
  norm_num [tolerance]
  linarith

end MatrixSpencer.RectangularRidgeTangentParameters
