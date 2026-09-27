import MatrixSpencer.DyadicBalancedModel
import MatrixSpencer.ObservedCapResponse

/-! Actual high-spectrum output estimates for the balanced dyadic model.
The two endpoint budgets are derived from the physical Gram cap and fixed point. -/

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer
namespace DyadicHighForcing

variable {n ι : Type*} [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
local instance highDyadicCStar : CStarAlgebra (Matrix n n ℂ) := {}

lemma paired_exponent_le_one (m : ℕ) (hm : 1 ≤ m) : 2 / (2 : ℝ) ^ m ≤ 1 := by
  have hp : (2 : ℝ) ≤ 2 ^ m := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
  exact (div_le_one (by positivity)).mpr hp

/-- The inverse-transport endpoint retains its correlation with the fixed density. -/
lemma inverseTransport_output_le (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef)
    {t ε k : ℝ} (ht : 0 ≤ t) (hε : 0 < ε)
    (hWP : realTrace (Z⁻¹ * balancedDensity S Z) ≤ k)
    (hcap : physicalRealGram (balancedDensity S Z) D ≤ algebraMap ℝ (Matrix ι ι ℝ) t)
    (hfix : krausChannel D (balancedDensity S Z) = balancedDensity S Z) :
    realTrace (Z⁻¹ * SpectralHighForcing.outputGram (balancedDensity_posDef hS hZ).isHermitian ε D) ≤
      2 * (t / ε) ^ 2 * k := by
  have h := realTrace_mul_mono hZ.inv.posSemidef
    (SpectralHighForcing.outputGram_le_P D hD (balancedDensity_posDef hS hZ).posSemidef ht hε hcap hfix)
  rw [Matrix.mul_smul, realTrace_smul] at h
  exact h.trans (mul_le_mul_of_nonneg_left hWP (by positivity))

/-- Interpolation is applied to the actual positive high-output covariance. -/
theorem high_output_interpolation_le (m : ℕ) (hm : 1 ≤ m)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef)
    {t ε k : ℝ} (ht : 0 ≤ t) (hε : 0 < ε)
    (hWP : realTrace (Z⁻¹ * balancedDensity S Z) ≤ k)
    (hcap : physicalRealGram (balancedDensity S Z) D ≤ algebraMap ℝ (Matrix ι ι ℝ) t)
    (hfix : krausChannel D (balancedDensity S Z) = balancedDensity S Z) :
    realTrace (DyadicBalancedModel.balancedDyadicRoot m S Z *
      SpectralHighForcing.outputGram (balancedDensity_posDef hS hZ).isHermitian ε D) ≤
      (2 * (t / ε) ^ 2 * k) ^ (1 - 2 / (2 : ℝ) ^ m) *
        (2 * Real.sqrt (realTrace (balancedRoot S Z * balancedRoot S Z) * t *
          (t / ε) ^ 3 * realTrace (balancedDensity S Z))) ^ (2 / (2 : ℝ) ^ m) := by
  have hP := balancedDensity_posDef hS hZ
  have hR := balancedRoot_posDef hS hZ
  have hX := SpectralHighForcing.outputGram_posSemidef hP.posSemidef ε D hD
  have hi := DyadicBalancedModel.balancedDyadicRoot_trace_le m hm hS.posSemidef hZ hX
  have hW := inverseTransport_output_le D hD hS hZ ht hε hWP hcap hfix
  have hRend := ObservedCapResponse.trace_weighted_output_le D hD hP.posSemidef
    hR.posSemidef ht hε hcap hfix
  apply hi.trans
  apply mul_le_mul
  · exact Real.rpow_le_rpow (realTrace_mul_nonneg hZ.inv.posSemidef hX) hW
      (sub_nonneg.mpr (paired_exponent_le_one m hm))
  · exact Real.rpow_le_rpow (realTrace_mul_nonneg hR.posSemidef hX) hRend (by positivity)
  · exact Real.rpow_nonneg (realTrace_mul_nonneg hR.posSemidef hX) _
  · exact Real.rpow_nonneg ((realTrace_mul_nonneg hZ.inv.posSemidef hX).trans hW) _

lemma high_radius_identity {k L c : ℝ} (hk : 0 < k) (hL : 0 < L) (hc : 0 < c) :
    Real.sqrt (k * (L / Real.sqrt k) * (L / c) ^ 3 * Real.sqrt k) =
      L ^ 2 * c ^ (-(3 : ℝ) / 2) * Real.sqrt k := by
  have hcPow : (c ^ (-(3 : ℝ) / 2)) ^ 2 = (c ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le,
      show (-(3 : ℝ) / 2) * (2 : ℕ) = -(3 : ℝ) by norm_num,
      Real.rpow_neg hc.le]
    norm_num
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  rw [mul_pow, mul_pow, Real.sq_sqrt hk.le, hcPow]
  field_simp

lemma high_endpoint_interpolation_identity {a c k : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hk : 0 < k) (q : ℝ) :
    (a * c ^ (-(2 : ℝ)) * k) ^ (1 - 2 * q) *
      (a * c ^ (-(3 : ℝ) / 2) * Real.sqrt k) ^ (2 * q) =
      a * c ^ (q - 2) * k ^ (1 - q) := by
  rw [Real.sqrt_eq_rpow,
    Real.mul_rpow (mul_nonneg ha.le (Real.rpow_nonneg hc.le _)) hk.le,
    Real.mul_rpow ha.le (Real.rpow_nonneg hc.le _),
    Real.mul_rpow (mul_nonneg ha.le (Real.rpow_nonneg hc.le _)) (Real.rpow_nonneg hk.le _),
    Real.mul_rpow ha.le (Real.rpow_nonneg hc.le _),
    ← Real.rpow_mul hc.le, ← Real.rpow_mul hc.le, ← Real.rpow_mul hk.le]
  calc
    _ = (a ^ (1 - 2 * q) * a ^ (2 * q)) *
        (c ^ (-(2 : ℝ) * (1 - 2 * q)) * c ^ (-(3 : ℝ) / 2 * (2 * q))) *
        (k ^ (1 - 2 * q) * k ^ ((1 / 2 : ℝ) * (2 * q))) := by ring
    _ = _ := by
      rw [← Real.rpow_add ha, ← Real.rpow_add hc, ← Real.rpow_add hk,
        show 1 - 2 * q + 2 * q = 1 by ring, Real.rpow_one,
        show -(2 : ℝ) * (1 - 2 * q) + -(3 : ℝ) / 2 * (2 * q) = q - 2 by ring,
        show 1 - 2 * q + (1 / 2 : ℝ) * (2 * q) = 1 - q by ring]

lemma cap_cutoff_ratio {k L c : ℝ} (hk : 0 < k) (hc : 0 < c) :
    (L / Real.sqrt k) / (c / Real.sqrt k) = L / c := by
  have hs := (Real.sqrt_pos.mpr hk).ne'
  field_simp

lemma high_radius_le_budget {r p k L c : ℝ}
    (hk : 0 < k) (hL : 0 < L) (hc : 0 < c)
    (hp0 : 0 ≤ p) (hr : r ≤ k) (hp : p ≤ Real.sqrt k) :
    Real.sqrt (r * (L / Real.sqrt k) * ((L / Real.sqrt k) / (c / Real.sqrt k)) ^ 3 * p) ≤
      L ^ 2 * c ^ (-(3 : ℝ) / 2) * Real.sqrt k := by
  rw [cap_cutoff_ratio hk hc]
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul hr hp hp0 hk.le)
    (show 0 ≤ (L / Real.sqrt k) * (L / c) ^ 3 by positivity)
  have hh' : r * (L / Real.sqrt k) * (L / c) ^ 3 * p ≤
      k * (L / Real.sqrt k) * (L / c) ^ 3 * Real.sqrt k := by
    convert hh using 1 <;> ring
  exact (Real.sqrt_le_sqrt hh').trans_eq (high_radius_identity hk hL hc)

/-- The correlated high-output trace has the precise rectangular scaling. -/
theorem high_output_trace_le_budget (m : ℕ) (hm : 1 ≤ m)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef)
    {k L c : ℝ} (hk : 0 < k) (hL : 0 < L) (hc : 0 < c)
    (hPtrace : realTrace (balancedDensity S Z) ≤ Real.sqrt k)
    (hRtrace : realTrace (balancedRoot S Z * balancedRoot S Z) ≤ k)
    (hWP : realTrace (Z⁻¹ * balancedDensity S Z) ≤ k)
    (hcap : physicalRealGram (balancedDensity S Z) D ≤
      algebraMap ℝ (Matrix ι ι ℝ) (L / Real.sqrt k))
    (hfix : krausChannel D (balancedDensity S Z) = balancedDensity S Z) :
    realTrace (DyadicBalancedModel.balancedDyadicRoot m S Z *
      SpectralHighForcing.outputGram (balancedDensity_posDef hS hZ).isHermitian
        (c / Real.sqrt k) D) ≤
      2 * L ^ 2 * c ^ (1 / (2 : ℝ) ^ m - 2) * k ^ (1 - 1 / (2 : ℝ) ^ m) := by
  have ht : 0 < L / Real.sqrt k := div_pos hL (Real.sqrt_pos.mpr hk)
  have hε : 0 < c / Real.sqrt k := div_pos hc (Real.sqrt_pos.mpr hk)
  have hi := high_output_interpolation_le m hm D hD hS hZ ht.le hε hWP hcap hfix
  have hr := high_radius_le_budget hk hL hc
    (realTrace_nonneg (balancedDensity_posDef hS hZ).posSemidef) hRtrace hPtrace
  have ha : 0 < 2 * L ^ 2 := by positivity
  have he : 2 / (2 : ℝ) ^ m = 2 * (1 / (2 : ℝ) ^ m) := by ring
  have hweq : 2 * ((L / Real.sqrt k) / (c / Real.sqrt k)) ^ 2 * k =
      (2 * L ^ 2) * c ^ (-(2 : ℝ)) * k := by
    rw [cap_cutoff_ratio hk hc, Real.rpow_neg hc.le, Real.rpow_two]
    ring
  rw [hweq] at hi
  calc
    _ ≤ ((2 * L ^ 2) * c ^ (-(2 : ℝ)) * k) ^ (1 - 2 / (2 : ℝ) ^ m) *
        ((2 * L ^ 2) * c ^ (-(3 : ℝ) / 2) * Real.sqrt k) ^ (2 / (2 : ℝ) ^ m) := by
      apply hi.trans
      apply mul_le_mul_of_nonneg_left
      · apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        convert mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2) using 1
        ring
      · positivity
    _ = _ := by
      rw [he, high_endpoint_interpolation_identity ha hc hk]

end DyadicHighForcing
end MatrixSpencer
