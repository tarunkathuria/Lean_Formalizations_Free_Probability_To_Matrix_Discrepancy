import MatrixSpencer.DyadicBalancedModel
import MatrixSpencer.SpectralLowForcing

/-!
# Dyadic low-spectrum forcing from actual physical trace budgets

The two endpoint trace bounds are paired with the proved correlated
dyadic interpolation. No norm bound on the fractional weight, simultaneous
diagonalization, or curvature estimate is assumed.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer
namespace DyadicLowForcing
open DyadicBalancedModel SpectralLowForcing

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance dyadicLowForcingCStar : CStarAlgebra (Matrix n n ℂ) := {}

lemma dyadic_exponents_nonneg {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ 1 - 2 / (2 : ℝ) ^ m ∧ 0 ≤ 2 / (2 : ℝ) ^ m := by
  have hp : (2 : ℝ) ≤ 2 ^ m := by
    exact_mod_cast (show 2 ^ 1 ≤ 2 ^ m from Nat.pow_le_pow_right (by norm_num) hm)
  have hp0 : (0 : ℝ) < 2 ^ m := by positivity
  have hdiv : 2 / (2 : ℝ) ^ m ≤ 1 := (div_le_one hp0).mpr hp
  exact ⟨sub_nonneg.mpr hdiv, by positivity⟩

/-- A PSD test bounded by P inherits the W endpoint, without commuting with P. -/
lemma interpolated_trace_le (m : ℕ) (hm : 1 ≤ m)
    {S Z X : Matrix n n ℂ} (hS : S.PosSemidef) (hZ : Z.PosDef) (hX : X.PosSemidef)
    {k b : ℝ} (hk : 0 ≤ k)
    (hXP : X ≤ balancedDensity S Z)
    (hWP : realTrace (Z⁻¹ * balancedDensity S Z) ≤ k)
    (hRX : realTrace (balancedRoot S Z * X) ≤ b) :
    realTrace (balancedDyadicRoot m S Z * X) ≤
      k ^ (1 - 2 / (2 : ℝ) ^ m) * b ^ (2 / (2 : ℝ) ^ m) := by
  have hW := hZ.inv.posSemidef
  have hR := (balancedDyadicRoot_posSemidef 1 hS hZ)
  have hWX := (realTrace_mul_mono hW hXP).trans hWP
  have hexp := dyadic_exponents_nonneg hm
  apply (balancedDyadicRoot_trace_le m hm hS hZ hX).trans
  apply mul_le_mul
  · exact Real.rpow_le_rpow (realTrace_mul_nonneg hW hX) hWX hexp.1
  · exact Real.rpow_le_rpow (realTrace_mul_nonneg hR hX) hRX hexp.2
  · exact Real.rpow_nonneg (realTrace_mul_nonneg hR hX) _
  · exact Real.rpow_nonneg hk _

/-- The actual low-forcing estimate before choosing the cutoff scale. -/
theorem low_forcing_interpolated (m : ℕ) (hm : 1 ≤ m)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef)
    {k ε : ℝ} (hk : 0 < k) (hε : 0 < ε)
    (hfix : krausChannel D (balancedDensity S Z) = balancedDensity S Z)
    (hWP : realTrace (Z⁻¹ * balancedDensity S Z) ≤ k)
    (hRR : realTrace (balancedRoot S Z * balancedRoot S Z) ≤ k) :
    (∑ a, realTrace (balancedDyadicRoot m S Z *
      lowForce (balancedDensity_posDef hS hZ).isHermitian ε (D a) * balancedDensity S Z *
      lowForce (balancedDensity_posDef hS hZ).isHermitian ε (D a))) ≤
      4 * k ^ (1 - 2 / (2 : ℝ) ^ m) *
        (Real.sqrt (k * ε * realTrace (balancedDensity S Z))) ^ (2 / (2 : ℝ) ^ m) := by
  let P := balancedDensity S Z
  let R := balancedRoot S Z
  let Rm := balancedDyadicRoot m S Z
  have hP : P.PosDef := balancedDensity_posDef hS hZ
  have hR : R.PosSemidef := (balancedRoot_posDef hS hZ).posSemidef
  have hRm : Rm.PosSemidef := balancedDyadicRoot_posSemidef m hS.posSemidef hZ
  let Pl := SpectralCutoff.lowPart hP.isHermitian ε
  have hPl : Pl.PosSemidef := SpectralCutoff.lowPart_posSemidef hP.posSemidef ε
  have hPlP : Pl ≤ P := SpectralCutoff.lowPart_le hP.posSemidef ε
  have hPhi : (krausChannel D Pl).PosSemidef := channel_posSemidef D hPl
  have hPhiP : krausChannel D Pl ≤ P := (KrausContraction.channel_mono D hPlP).trans_eq hfix
  have hroot : Real.sqrt (realTrace (R * R) * ε * realTrace P) ≤
      Real.sqrt (k * ε * realTrace P) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRR hε.le)
      (realTrace_nonneg hP.posSemidef)
  have hRPl : realTrace (R * Pl) ≤ Real.sqrt (k * ε * realTrace P) :=
    (trace_lowPart_le R hR hP.posSemidef hε).trans hroot
  have hRPhi : realTrace (R * krausChannel D Pl) ≤ Real.sqrt (k * ε * realTrace P) :=
    (trace_channel_lowPart_le D hD hP hR hfix hε).trans hroot
  have hlow := interpolated_trace_le m hm hS.posSemidef hZ hPl hk.le hPlP hWP hRPl
  have hchannel := interpolated_trace_le m hm hS.posSemidef hZ hPhi hk.le hPhiP hWP hRPhi
  have henergy := low_forcing_intermediate D hD hP.posSemidef hRm hfix ε
  have he : (∑ a, realTrace (Rm * lowForce hP.isHermitian ε (D a) * P *
      lowForce hP.isHermitian ε (D a))) =
      ∑ a, realTrace (P * lowForce hP.isHermitian ε (D a) * Rm *
        lowForce hP.isHermitian ε (D a)) := by
    apply Finset.sum_congr rfl
    intro a _
    simpa only [Matrix.mul_assoc] using realTrace_mul_comm
      (Rm * lowForce hP.isHermitian ε (D a)) (P * lowForce hP.isHermitian ε (D a))
  change (∑ a, realTrace (Rm * lowForce hP.isHermitian ε (D a) * P *
      lowForce hP.isHermitian ε (D a))) ≤ _
  rw [he]
  change realTrace (Rm * Pl) ≤ _ at hlow
  change realTrace (Rm * krausChannel D Pl) ≤ _ at hchannel
  change (∑ a, realTrace (P * lowForce hP.isHermitian ε (D a) * Rm *
      lowForce hP.isHermitian ε (D a))) ≤ 2 * (realTrace (Rm * krausChannel D Pl) +
        realTrace (Rm * Pl)) at henergy
  dsimp only [P] at hlow hchannel henergy ⊢
  nlinarith

lemma interpolation_scale_identity {k c q : ℝ} (hk : 0 < k) (hc : 0 ≤ c) :
    k ^ (1 - 2 * q) * (Real.sqrt (k * c)) ^ (2 * q) = c ^ q * k ^ (1 - q) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (mul_nonneg hk.le hc)]
  rw [show (1 / 2 : ℝ) * (2 * q) = q by ring, Real.mul_rpow hk.le hc,
    ← mul_assoc, ← Real.rpow_add hk]
  rw [show 1 - 2 * q + q = 1 - q by ring, mul_comm]

/-- Choosing epsilon=c/sqrt(k) gives the dimension-free dyadic low-forcing budget. -/
theorem low_forcing_le (m : ℕ) (hm : 1 ≤ m)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef)
    {k c : ℝ} (hk : 0 < k) (hc : 0 < c)
    (hfix : krausChannel D (balancedDensity S Z) = balancedDensity S Z)
    (hP : realTrace (balancedDensity S Z) ≤ Real.sqrt k)
    (hWP : realTrace (Z⁻¹ * balancedDensity S Z) ≤ k)
    (hRR : realTrace (balancedRoot S Z * balancedRoot S Z) ≤ k) :
    (∑ a, realTrace (balancedDyadicRoot m S Z *
      lowForce (balancedDensity_posDef hS hZ).isHermitian (c / Real.sqrt k) (D a) *
      balancedDensity S Z *
      lowForce (balancedDensity_posDef hS hZ).isHermitian (c / Real.sqrt k) (D a))) ≤
      4 * c ^ (1 / (2 : ℝ) ^ m) * k ^ (1 - 1 / (2 : ℝ) ^ m) := by
  have hks : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hε : 0 < c / Real.sqrt k := div_pos hc hks
  have hinside : k * (c / Real.sqrt k) * realTrace (balancedDensity S Z) ≤ k * c := by
    have h := mul_le_mul_of_nonneg_left hP (show 0 ≤ k * (c / Real.sqrt k) by positivity)
    have he : k * (c / Real.sqrt k) * Real.sqrt k = k * c := by field_simp
    exact h.trans_eq he
  have hr := Real.rpow_le_rpow (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hinside)
    (dyadic_exponents_nonneg hm).2
  have hb := low_forcing_interpolated m hm D hD hS hZ hk hε hfix hWP hRR
  have hmul := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ 4 * k ^ (1 - 2 / (2 : ℝ) ^ m) by positivity)
  have he : 4 * k ^ (1 - 2 / (2 : ℝ) ^ m) * (Real.sqrt (k * c)) ^ (2 / (2 : ℝ) ^ m) =
      4 * c ^ (1 / (2 : ℝ) ^ m) * k ^ (1 - 1 / (2 : ℝ) ^ m) := by
    have h := interpolation_scale_identity (q := 1 / (2 : ℝ) ^ m) hk hc.le
    simp only [mul_one_div] at h
    nlinarith
  exact hb.trans (hmul.trans_eq he)

end DyadicLowForcing
end MatrixSpencer
