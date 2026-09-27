import MatrixSpencer.DyadicHighForcing
import MatrixSpencer.DyadicLowForcing

/-! Observed response of the explicit dyadic curvature model.
The reparameterized two-sided operator is exact; no equality between model
curvature and the actual regularizer Hessian is asserted. -/

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer
namespace DyadicObservedCapResponse

variable {n ι : Type*} [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
local instance observedDyadicCStar : CStarAlgebra (Matrix n n ℂ) := {}

lemma balancedInverseModelSuper_eq_pair (m : ℕ) (η : ℝ) (S Z : Matrix n n ℂ) :
    DyadicBalancedModel.balancedInverseModelSuper m η⁻¹ S Z =
      tsallisPairSuper η (balancedDensity S Z) (DyadicBalancedModel.balancedDyadicRoot m S Z) := rfl

/-- The dyadic coefficient p/(2 theta) is exactly the effective square-root coefficient. -/
lemma balancedInverseModelSuper_eq_dyadic_pair (m : ℕ) {θ : ℝ} (hθ : θ ≠ 0)
    (S Z : Matrix n n ℂ) :
    DyadicBalancedModel.balancedInverseModelSuper m (((2 ^ m : ℕ) : ℝ) / (2 * θ)) S Z =
      tsallisPairSuper (2 * θ * (1 / (2 : ℝ) ^ m))
        (balancedDensity S Z) (DyadicBalancedModel.balancedDyadicRoot m S Z) := by
  have hc : ((2 ^ m : ℕ) : ℝ) / (2 * θ) = (2 * θ * (1 / (2 : ℝ) ^ m))⁻¹ := by
    push_cast
    field_simp
  rw [hc, balancedInverseModelSuper_eq_pair]

omit [DecidableEq ι] in
/-- The reused response is the inverse of the actual whitened model operator. -/
lemma responseOperator_eq_model (m : ℕ) {θ : ℝ} (hθ : θ ≠ 0)
    (S Z : Matrix n n ℂ) (D : ι → Matrix n n ℂ) :
    ObservedCapResponse.responseOperator (2 * θ * (1 / (2 : ℝ) ^ m))
      (balancedDensity S Z) (DyadicBalancedModel.balancedDyadicRoot m S Z) D =
      (whitenedFull (jordanSuper (balancedDensity S Z)) (krausSuper D)
        (DyadicBalancedModel.balancedInverseModelSuper m
          (((2 ^ m : ℕ) : ℝ) / (2 * θ)) S Z))⁻¹ := by
  rw [balancedInverseModelSuper_eq_dyadic_pair m hθ]
  rfl

/-- High response uses the full inverse bound and the actual high-output estimate. -/
lemma high_response_le (m : ℕ) (hm : 1 ≤ m)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {η : ℝ} (hη : 0 < η) {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef)
    {k L c : ℝ} (hk : 0 < k) (hL : 0 < L) (hc : 0 < c)
    (hPtrace : realTrace (balancedDensity S Z) ≤ Real.sqrt k)
    (hRtrace : realTrace (balancedRoot S Z * balancedRoot S Z) ≤ k)
    (hWP : realTrace (Z⁻¹ * balancedDensity S Z) ≤ k)
    (hcap : physicalRealGram (balancedDensity S Z) D ≤
      algebraMap ℝ (Matrix ι ι ℝ) (L / Real.sqrt k))
    (hfix : krausChannel D (balancedDensity S Z) = balancedDensity S Z) :
    realTrace (jordanForceFrame (balancedDensity S Z)
      (fun a => SpectralHighForcing.highForce (balancedDensity_posDef hS hZ).isHermitian
        (c / Real.sqrt k) (D a)) *
      ObservedCapResponse.responseOperator η (balancedDensity S Z)
        (DyadicBalancedModel.balancedDyadicRoot m S Z) D) ≤
      Real.sqrt k + η⁻¹ * (2 * L ^ 2 * c ^ (1 / (2 : ℝ) ^ m - 2) *
        k ^ (1 - 1 / (2 : ℝ) ^ m)) := by
  let P := balancedDensity S Z
  let R := DyadicBalancedModel.balancedDyadicRoot m S Z
  have hP : P.PosDef := balancedDensity_posDef hS hZ
  have hR : R.PosDef := DyadicBalancedModel.balancedDyadicRoot_posDef m hS hZ
  let E := fun a => SpectralHighForcing.highForce hP.isHermitian (c / Real.sqrt k) (D a)
  have hE : ∀ a, (E a).IsHermitian := fun a =>
    SpectralHighForcing.highForce_hermitian hP.isHermitian (hD a) _
  have h := realTrace_mul_mono (jordanForceFrame_posSemidef P E)
    (ObservedCapResponse.responseOperator_le_coupled hη hP hR D)
  rw [Matrix.mul_add, Matrix.mul_one, realTrace_add,
    jordanForceFrame_coupling_pairing hη hP hR D E hD hE] at h
  have he : (∑ a, realTrace (R * krausChannel D (E a) * P * krausChannel D (E a))) =
      realTrace (R * SpectralHighForcing.outputGram hP.isHermitian (c / Real.sqrt k) D) := by
    simp only [SpectralHighForcing.outputGram, Matrix.mul_sum, realTrace_sum, Matrix.mul_assoc, E]
  rw [he] at h
  have hf := (HighFrameBudget.high_frame_trace_le hP D hD hfix (c / Real.sqrt k)).trans hPtrace
  have hw := mul_le_mul_of_nonneg_left
    (DyadicHighForcing.high_output_trace_le_budget m hm D hD hS hZ hk hL hc
      hPtrace hRtrace hWP hcap hfix) (inv_nonneg.mpr hη.le)
  exact h.trans (add_le_add hf hw)

/-- Low response uses the regularizer-only inverse bound and the actual low-force sum. -/
lemma low_response_le (m : ℕ) (hm : 1 ≤ m)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {η : ℝ} (hη : 0 < η) {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef)
    {k c : ℝ} (hk : 0 < k) (hc : 0 < c)
    (hPtrace : realTrace (balancedDensity S Z) ≤ Real.sqrt k)
    (hRtrace : realTrace (balancedRoot S Z * balancedRoot S Z) ≤ k)
    (hWP : realTrace (Z⁻¹ * balancedDensity S Z) ≤ k)
    (hfix : krausChannel D (balancedDensity S Z) = balancedDensity S Z) :
    realTrace (jordanForceFrame (balancedDensity S Z)
      (fun a => SpectralLowForcing.lowForce (balancedDensity_posDef hS hZ).isHermitian
        (c / Real.sqrt k) (D a)) *
      ObservedCapResponse.responseOperator η (balancedDensity S Z)
        (DyadicBalancedModel.balancedDyadicRoot m S Z) D) ≤
      η⁻¹ * (4 * c ^ (1 / (2 : ℝ) ^ m) * k ^ (1 - 1 / (2 : ℝ) ^ m)) := by
  let P := balancedDensity S Z
  let R := DyadicBalancedModel.balancedDyadicRoot m S Z
  have hP : P.PosDef := balancedDensity_posDef hS hZ
  have hR : R.PosDef := DyadicBalancedModel.balancedDyadicRoot_posDef m hS hZ
  let E := fun a => SpectralLowForcing.lowForce hP.isHermitian (c / Real.sqrt k) (D a)
  have hE : ∀ a, (E a).IsHermitian := fun a =>
    SpectralLowForcing.lowForce_hermitian hP.isHermitian (hD a) _
  have h := realTrace_mul_mono (jordanForceFrame_posSemidef P E)
    (ObservedCapResponse.responseOperator_le_regularizer hη hP hR D)
  rw [jordanForceFrame_regularizer_pairing hη hP hR E hE] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (DyadicLowForcing.low_forcing_le m hm D hD hS hZ hk hc hfix hPtrace hWP hRtrace)
    (inv_nonneg.mpr hη.le))

/-- The cap-response estimate with a freely chosen positive cutoff scale. -/
theorem response_trace_le (m : ℕ) (hm : 1 ≤ m)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {η : ℝ} (hη : 0 < η) {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef)
    {k L c : ℝ} (hk : 0 < k) (hL : 0 < L) (hc : 0 < c)
    (hPtrace : realTrace (balancedDensity S Z) ≤ Real.sqrt k)
    (hRtrace : realTrace (balancedRoot S Z * balancedRoot S Z) ≤ k)
    (hWP : realTrace (Z⁻¹ * balancedDensity S Z) ≤ k)
    (hcap : physicalRealGram (balancedDensity S Z) D ≤
      algebraMap ℝ (Matrix ι ι ℝ) (L / Real.sqrt k))
    (hfix : krausChannel D (balancedDensity S Z) = balancedDensity S Z) :
    realTrace (jordanForceFrame (balancedDensity S Z) D *
      ObservedCapResponse.responseOperator η (balancedDensity S Z)
        (DyadicBalancedModel.balancedDyadicRoot m S Z) D) ≤
      2 * Real.sqrt k + η⁻¹ *
        (8 * c ^ (1 / (2 : ℝ) ^ m) + 4 * L ^ 2 * c ^ (1 / (2 : ℝ) ^ m - 2)) *
          k ^ (1 - 1 / (2 : ℝ) ^ m) := by
  have hP := balancedDensity_posDef hS hZ
  have hR := DyadicBalancedModel.balancedDyadicRoot_posDef m hS hZ
  have htri := ObservedCapResponse.frame_trace_add_le (balancedDensity S Z)
    (fun a => SpectralHighForcing.highForce hP.isHermitian (c / Real.sqrt k) (D a))
    (fun a => SpectralLowForcing.lowForce hP.isHermitian (c / Real.sqrt k) (D a))
    (ObservedCapResponse.responseOperator_posDef hη hP hR D).posSemidef
  simp only [ObservedCapResponse.force_high_add_low hP.isHermitian (c / Real.sqrt k)] at htri
  have hh := high_response_le m hm D hD hη hS hZ hk hL hc hPtrace hRtrace hWP hcap hfix
  have hl := low_response_le m hm D hD hη hS hZ hk hc hPtrace hRtrace hWP hfix
  nlinarith

/-- Taking the cutoff scale equal to the Gram cap scale gives the optimized model budget. -/
theorem response_trace_le_optimized (m : ℕ) (hm : 1 ≤ m)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {η : ℝ} (hη : 0 < η) {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef)
    {k L : ℝ} (hk : 0 < k) (hL : 0 < L)
    (hPtrace : realTrace (balancedDensity S Z) ≤ Real.sqrt k)
    (hRtrace : realTrace (balancedRoot S Z * balancedRoot S Z) ≤ k)
    (hWP : realTrace (Z⁻¹ * balancedDensity S Z) ≤ k)
    (hcap : physicalRealGram (balancedDensity S Z) D ≤
      algebraMap ℝ (Matrix ι ι ℝ) (L / Real.sqrt k))
    (hfix : krausChannel D (balancedDensity S Z) = balancedDensity S Z) :
    realTrace (jordanForceFrame (balancedDensity S Z) D *
      ObservedCapResponse.responseOperator η (balancedDensity S Z)
        (DyadicBalancedModel.balancedDyadicRoot m S Z) D) ≤
      2 * Real.sqrt k + 12 * η⁻¹ * L ^ (1 / (2 : ℝ) ^ m) * k ^ (1 - 1 / (2 : ℝ) ^ m) := by
  have h := response_trace_le m hm D hD hη hS hZ hk hL hL hPtrace hRtrace hWP hcap hfix
  have he : L ^ 2 * L ^ (1 / (2 : ℝ) ^ m - 2) = L ^ (1 / (2 : ℝ) ^ m) := by
    rw [← Real.rpow_two, ← Real.rpow_add hL,
      show (2 : ℝ) + (1 / (2 : ℝ) ^ m - 2) = 1 / (2 : ℝ) ^ m by ring]
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [show 4 * L ^ 2 * L ^ (1 / (2 : ℝ) ^ m - 2) =
        4 * (L ^ 2 * L ^ (1 / (2 : ℝ) ^ m - 2)) by ring, he]
      ring

/-- The final physical cap bound for the dyadic inverse-curvature model, q=1/2^m. -/
theorem response_trace_le_dyadic (m : ℕ) (hm : 1 ≤ m)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef)
    {k L : ℝ} (hk : 0 < k) (hL : 0 < L)
    (hPtrace : realTrace (balancedDensity S Z) ≤ Real.sqrt k)
    (hRtrace : realTrace (balancedRoot S Z * balancedRoot S Z) ≤ k)
    (hWP : realTrace (Z⁻¹ * balancedDensity S Z) ≤ k)
    (hcap : physicalRealGram (balancedDensity S Z) D ≤
      algebraMap ℝ (Matrix ι ι ℝ) (L / Real.sqrt k))
    (hfix : krausChannel D (balancedDensity S Z) = balancedDensity S Z) :
    realTrace (jordanForceFrame (balancedDensity S Z) D *
      ObservedCapResponse.responseOperator (2 * θ * (1 / (2 : ℝ) ^ m)) (balancedDensity S Z)
        (DyadicBalancedModel.balancedDyadicRoot m S Z) D) ≤
      2 * Real.sqrt k + (6 * L ^ (1 / (2 : ℝ) ^ m) / (θ * (1 / (2 : ℝ) ^ m))) *
        k ^ (1 - 1 / (2 : ℝ) ^ m) := by
  have hη : 0 < 2 * θ * (1 / (2 : ℝ) ^ m) := by positivity
  have h := response_trace_le_optimized m hm D hD hη hS hZ hk hL hPtrace hRtrace hWP hcap hfix
  apply h.trans_eq
  congr 1
  field_simp
  norm_num

/-- The same final budget stated with the explicit model matrix, with no parameter alias. -/
theorem model_response_trace_le (m : ℕ) (hm : 1 ≤ m)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef)
    {k L : ℝ} (hk : 0 < k) (hL : 0 < L)
    (hPtrace : realTrace (balancedDensity S Z) ≤ Real.sqrt k)
    (hRtrace : realTrace (balancedRoot S Z * balancedRoot S Z) ≤ k)
    (hWP : realTrace (Z⁻¹ * balancedDensity S Z) ≤ k)
    (hcap : physicalRealGram (balancedDensity S Z) D ≤
      algebraMap ℝ (Matrix ι ι ℝ) (L / Real.sqrt k))
    (hfix : krausChannel D (balancedDensity S Z) = balancedDensity S Z) :
    realTrace (jordanForceFrame (balancedDensity S Z) D *
      (whitenedFull (jordanSuper (balancedDensity S Z)) (krausSuper D)
        (DyadicBalancedModel.balancedInverseModelSuper m
          (((2 ^ m : ℕ) : ℝ) / (2 * θ)) S Z))⁻¹) ≤
      2 * Real.sqrt k + (6 * L ^ (1 / (2 : ℝ) ^ m) / (θ * (1 / (2 : ℝ) ^ m))) *
        k ^ (1 - 1 / (2 : ℝ) ^ m) := by
  rw [← responseOperator_eq_model m hθ.ne']
  exact response_trace_le_dyadic m hm D hD hθ hS hZ hk hL hPtrace hRtrace hWP hcap hfix

end DyadicObservedCapResponse
end MatrixSpencer
