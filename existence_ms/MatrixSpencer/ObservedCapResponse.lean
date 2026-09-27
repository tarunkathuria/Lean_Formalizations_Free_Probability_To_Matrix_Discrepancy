import MatrixSpencer.HighFrameBudget
import MatrixSpencer.ComplexInverseComparison
import MatrixSpencer.FrameTrace

/-!
# The observed response bound from the actual physical Gram cap

Every high/low budget is derived from the physical hypotheses. The response
operator is the inverse of the actual whitened full operator.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section
namespace MatrixSpencer
namespace ObservedCapResponse

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

/-- The actual full observed inverse in complex Hilbert--Schmidt coordinates. -/
def responseOperator (θ : ℝ) (P R : Matrix n n ℂ) (D : ι → Matrix n n ℂ) :
    Matrix (n × n) (n × n) ℂ :=
  (whitenedFull (jordanSuper P) (krausSuper D) (tsallisPairSuper θ P R))⁻¹

omit [DecidableEq ι] in
lemma responseOperator_posDef {θ : ℝ} (hθ : 0 < θ) {P R : Matrix n n ℂ}
    (hP : P.PosDef) (hR : R.PosDef) (D : ι → Matrix n n ℂ) :
    (responseOperator θ P R D).PosDef :=
  (whitenedFull_posDef (jordanSuper_posDef hP) (tsallisPairSuper_posDef hθ hP hR) _).inv

omit [DecidableEq ι] in
lemma responseOperator_le_regularizer {θ : ℝ} (hθ : 0 < θ) {P R : Matrix n n ℂ}
    (hP : P.PosDef) (hR : R.PosDef) (D : ι → Matrix n n ℂ) :
    responseOperator θ P R D ≤ (whitenedRegularizer (jordanSuper P) (tsallisPairSuper θ P R))⁻¹ :=
  ComplexInverseComparison.coupledOperator_inverse_le _
    (whitenedRegularizer_posDef (jordanSuper_posDef hP) (tsallisPairSuper_posDef hθ hP hR))

omit [DecidableEq ι] in
lemma responseOperator_le_coupled {θ : ℝ} (hθ : 0 < θ) {P R : Matrix n n ℂ}
    (hP : P.PosDef) (hR : R.PosDef) (D : ι → Matrix n n ℂ) :
    responseOperator θ P R D ≤ 1 + whitenedChannel (jordanSuper P) (krausSuper D) *
      (whitenedRegularizer (jordanSuper P) (tsallisPairSuper θ P R))⁻¹ *
        (whitenedChannel (jordanSuper P) (krausSuper D))ᴴ :=
  ComplexInverseComparison.coupled_inverse_domination _
    (whitenedRegularizer_posDef (jordanSuper_posDef hP) (tsallisPairSuper_posDef hθ hP hR))

lemma quadratic_add_le {m : Type*} [Fintype m] {Q : Matrix m m ℂ} (hQ : Q.PosSemidef)
    (x y : m → ℂ) :
    ComplexInverseComparison.quadratic Q (x + y) ≤
      2 * (ComplexInverseComparison.quadratic Q x + ComplexInverseComparison.quadratic Q y) := by
  have hpar : ComplexInverseComparison.quadratic Q (x + y) +
      ComplexInverseComparison.quadratic Q (x - y) =
      2 * (ComplexInverseComparison.quadratic Q x + ComplexInverseComparison.quadratic Q y) := by
    simp only [ComplexInverseComparison.quadratic, ComplexInverseComparison.pairing,
      Matrix.mulVec_add, Matrix.mulVec_sub, star_add, star_sub, dotProduct_add, dotProduct_sub,
      add_dotProduct, sub_dotProduct, map_add, map_sub]
    ring
  linarith [ComplexInverseComparison.quadratic_nonneg hQ (x - y)]

omit [Fintype ι] [DecidableEq ι] in
lemma forceSynthesis_add (P : Matrix n n ℂ) (E F : ι → Matrix n n ℂ) :
    jordanForceSynthesis P (fun a => E a + F a) = jordanForceSynthesis P E + jordanForceSynthesis P F := by
  rw [jordanForceSynthesis, show krausSynthesis (fun a => E a + F a) = krausSynthesis E + krausSynthesis F from rfl,
    Matrix.mul_add, smul_add]
  rfl

omit [DecidableEq ι] in
lemma frame_trace_add_le (P : Matrix n n ℂ) (E F : ι → Matrix n n ℂ)
    {Q : Matrix (n × n) (n × n) ℂ} (hQ : Q.PosSemidef) :
    realTrace (jordanForceFrame P (fun a => E a + F a) * Q) ≤
      2 * (realTrace (jordanForceFrame P E * Q) + realTrace (jordanForceFrame P F * Q)) := by
  simp only [jordanForceFrame, frameTrace_eq_sum, forceSynthesis_add,
    Matrix.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib, mul_add]
  apply Finset.sum_le_sum
  intro a _
  simpa only [ComplexInverseComparison.quadratic, ComplexInverseComparison.pairing, mul_add]
    using quadratic_add_le hQ (fun i => jordanForceSynthesis P E i a) (fun i => jordanForceSynthesis P F i a)

lemma force_high_add_low {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) (D : Matrix n n ℂ) :
    SpectralHighForcing.highForce hP ε D + SpectralLowForcing.lowForce hP ε D = D := by
  rw [SpectralLowForcing.lowForce_eq_sub]
  exact add_sub_cancel _ _

lemma trace_weighted_output_le (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P R : Matrix n n ℂ} (hP : P.PosSemidef) (hR : R.PosSemidef)
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε)
    (hcap : physicalRealGram P D ≤ algebraMap ℝ (Matrix ι ι ℝ) t)
    (hfix : krausChannel D P = P) :
    realTrace (R * SpectralHighForcing.outputGram hP.isHermitian ε D) ≤
      2 * Real.sqrt (realTrace (R * R) * t * (t / ε) ^ 3 * realTrace P) := by
  have hc := SpectralLowForcing.trace_mul_le_sqrt hR (SpectralHighForcing.outputGram_posSemidef hP ε D hD)
  have hs := SpectralHighForcing.outputGram_trace_sq_le D hD hP ht hε hcap hfix
  have hb := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hs (realTrace_mul_nonneg hR hR))
  apply (hc.trans hb).trans_eq
  rw [show realTrace (R * R) * (4 * t * (t / ε) ^ 3 * realTrace P) =
    4 * (realTrace (R * R) * t * (t / ε) ^ 3 * realTrace P) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

lemma high_response_le (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) {P R : Matrix n n ℂ} (hP : P.PosDef) (hR : R.PosDef)
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε)
    (hcap : physicalRealGram P D ≤ algebraMap ℝ (Matrix ι ι ℝ) t)
    (hfix : krausChannel D P = P) :
    realTrace (jordanForceFrame P (fun a => SpectralHighForcing.highForce hP.isHermitian ε (D a)) *
      responseOperator θ P R D) ≤ realTrace P + 2 * θ⁻¹ *
        Real.sqrt (realTrace (R * R) * t * (t / ε) ^ 3 * realTrace P) := by
  let E := fun a => SpectralHighForcing.highForce hP.isHermitian ε (D a)
  have hE : ∀ a, (E a).IsHermitian := fun a => SpectralHighForcing.highForce_hermitian hP.isHermitian (hD a) ε
  have h := realTrace_mul_mono (jordanForceFrame_posSemidef P E) (responseOperator_le_coupled hθ hP hR D)
  rw [Matrix.mul_add, Matrix.mul_one, realTrace_add, jordanForceFrame_coupling_pairing hθ hP hR D E hD hE] at h
  have he : (∑ a, realTrace (R * krausChannel D (E a) * P * krausChannel D (E a))) =
      realTrace (R * SpectralHighForcing.outputGram hP.isHermitian ε D) := by
    simp only [SpectralHighForcing.outputGram, Matrix.mul_sum, realTrace_sum, Matrix.mul_assoc, E]
  rw [he] at h
  have hf := HighFrameBudget.high_frame_trace_le hP D hD hfix ε
  have hw := mul_le_mul_of_nonneg_left (trace_weighted_output_le D hD hP.posSemidef hR.posSemidef ht hε hcap hfix)
    (inv_nonneg.mpr hθ.le)
  dsimp only [E] at h
  nlinarith

lemma low_response_le (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) {P R : Matrix n n ℂ} (hP : P.PosDef) (hR : R.PosDef)
    (hfix : krausChannel D P = P) {ε : ℝ} (hε : 0 < ε) :
    realTrace (jordanForceFrame P (fun a => SpectralLowForcing.lowForce hP.isHermitian ε (D a)) *
      responseOperator θ P R D) ≤ 4 * θ⁻¹ * Real.sqrt (realTrace (R * R) * ε * realTrace P) := by
  let E := fun a => SpectralLowForcing.lowForce hP.isHermitian ε (D a)
  have hE : ∀ a, (E a).IsHermitian := fun a => SpectralLowForcing.lowForce_hermitian hP.isHermitian (hD a) ε
  have h := realTrace_mul_mono (jordanForceFrame_posSemidef P E) (responseOperator_le_regularizer hθ hP hR D)
  rw [jordanForceFrame_regularizer_pairing hθ hP hR E hE] at h
  have hw := mul_le_mul_of_nonneg_left (SpectralLowForcing.low_forcing_le D hD hP hR.posSemidef hfix hε)
    (inv_nonneg.mpr hθ.le)
  have he : (∑ a, realTrace (R * E a * P * E a)) = ∑ a, realTrace (P * E a * R * E a) := by
    apply Finset.sum_congr rfl
    intro a _
    simpa only [Matrix.mul_assoc] using realTrace_mul_comm (R * E a) (P * E a)
  rw [he] at h
  dsimp only [E] at h
  nlinarith

/-- The physical Gram cap implies the full observed response estimate with an arbitrary cutoff. -/
theorem response_trace_le (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) {P R : Matrix n n ℂ} (hP : P.PosDef) (hR : R.PosDef)
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε)
    (hcap : physicalRealGram P D ≤ algebraMap ℝ (Matrix ι ι ℝ) t)
    (hfix : krausChannel D P = P) :
    realTrace (jordanForceFrame P D * responseOperator θ P R D) ≤
      2 * realTrace P + θ⁻¹ *
        (8 * Real.sqrt (realTrace (R * R) * ε * realTrace P) +
          4 * Real.sqrt (realTrace (R * R) * t * (t / ε) ^ 3 * realTrace P)) := by
  have htri := frame_trace_add_le P
    (fun a => SpectralHighForcing.highForce hP.isHermitian ε (D a))
    (fun a => SpectralLowForcing.lowForce hP.isHermitian ε (D a))
    (responseOperator_posDef hθ hP hR D).posSemidef
  simp only [force_high_add_low hP.isHermitian ε] at htri
  have hh := high_response_le D hD hθ hP hR ht hε hcap hfix
  have hl := low_response_le D hD hθ hP hR hfix hε
  nlinarith

/-- Taking cutoff equal to the actual cap scale gives the optimized square-root budget. -/
theorem response_trace_le_budget (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) {P R : Matrix n n ℂ} (hP : P.PosDef) (hR : R.PosDef)
    {k L : ℝ} (hk : 0 < k) (hL : 0 < L)
    (hPtrace : realTrace P ≤ Real.sqrt k) (hRtrace : realTrace (R * R) ≤ k)
    (hcap : physicalRealGram P D ≤ algebraMap ℝ (Matrix ι ι ℝ) (L / Real.sqrt k))
    (hfix : krausChannel D P = P) :
    realTrace (jordanForceFrame P D * responseOperator θ P R D) ≤
      (2 + 12 * Real.sqrt L / θ) * Real.sqrt k := by
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have ht : 0 < L / Real.sqrt k := div_pos hL hs
  have h := response_trace_le D hD hθ hP hR ht.le ht hcap hfix
  rw [div_self ht.ne', one_pow, mul_one] at h
  have hprod : realTrace (R * R) * (L / Real.sqrt k) * realTrace P ≤ k * L := by
    have hm := mul_le_mul hRtrace hPtrace (realTrace_nonneg hP.posSemidef) hk.le
    have hh := mul_le_mul_of_nonneg_right hm ht.le
    have he : (k * Real.sqrt k) * (L / Real.sqrt k) = k * L := by
      field_simp
    rw [he] at hh
    convert hh using 1; ring
  have hrad : Real.sqrt (realTrace (R * R) * (L / Real.sqrt k) * realTrace P) ≤
      Real.sqrt L * Real.sqrt k := by
    have hr := Real.sqrt_le_sqrt hprod
    rw [Real.sqrt_mul hk.le] at hr
    exact hr.trans_eq (mul_comm _ _)
  have hw := mul_le_mul_of_nonneg_left hrad (inv_nonneg.mpr hθ.le)
  calc
    _ ≤ 2 * Real.sqrt k + 12 * θ⁻¹ * (Real.sqrt L * Real.sqrt k) := by nlinarith
    _ = _ := by ring

end ObservedCapResponse
end MatrixSpencer
