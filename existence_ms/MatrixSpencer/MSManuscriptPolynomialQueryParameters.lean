import MatrixSpencer.MSManuscriptPolynomialQueryCurvature

/-! Polynomial inverse precisions and paid-preparation iteration budgets
for the unchanged square-MS query and controller scalar formulas. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptPolynomialQueryParameters
open MSManuscriptPolynomialQueryCurvature
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

def thresholdInv (N : ℕ) : ℕ := N+1
def precisionInv (N : ℕ) : ℕ := 128*(N+1)^2
def slopeStepInv (N d : ℕ) : ℕ := 32768+(second N d+1)*precisionInv N
def valueInv (N d : ℕ) : ℕ := 4*precisionInv N*slopeStepInv N d
def paidInv (N d : ℕ) : ℕ := 32768+4*curvature N d*thresholdInv N
def preparation (N d : ℕ) : ℕ := N*paidInv N d+2
def cleanupInv (N : ℕ) : ℕ := 131072*(N+1)
def acceptanceRadius (N d : ℕ) : ℕ := (d+1)*(2*N+1)
def anchorInv (N d : ℕ) : ℕ := 300*(acceptanceRadius N d+1)

theorem min_inverse_le {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA : a⁻¹ ≤ A) (hB : b⁻¹ ≤ B) : (min a b)⁻¹ ≤ A+B := by
  have hA0 := (inv_pos.mpr ha).le.trans hA
  have hB0 := (inv_pos.mpr hb).le.trans hB
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h]
    linarith

theorem threshold_inverse_le {m N : ℕ} (hm : m ≤ N) :
    (4096/Real.sqrt (m:ℝ))⁻¹ ≤ thresholdInv N := by
  rw [inv_div]
  have hs := MSManuscriptPolynomialMovementBounds.sqrt_le_add_one (Nat.cast_nonneg m)
  have hm' : (m:ℝ) ≤ N := Nat.cast_le.mpr hm
  simp only [thresholdInv, Nat.cast_add, Nat.cast_one]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<4096)).mpr
  linarith

theorem topPrecision_inverse_le {k N : ℕ} (hk : k ≤ N) {t : ℝ}
    (ht : 0 < t) (hti : t⁻¹ ≤ thresholdInv N) :
    (MSManuscriptGammaMatrix.topPrecision k t)⁻¹ ≤ precisionInv N := by
  rw [MSManuscriptGammaMatrix.topPrecision, inv_div, div_eq_mul_inv]
  have hk' : (k:ℝ) ≤ N := Nat.cast_le.mpr hk
  have hm := mul_le_mul_of_nonneg_left hti (show (0:ℝ)≤128*k by positivity)
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  norm_num only [thresholdInv, precisionInv, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_one] at hm ⊢
  nlinarith

theorem slopeStep_inverse_le {N d : ℕ} {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η)
    (hLb : L ≤ second N d) (hηb : η⁻¹ ≤ precisionInv N) :
    (MSManuscriptGammaDifference.stepSize (1/8192) L η)⁻¹ ≤ slopeStepInv N d := by
  have hB : (η/(L+1))⁻¹ ≤ (second N d+1 : ℕ)*(precisionInv N:ℝ) := by
    rw [inv_div, div_eq_mul_inv]
    exact mul_le_mul (by exact_mod_cast add_le_add_right hLb 1) hηb
      (inv_nonneg.mpr hη.le) (by positivity)
  have h := min_inverse_le (by norm_num : (0:ℝ)<(1/8192)/4)
    (div_pos hη (by linarith : 0<L+1)) (by norm_num : (((1/8192)/4:ℝ))⁻¹≤32768) hB
  simpa only [MSManuscriptGammaDifference.stepSize, slopeStepInv,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h

theorem valueTolerance_inverse_le {N d : ℕ} {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η)
    (hLb : L ≤ second N d) (hηb : η⁻¹ ≤ precisionInv N) :
    (MSManuscriptGammaDifference.valueTolerance (1/8192) L η)⁻¹ ≤ valueInv N d := by
  have hs := slopeStep_inverse_le hL hη hLb hηb
  have hs0 := MSManuscriptGammaDifference.stepSize_pos (by norm_num : (0:ℝ)<1/8192) hL hη
  have hm := mul_le_mul hηb hs (inv_nonneg.mpr hs0.le) (Nat.cast_nonneg _)
  have h4 := mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤4)
  convert h4 using 1 <;>
    simp only [MSManuscriptGammaDifference.valueTolerance, inv_div, _root_.mul_inv_rev,
      div_eq_mul_inv, valueInv, Nat.cast_mul, Nat.cast_ofNat] <;> ring

theorem paidSize_inverse_le {m N d : ℕ} (P : MSManuscriptSupportedGamma.Parameters m d)
    (hP : P.Valid) (hδ : P.floor = 1/8192)
    (hC : MSManuscriptSupportedPaid.curvatureBudget P ≤ curvature N d)
    (ht : P.threshold⁻¹ ≤ thresholdInv N) :
    (MSManuscriptSupportedPaid.paidSize P)⁻¹ ≤ paidInv N d := by
  have hcur := MSManuscriptSupportedPaid.curvatureBudget_pos P hP
  have hti0 : 0 ≤ P.threshold⁻¹ := inv_nonneg.mpr hP.2.2.2.2.2.1.le
  have hB : (P.threshold/(4*MSManuscriptSupportedPaid.curvatureBudget P))⁻¹ ≤
      4*(curvature N d:ℝ)*thresholdInv N := by
    rw [inv_div, div_eq_mul_inv]
    gcongr
  have h := min_inverse_le (by rw [hδ]; norm_num : 0<P.floor/4)
    (div_pos hP.2.2.2.2.2.1 (by positivity))
    (by rw [hδ]; norm_num : (P.floor/4)⁻¹≤32768) hB
  simpa only [MSManuscriptSupportedPaid.paidSize, paidInv, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat] using h

theorem preparation_budget_le {m N d : ℕ} (P : MSManuscriptSupportedGamma.Parameters m d)
    (hP : P.Valid) (hm : m ≤ N)
    (hpi : (MSManuscriptSupportedPaid.paidSize P)⁻¹ ≤ paidInv N d) :
    MSManuscriptSupportedPreparation.budget P ≤ preparation N d := by
  have hp := MSManuscriptSupportedPaid.paidSize_pos P hP
  have hnum : (m:ℝ)/MSManuscriptSupportedPaid.paidSize P ≤ (N:ℝ)*paidInv N d := by
    rw [div_eq_mul_inv]
    exact mul_le_mul (Nat.cast_le.mpr hm) hpi (inv_nonneg.mpr hp.le) (Nat.cast_nonneg _)
  have hc := Nat.ceil_lt_add_one (div_nonneg (Nat.cast_nonneg m) hp.le)
  apply (Nat.cast_le (α:=ℝ)).mp
  unfold MSManuscriptSupportedPreparation.budget MSManuscriptPreparationRun.budget preparation
  push_cast
  linarith

theorem cleanupTolerance_inverse_le {k N : ℕ} (hk : k ≤ N) :
    (MSManuscriptCleanupParameters.tolerance k (1/8192))⁻¹ ≤ cleanupInv N := by
  rw [MSManuscriptCleanupParameters.tolerance, inv_div]
  have hk' : (k:ℝ) ≤ N := Nat.cast_le.mpr hk
  norm_num [cleanupInv]
  linarith

end MatrixSpencer.MSManuscriptPolynomialQueryParameters
