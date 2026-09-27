import MatrixSpencer.MSManuscriptPolynomialQueryParameters

/-! Input-only precision bounds for the original square-MS acceptance
certificates and their saved supporting density.
-/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptPolynomialQueryAcceptance
open MSManuscriptPolynomialQueryParameters
local instance {m : Type*} [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}
set_option maxHeartbeats 800000

theorem radius_le {m N d : ℕ} (cfg : EpochConfig (Fin m) (Fin d))
    (hd : 0 < d) (hm : m ≤ N) :
    (MSManuscriptAcceptedEpoch.reportConfig cfg hd).radius ≤ acceptanceRadius N d := by
  have hs := MSManuscriptPolynomialMovementBounds.sqrt_le_add_one (Nat.cast_nonneg d)
  have hm' : (m:ℝ) ≤ N := Nat.cast_le.mpr hm
  have hb : cfg.epsilon*(m:ℝ) ≤ 1 := by
    have h := cfg.epsilon_small
    simp only [Fintype.card_fin] at h
    nlinarith
  have hp : 0 ≤ 2*(m:ℝ)+cfg.epsilon*m := by
    have he := cfg.epsilon_pos.le
    positivity
  change Real.sqrt (d:ℝ)*(2*(m:ℝ)+cfg.epsilon*m) ≤ _
  have hmul := mul_le_mul hs (show 2*(m:ℝ)+cfg.epsilon*m ≤ 2*(N:ℝ)+1 by linarith)
    hp (by positivity : (0:ℝ)≤d+1)
  simpa only [acceptanceRadius, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using hmul

theorem tolerance_inverse_le {m d : ℕ} (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0 < d) :
    (MSManuscriptNumericalAcceptance.tolerance (MSManuscriptAcceptedEpoch.reportConfig cfg hd))⁻¹ ≤ 100 := by
  have hs := MSManuscriptNumericalConfig.sqrt_count_ge_one cfg
  change (Real.sqrt (m:ℝ)/100)⁻¹ ≤ 100
  rw [inv_div]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hs)).mpr
  linarith

theorem valueTolerance_inverse_le {m d : ℕ} (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0 < d) :
    (MSManuscriptNumericalAcceptance.tolerance (MSManuscriptAcceptedEpoch.reportConfig cfg hd)/3)⁻¹ ≤ 300 := by
  have h := tolerance_inverse_le cfg hd
  rw [inv_div, div_eq_mul_inv]
  linarith

theorem anchorTolerance_inverse_le {m N d : ℕ} (cfg : EpochConfig (Fin m) (Fin d))
    (hd : 0 < d) (hm : m ≤ N) :
    (MSManuscriptCertificateReport.anchorTolerance
      (MSManuscriptAcceptedEpoch.reportConfig cfg hd).radius
      (MSManuscriptNumericalAcceptance.tolerance (MSManuscriptAcceptedEpoch.reportConfig cfg hd)))⁻¹ ≤
        anchorInv N d := by
  have hr := radius_le cfg hd hm
  have ht := tolerance_inverse_le cfg hd
  have ht0 := (MSManuscriptNumericalAcceptance.tolerance_pos
    (MSManuscriptAcceptedEpoch.reportConfig cfg hd)).le
  rw [MSManuscriptCertificateReport.anchorTolerance, inv_div, div_eq_mul_inv]
  have hb := mul_le_mul (show 3*((MSManuscriptAcceptedEpoch.reportConfig cfg hd).radius+1) ≤
      3*((acceptanceRadius N d:ℝ)+1) by linarith) ht (inv_nonneg.mpr ht0) (by positivity)
  convert hb using 1 <;> simp only [anchorInv, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one] <;> ring

end MatrixSpencer.MSManuscriptPolynomialQueryAcceptance
