import MatrixSpencer.RectangularRidgeUniformRootJets

/-!
# Inverse-floor input bounds for the actual root-power calculation

For a positive density bounded above by the identity, the actual dyadic root has
norm at most one and its genuine first four line derivatives satisfy the common
power bound `(120 / μ)^r`, uniformly in the dyadic depth.
-/
open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeRootJetsInverseFloor
open RectangularRidgeRootJetBounds RectangularRidgeActualRootJets
open RectangularRidgeActualRootJetBounds RectangularRidgeUniformRootJets
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance ridgeRootJetsInverseFloorCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeRootJetsInverseFloorRealSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

lemma root_one (m : ℕ) : dyadicRoot m (1 : Matrix n n ℂ) = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [dyadicRoot_succ, ih, CFC.sqrt_one]

lemma root_norm_le_one (m : ℕ) {S : Matrix n n ℂ} (hS : S.PosSemidef) (hS1 : S ≤ 1) :
    ‖dyadicRoot m S‖ ≤ 1 := by
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ zero_le_one (dyadicRoot_posSemidef m hS).nonneg).mpr
  simpa only [map_one, root_one] using dyadicRoot_mono m hS1

lemma tracked_scale_le_inverse_power (m r : ℕ) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    μ ^ (exponent m - (r : ℝ)) ≤ μ⁻¹ ^ r := by
  rw [Real.rpow_sub hμ, Real.rpow_natCast]
  have h := div_le_div_of_nonneg_right
    (Real.rpow_le_one hμ.le hμ1 (exponent_pos m).le) (pow_nonneg hμ.le r)
  simpa only [one_div, inv_pow] using h

lemma jet_one_inverse_floor (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) (hX : ‖X‖ ≤ 1) :
    ‖jet 1 m S X‖ ≤ 120 / μ := by
  have h := (jet_one_norm_le m S X hS hμ hfloor hX).trans
    (by simpa only [Nat.cast_one] using tracked_scale_le_inverse_power m 1 hμ hμ1)
  simp only [pow_one] at h
  exact h.trans (by rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr hμ])

lemma jet_two_inverse_floor (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) (hX : ‖X‖ ≤ 1) :
    ‖jet 2 m S X‖ ≤ (120 / μ) ^ 2 := by
  have h := (jet_two_norm_le m S X hS hμ hfloor hX).trans
    (mul_le_mul_of_nonneg_left (tracked_scale_le_inverse_power m 2 hμ hμ1) (by norm_num))
  exact h.trans (by rw [div_eq_mul_inv, mul_pow]; nlinarith [sq_nonneg μ⁻¹])

lemma jet_three_inverse_floor (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) (hX : ‖X‖ ≤ 1) :
    ‖jet 3 m S X‖ ≤ (120 / μ) ^ 3 := by
  have h := (jet_three_norm_le m S X hS hμ hfloor hX).trans
    (mul_le_mul_of_nonneg_left (tracked_scale_le_inverse_power m 3 hμ hμ1) (by norm_num))
  exact h.trans (by rw [div_eq_mul_inv, mul_pow]; nlinarith [pow_nonneg (inv_nonneg.mpr hμ.le) 3])

lemma jet_four_inverse_floor (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) (hX : ‖X‖ ≤ 1) :
    ‖jet 4 m S X‖ ≤ (120 / μ) ^ 4 := by
  have h := (jet_four_norm_le m S X hS hμ hfloor hX).trans
    (mul_le_mul_of_nonneg_left (tracked_scale_le_inverse_power m 4 hμ hμ1) (by norm_num))
  exact h.trans (by rw [div_eq_mul_inv, mul_pow]; nlinarith [pow_nonneg (inv_nonneg.mpr hμ.le) 4])

lemma matrixPath_jet_bounds (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) (hX : ‖X‖ ≤ 1) :
    ‖iteratedDeriv 1 (matrixPath m S X) 0‖ ≤ (120 / μ) ^ 1 ∧
    ‖iteratedDeriv 2 (matrixPath m S X) 0‖ ≤ (120 / μ) ^ 2 ∧
    ‖iteratedDeriv 3 (matrixPath m S X) 0‖ ≤ (120 / μ) ^ 3 ∧
    ‖iteratedDeriv 4 (matrixPath m S X) 0‖ ≤ (120 / μ) ^ 4 := by
  simp only [← jet_coe _ m S X hS, herm_norm_coe, pow_one]
  exact ⟨jet_one_inverse_floor m S X hS hμ hμ1 hfloor hX,
    jet_two_inverse_floor m S X hS hμ hμ1 hfloor hX,
    jet_three_inverse_floor m S X hS hμ hμ1 hfloor hX,
    jet_four_inverse_floor m S X hS hμ hμ1 hfloor hX⟩

end MatrixSpencer.RectangularRidgeRootJetsInverseFloor
