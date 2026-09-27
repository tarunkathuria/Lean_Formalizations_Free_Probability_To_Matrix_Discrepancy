import MatrixSpencer.RectangularRidgeActualRootJets

/-!
# Quantitative bounds for genuine dyadic-root line derivatives

These are bounds on the actual iterated derivatives of the positive root along
an affine Hermitian line. Every derivative is identified by differentiating the
square equation, then estimated using the actual positive Sylvester inverse.
-/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
set_option maxHeartbeats 2000000
namespace MatrixSpencer.RectangularRidgeActualRootJetBounds
open RectangularRidgeRootJetBounds RectangularRidgeActualRootJets
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance ridgeActualRootJetBoundsCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeActualRootJetBoundsRealSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

@[simp] lemma herm_norm_coe (W : Herm (n := n)) : ‖(W : Matrix n n ℂ)‖ = ‖W‖ := rfl

lemma solution_norm_le (Q W : Herm (n := n)) (hQ : (Q : Matrix n n ℂ).PosDef)
    {a : ℝ} (ha : 0 < a) (hfloor : a • (1 : Matrix n n ℂ) ≤ (Q : Matrix n n ℂ)) :
    ‖W‖ ≤ (2 * a)⁻¹ * ‖(Q : Matrix n n ℂ) * (W : Matrix n n ℂ) +
      (W : Matrix n n ℂ) * (Q : Matrix n n ℂ)‖ := by
  have hB := (hermitianSylvester Q hQ W).property
  have hi := RectangularRidgeSylvesterBound.inverse_norm_le (Q : Matrix n n ℂ) hQ ha hfloor hB
  have he : (sylvesterEquiv (Q : Matrix n n ℂ) hQ).symm
      ((hermitianSylvester Q hQ W : Herm (n := n)) : Matrix n n ℂ) = (W : Matrix n n ℂ) := by
    apply (sylvesterEquiv (Q : Matrix n n ℂ) hQ).injective
    rw [LinearEquiv.apply_symm_apply, sylvesterEquiv_apply]
    rfl
  rw [he] at hi
  simpa only [hermitianSylvester_apply, herm_norm_coe, div_eq_mul_inv, mul_comm] using hi

lemma jet_norm_le_square_rhs (r m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) {μ : ℝ} (hμ : 0 < μ)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) :
    ‖jet r (m + 1) S X‖ ≤ (2 * μ ^ exponent (m + 1))⁻¹ *
      ‖dyadicRoot (m + 1) (S : Matrix n n ℂ) * (jet r (m + 1) S X : Matrix n n ℂ) +
        (jet r (m + 1) S X : Matrix n n ℂ) * dyadicRoot (m + 1) (S : Matrix n n ℂ)‖ := by
  simpa only [hermitianDyadicRoot_coe] using solution_norm_le (hermitianDyadicRoot (m + 1) S) (jet r (m + 1) S X)
    (hermitianDyadicRoot_posDef (m + 1) S hS) (Real.rpow_pos_of_pos hμ _) (by
      simpa only [hermitianDyadicRoot_coe] using root_floor (m + 1) hμ hfloor)

lemma norm_real_smul_mul_le (c : ℝ) (hc : 0 ≤ c) (A B : Matrix n n ℂ) :
    ‖c • (A * B)‖ ≤ c * ‖A‖ * ‖B‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_mul_le A B) hc

lemma second_recurrence (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) {μ : ℝ} (hμ : 0 < μ)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) :
    ‖jet 2 (m + 1) S X‖ ≤ (2 * μ ^ exponent (m + 1))⁻¹ *
      (‖jet 2 m S X‖ + 2 * ‖jet 1 (m + 1) S X‖ ^ 2) := by
  have he : dyadicRoot (m + 1) (S : Matrix n n ℂ) * (jet 2 (m + 1) S X : Matrix n n ℂ) +
      (jet 2 (m + 1) S X : Matrix n n ℂ) * dyadicRoot (m + 1) (S : Matrix n n ℂ) =
      (jet 2 m S X : Matrix n n ℂ) -
        (2 : ℝ) • ((jet 1 (m + 1) S X : Matrix n n ℂ) * (jet 1 (m + 1) S X : Matrix n n ℂ)) := by
    rw [square_jet_two m S X hS]
    module
  apply (jet_norm_le_square_rhs 2 m S X hS hμ hfloor).trans
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sub_le _ _).trans
  apply add_le_add_left
  simpa only [herm_norm_coe, pow_two, mul_assoc] using
    norm_real_smul_mul_le 2 (by norm_num) (jet 1 (m + 1) S X : Matrix n n ℂ)
      (jet 1 (m + 1) S X : Matrix n n ℂ)

lemma third_recurrence (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) {μ : ℝ} (hμ : 0 < μ)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) :
    ‖jet 3 (m + 1) S X‖ ≤ (2 * μ ^ exponent (m + 1))⁻¹ *
      (‖jet 3 m S X‖ + 6 * ‖jet 1 (m + 1) S X‖ * ‖jet 2 (m + 1) S X‖) := by
  have he : dyadicRoot (m + 1) (S : Matrix n n ℂ) * (jet 3 (m + 1) S X : Matrix n n ℂ) +
      (jet 3 (m + 1) S X : Matrix n n ℂ) * dyadicRoot (m + 1) (S : Matrix n n ℂ) =
      (jet 3 m S X : Matrix n n ℂ) -
        (3 : ℝ) • ((jet 2 (m + 1) S X : Matrix n n ℂ) * (jet 1 (m + 1) S X : Matrix n n ℂ)) -
        (3 : ℝ) • ((jet 1 (m + 1) S X : Matrix n n ℂ) * (jet 2 (m + 1) S X : Matrix n n ℂ)) := by
    rw [square_jet_three m S X hS]
    module
  apply (jet_norm_le_square_rhs 3 m S X hS hμ hfloor).trans
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have ha := norm_real_smul_mul_le 3 (by norm_num) (jet 2 (m + 1) S X : Matrix n n ℂ)
    (jet 1 (m + 1) S X : Matrix n n ℂ)
  have hb := norm_real_smul_mul_le 3 (by norm_num) (jet 1 (m + 1) S X : Matrix n n ℂ)
    (jet 2 (m + 1) S X : Matrix n n ℂ)
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) hb).trans
  have hh := add_le_add_right (add_le_add_left ha ‖(jet 3 m S X : Matrix n n ℂ)‖)
    (3 * ‖(jet 1 (m + 1) S X : Matrix n n ℂ)‖ * ‖(jet 2 (m + 1) S X : Matrix n n ℂ)‖)
  exact hh.trans_eq (by simp only [herm_norm_coe]; ring)

lemma fourth_recurrence (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) {μ : ℝ} (hμ : 0 < μ)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) :
    ‖jet 4 (m + 1) S X‖ ≤ (2 * μ ^ exponent (m + 1))⁻¹ *
      (‖jet 4 m S X‖ + 8 * ‖jet 1 (m + 1) S X‖ * ‖jet 3 (m + 1) S X‖ +
        6 * ‖jet 2 (m + 1) S X‖ ^ 2) := by
  have he : dyadicRoot (m + 1) (S : Matrix n n ℂ) * (jet 4 (m + 1) S X : Matrix n n ℂ) +
      (jet 4 (m + 1) S X : Matrix n n ℂ) * dyadicRoot (m + 1) (S : Matrix n n ℂ) =
      (jet 4 m S X : Matrix n n ℂ) -
        (4 : ℝ) • ((jet 3 (m + 1) S X : Matrix n n ℂ) * (jet 1 (m + 1) S X : Matrix n n ℂ)) -
        (6 : ℝ) • ((jet 2 (m + 1) S X : Matrix n n ℂ) * (jet 2 (m + 1) S X : Matrix n n ℂ)) -
        (4 : ℝ) • ((jet 1 (m + 1) S X : Matrix n n ℂ) * (jet 3 (m + 1) S X : Matrix n n ℂ)) := by
    rw [square_jet_four m S X hS]
    module
  apply (jet_norm_le_square_rhs 4 m S X hS hμ hfloor).trans
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have ha := norm_real_smul_mul_le 4 (by norm_num) (jet 3 (m + 1) S X : Matrix n n ℂ)
    (jet 1 (m + 1) S X : Matrix n n ℂ)
  have hb := norm_real_smul_mul_le 6 (by norm_num) (jet 2 (m + 1) S X : Matrix n n ℂ)
    (jet 2 (m + 1) S X : Matrix n n ℂ)
  have hc := norm_real_smul_mul_le 4 (by norm_num) (jet 1 (m + 1) S X : Matrix n n ℂ)
    (jet 3 (m + 1) S X : Matrix n n ℂ)
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) hc).trans
  apply (add_le_add_right (add_le_add (norm_sub_le _ _) hb) _).trans
  simp only [herm_norm_coe] at ha hb hc ⊢
  nlinarith [ha]

end MatrixSpencer.RectangularRidgeActualRootJetBounds
