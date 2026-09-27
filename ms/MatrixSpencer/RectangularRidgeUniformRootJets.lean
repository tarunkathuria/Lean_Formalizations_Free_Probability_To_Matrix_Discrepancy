import MatrixSpencer.RectangularRidgeActualRootJetBounds

/-!
# Depth-independent bounds through four derivatives of the actual dyadic root

The scalar powers track the improving spectral floor at each root. Thus neither
the inverse-floor exponent nor the constants grow with the root depth.
-/
open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeUniformRootJets
open RectangularRidgeRootJetBounds RectangularRidgeActualRootJets
open RectangularRidgeActualRootJetBounds
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance ridgeUniformRootJetsCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeUniformRootJetsRealSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

lemma old_step_scale (m : ℕ) (r : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    (2 * μ ^ exponent (m + 1))⁻¹ * μ ^ (exponent m - r) =
      (1 / 2 : ℝ) * μ ^ (exponent (m + 1) - r) := by
  have he : exponent m - r = exponent (m + 1) + (exponent (m + 1) - r) := by
    rw [exponent_succ m]
    ring
  rw [he, Real.rpow_add hμ]
  have hp : μ ^ exponent (m + 1) ≠ 0 := (Real.rpow_pos_of_pos hμ _).ne'
  field_simp

lemma cross_step_scale {μ q r s : ℝ} (hμ : 0 < μ) :
    (2 * μ ^ q)⁻¹ * (μ ^ (q - s) * μ ^ (q - (r - s))) =
      (1 / 2 : ℝ) * μ ^ (q - r) := by
  rw [← Real.rpow_add hμ]
  have he : q - s + (q - (r - s)) = q + (q - r) := by ring
  rw [he, Real.rpow_add hμ]
  have hp : μ ^ q ≠ 0 := (Real.rpow_pos_of_pos hμ _).ne'
  field_simp

lemma second_scale (m : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    (2 * μ ^ exponent (m + 1))⁻¹ *
      (2 * μ ^ (exponent m - 2) + 2 * (μ ^ (exponent (m + 1) - 1)) ^ 2) =
      2 * μ ^ (exponent (m + 1) - 2) := by
  have hc := cross_step_scale (q := exponent (m + 1)) (r := 2) (s := 1) hμ
  norm_num only [show (2 : ℝ) - 1 = 1 from by norm_num] at hc
  calc
    _ = 2 * ((2 * μ ^ exponent (m + 1))⁻¹ * μ ^ (exponent m - 2)) +
      2 * ((2 * μ ^ exponent (m + 1))⁻¹ *
        (μ ^ (exponent (m + 1) - 1) * μ ^ (exponent (m + 1) - 1))) := by ring
    _ = _ := by rw [old_step_scale m 2 hμ, hc]; ring

lemma third_scale (m : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    (2 * μ ^ exponent (m + 1))⁻¹ *
      (12 * μ ^ (exponent m - 3) +
        6 * μ ^ (exponent (m + 1) - 1) * (2 * μ ^ (exponent (m + 1) - 2))) =
      12 * μ ^ (exponent (m + 1) - 3) := by
  have hc := cross_step_scale (q := exponent (m + 1)) (r := 3) (s := 1) hμ
  norm_num only [show (3 : ℝ) - 1 = 2 from by norm_num] at hc
  calc
    _ = 12 * ((2 * μ ^ exponent (m + 1))⁻¹ * μ ^ (exponent m - 3)) +
      12 * ((2 * μ ^ exponent (m + 1))⁻¹ *
        (μ ^ (exponent (m + 1) - 1) * μ ^ (exponent (m + 1) - 2))) := by ring
    _ = _ := by rw [old_step_scale m 3 hμ, hc]; ring

lemma fourth_scale (m : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    (2 * μ ^ exponent (m + 1))⁻¹ *
      (120 * μ ^ (exponent m - 4) +
        8 * μ ^ (exponent (m + 1) - 1) * (12 * μ ^ (exponent (m + 1) - 3)) +
        6 * (2 * μ ^ (exponent (m + 1) - 2)) ^ 2) =
      120 * μ ^ (exponent (m + 1) - 4) := by
  have hc := cross_step_scale (q := exponent (m + 1)) (r := 4) (s := 1) hμ
  have hd := cross_step_scale (q := exponent (m + 1)) (r := 4) (s := 2) hμ
  norm_num only [show (4 : ℝ) - 1 = 3 from by norm_num] at hc
  norm_num only [show (4 : ℝ) - 2 = 2 from by norm_num] at hd
  calc
    _ = 120 * ((2 * μ ^ exponent (m + 1))⁻¹ * μ ^ (exponent m - 4)) +
      96 * ((2 * μ ^ exponent (m + 1))⁻¹ *
        (μ ^ (exponent (m + 1) - 1) * μ ^ (exponent (m + 1) - 3))) +
      24 * ((2 * μ ^ exponent (m + 1))⁻¹ *
        (μ ^ (exponent (m + 1) - 2) * μ ^ (exponent (m + 1) - 2))) := by ring
    _ = _ := by rw [old_step_scale m 4 hμ, hc, hd]; ring

lemma zero_depth_higher_jets (S X : Herm (n := n)) :
    jet 2 0 S X = 0 ∧ jet 3 0 S X = 0 ∧ jet 4 0 S X = 0 := by
  have hl : deriv (path 0 S X) = fun _ => X := by
    funext t
    have h : HasDerivAt (line S X) X t := by
      simpa [line] using (hasDerivAt_const t S).add ((hasDerivAt_id t).smul_const X)
    exact h.deriv
  have hz : deriv (fun _ : ℝ => X) = fun _ => (0 : Herm (n := n)) := by
    funext t
    exact deriv_const t X
  simp only [jet, show (4 : ℕ) = 3 + 1 from rfl, show (3 : ℕ) = 2 + 1 from rfl,
    show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero, hl, hz, deriv_const]
  simp

lemma jet_two_norm_le (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) {μ : ℝ} (hμ : 0 < μ)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) (hX : ‖X‖ ≤ 1) :
    ‖jet 2 m S X‖ ≤ 2 * μ ^ (exponent m - 2) := by
  induction m with
  | zero => rw [(zero_depth_higher_jets S X).1, norm_zero]; positivity
  | succ m ih =>
    have h1 := jet_one_norm_le (m + 1) S X hS hμ hfloor hX
    apply (second_recurrence m S X hS hμ hfloor).trans
    apply le_trans _ (second_scale m hμ).le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add ih (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) h1 2) (by norm_num))

lemma jet_three_norm_le (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) {μ : ℝ} (hμ : 0 < μ)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) (hX : ‖X‖ ≤ 1) :
    ‖jet 3 m S X‖ ≤ 12 * μ ^ (exponent m - 3) := by
  induction m with
  | zero => rw [(zero_depth_higher_jets S X).2.1, norm_zero]; positivity
  | succ m ih =>
    have h1 := jet_one_norm_le (m + 1) S X hS hμ hfloor hX
    have h2 := jet_two_norm_le (m + 1) S X hS hμ hfloor hX
    apply (third_recurrence m S X hS hμ hfloor).trans
    apply le_trans _ (third_scale m hμ).le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add ih
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2
      (norm_nonneg _) (by positivity)

lemma jet_four_norm_le (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) {μ : ℝ} (hμ : 0 < μ)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) (hX : ‖X‖ ≤ 1) :
    ‖jet 4 m S X‖ ≤ 120 * μ ^ (exponent m - 4) := by
  induction m with
  | zero => rw [(zero_depth_higher_jets S X).2.2, norm_zero]; positivity
  | succ m ih =>
    have h1 := jet_one_norm_le (m + 1) S X hS hμ hfloor hX
    have h2 := jet_two_norm_le (m + 1) S X hS hμ hfloor hX
    have h3 := jet_three_norm_le (m + 1) S X hS hμ hfloor hX
    apply (fourth_recurrence m S X hS hμ hfloor).trans
    apply le_trans _ (fourth_scale m hμ).le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add
    · apply add_le_add ih
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h3
        (norm_nonneg _) (by positivity)
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h2 2) (by norm_num)

end MatrixSpencer.RectangularRidgeUniformRootJets
