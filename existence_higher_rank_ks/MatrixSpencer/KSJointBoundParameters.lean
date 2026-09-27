import MatrixSpencer.KSComplexPolynomialBounds
import MatrixSpencer.KSComplexObjectiveBound
import MatrixSpencer.KSComplexPerturbationRadius

/-!
# Input-entry constants for the remaining joint derivative certificate

All constants here are explicit arithmetic expressions. Their positivity
is proved. The separate joint-certificate theorem must still prove that
the actual objective obeys the declared derivative cap; the formula alone
does not assert that analytic conclusion.
-/

noncomputable section
namespace MatrixSpencer.KSJointBoundParameters

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

def radius (v : Fin N → n → ℂ) (δ η θ : ℝ) : ℝ :=
  KSComplexPerturbationRadius.radius (KSDebitUniformFloor.uniformFloor v δ η θ) (δ / 2)

def centerCap (v : Fin N → n → ℂ) (δ η : ℝ) : ℝ :=
  KSDebitUniformFloor.centerRadius v δ η + 2 * KSComplexPolynomialBounds.slopeBudget v

def objectiveCap (v : Fin N → n → ℂ) (δ η θ : ℝ) : ℝ :=
  1 + KSComplexObjectiveBound.valueCap (Fintype.card (n ⊕ n))
    (centerCap v δ η) 2 (KSComplexPolynomialBounds.sourceBudget v) θ

def jointCap (v : Fin N → n → ℂ) (δ η θ : ℝ) : ℝ :=
  objectiveCap v δ η θ * (10 / radius v δ η θ) ^ 4

theorem centerCap_pos (v : Fin N → n → ℂ) {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) :
    0 < centerCap v δ η := by
  have hR := KSDebitUniformFloor.centerRadius_pos v hδ hη
  have hs := KSComplexPolynomialBounds.slopeBudget_pos v
  unfold centerCap
  linarith

theorem objectiveCap_pos (v : Fin N → n → ℂ) {δ η θ : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hθ : 0 ≤ θ) : 0 < objectiveCap v δ η θ := by
  have h := KSComplexObjectiveBound.valueCap_nonneg (Fintype.card (n ⊕ n))
    (centerCap_pos v hδ hη).le (by norm_num : (0 : ℝ) ≤ 2) hθ
    (m := KSComplexPolynomialBounds.sourceBudget v)
  unfold objectiveCap
  linarith

theorem radius_pos [Nonempty n] (v : Fin N → n → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hθ : 0 < θ) : 0 < radius v δ η θ :=
  KSComplexPerturbationRadius.radius_pos
    (KSDebitUniformFloor.uniformFloor_pos v hδ.le hη hθ) (by positivity)

theorem radius_le_one (v : Fin N → n → ℂ) (δ η θ : ℝ) : radius v δ η θ ≤ 1 :=
  KSComplexPerturbationRadius.radius_le_one _ _

theorem jointCap_pos [Nonempty n] (v : Fin N → n → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hθ : 0 < θ) : 0 < jointCap v δ η θ := by
  have hK := objectiveCap_pos v hδ.le hη hθ.le
  have hr := radius_pos v hδ hη hθ
  unfold jointCap
  positivity

end MatrixSpencer.KSJointBoundParameters
