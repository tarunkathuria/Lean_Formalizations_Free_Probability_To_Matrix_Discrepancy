import MatrixSpencer.RectangularRidgeSylvesterBound
import MatrixSpencer.DyadicRootDerivative
import MatrixSpencer.DyadicTraceBounds

/-!
# Tracked dyadic square-root derivative bounds

The actual first derivative is bounded uniformly in the root depth, by tracking
the successive spectral floors rather than repeatedly substituting the original
floor. Scalar constants for the differentiated square relation through order
four are supplied separately. The latter algebraic identities do not themselves
assert an actual higher-derivative theorem.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeRootJetBounds
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def exponent (m : ℕ) : ℝ := 1 / (2 : ℝ) ^ m

theorem exponent_pos (m : ℕ) : 0 < exponent m := by unfold exponent; positivity

theorem exponent_succ (m : ℕ) : exponent m = 2 * exponent (m + 1) := by
  unfold exponent
  rw [pow_succ]
  field_simp

/-- The actual iterated root inherits its tracked spectral floor. -/
theorem root_floor (m : ℕ) {μ : ℝ} (hμ : 0 < μ) {S : Matrix n n ℂ}
    (hS : μ • (1 : Matrix n n ℂ) ≤ S) :
    μ ^ exponent m • (1 : Matrix n n ℂ) ≤ dyadicRoot m S := by
  have h := dyadicRoot_mono m hS
  rw [dyadicRoot_real_smul_one m hμ.le] at h
  simpa only [exponent, _root_.one_div_pow, Nat.cast_pow, Nat.cast_ofNat] using h

/-- Exponents cancel in one differentiated square-root step. -/
theorem first_step_scale (m : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    (2 * μ ^ exponent (m + 1))⁻¹ * μ ^ (exponent m - 1) =
      (1 / 2 : ℝ) * μ ^ (exponent (m + 1) - 1) := by
  have he : exponent m - 1 = exponent (m + 1) + (exponent (m + 1) - 1) := by
    rw [exponent_succ m]
    ring
  rw [he, Real.rpow_add hμ]
  have hp : μ ^ exponent (m + 1) ≠ 0 := (Real.rpow_pos_of_pos hμ _).ne'
  field_simp

/-- The norm of the genuine real dyadic-root derivative, with no supplied derivative bound. -/
theorem derivative_norm_le (m : ℕ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) {μ : ℝ} (hμ : 0 < μ)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) :
    ‖(hermitianDyadicRootDerivative m S hS :
      selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ))‖ ≤
      μ ^ (exponent m - 1) := by
  induction m with
  | zero =>
    simpa only [hermitianDyadicRootDerivative, exponent, pow_zero, div_one,
      sub_self, Real.rpow_zero] using
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := selfAdjoint (Matrix n n ℂ)))
  | succ m ih =>
    let Q := hermitianSqrt (hermitianDyadicRoot m S)
    have hQ : (Q : Matrix n n ℂ).PosDef :=
      (hermitianDyadicRoot_posDef m S hS).posDef_sqrt
    have hf : μ ^ exponent (m + 1) • (1 : Matrix n n ℂ) ≤ (Q : Matrix n n ℂ) := by
      simpa only [Q, hermitianSqrt_coe, hermitianDyadicRoot_coe, dyadicRoot_succ] using
        root_floor (m + 1) hμ hfloor
    have hinv := RectangularRidgeSylvesterBound.hermitian_inverse_opNorm_le Q hQ
      (Real.rpow_pos_of_pos hμ _) hf
    change ‖((hermitianSylvester Q hQ).symm.toContinuousLinearMap).comp
      (hermitianDyadicRootDerivative m S hS :
        selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ))‖ ≤ _
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply (mul_le_mul hinv ih (norm_nonneg _)
      (by positivity : 0 ≤ (2 * μ ^ exponent (m + 1))⁻¹)).trans
    rw [first_step_scale m hμ]
    nlinarith [Real.rpow_nonneg hμ.le (exponent (m + 1) - 1)]

/-- Uniform inverse-polynomial bound on the actual derivative at any depth. -/
theorem fderiv_norm_le_inverse_floor (m : ℕ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) :
    ‖fderiv ℝ (hermitianDyadicRoot m) S‖ ≤ μ⁻¹ := by
  rw [fderiv_hermitianDyadicRoot m S hS]
  apply (derivative_norm_le m S hS hμ hfloor).trans
  rw [Real.rpow_sub hμ, Real.rpow_one]
  exact (div_le_div_of_nonneg_right
    (Real.rpow_le_one hμ.le hμ1 (exponent_pos m).le) hμ.le).trans_eq (one_div μ)

/-- Universal constants solving the differentiated-square scalar recurrences. -/
def jetConstant : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 12
  | 4 => 120
  | _ => 0

/-- The cross terms in the second, third and fourth square derivatives. -/
theorem jetConstant_recurrences :
    2 * jetConstant 1 ^ 2 = jetConstant 2 ∧
    6 * jetConstant 1 * jetConstant 2 = jetConstant 3 ∧
    8 * jetConstant 1 * jetConstant 3 + 6 * jetConstant 2 ^ 2 = jetConstant 4 := by
  norm_num [jetConstant]

/-- The tracked powers in each higher-order cross term have the same scale. -/
theorem jet_cross_scale {μ q : ℝ} (hμ : 0 < μ) (r s : ℕ) (hs : s ≤ r) :
    (μ ^ (q - (s : ℝ)) * μ ^ (q - ((r - s : ℕ) : ℝ))) /
      (2 * μ ^ q) = (1 / 2 : ℝ) * μ ^ (q - (r : ℝ)) := by
  rw [← Real.rpow_add hμ, Nat.cast_sub hs]
  have he : q - (s : ℝ) + (q - ((r : ℝ) - (s : ℝ))) = q + (q - (r : ℝ)) := by ring
  rw [he, Real.rpow_add hμ]
  have hp : μ ^ q ≠ 0 := (Real.rpow_pos_of_pos hμ _).ne'
  field_simp

end MatrixSpencer.RectangularRidgeRootJetBounds
