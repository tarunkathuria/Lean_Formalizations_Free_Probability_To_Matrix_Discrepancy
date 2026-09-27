import MatrixSpencer.KSSylvesterOrder
import MatrixSpencer.SqrtDerivative

/-!
# Explicit operator-norm bounds for the actual Sylvester inverse

A coefficient floor `a I ≤ Q` gives inverse norm `1/(2a)` on the real
Hermitian space. The proof is by positivity of the already constructed
Sylvester inverse and an explicit scalar-identity comparison. No inverse
norm or derivative bound is supplied as a hypothesis.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeSylvesterBound
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- The actual Sylvester inverse at a scalar multiple of its coefficient. -/
theorem inverse_smul_coefficient (Q : Matrix n n ℂ) (hQ : Q.PosDef) (c : ℝ) :
    (sylvesterEquiv Q hQ).symm ((2 * c) • Q) = c • (1 : Matrix n n ℂ) := by
  apply (sylvesterEquiv Q hQ).injective
  rw [LinearEquiv.apply_symm_apply, sylvesterEquiv_apply]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  module

/-- A spectral floor bounds the actual inverse on every Hermitian input. -/
theorem inverse_norm_le (Q : Matrix n n ℂ) (hQ : Q.PosDef) {a : ℝ}
    (ha : 0 < a) (hfloor : a • (1 : Matrix n n ℂ) ≤ Q)
    {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    ‖(sylvesterEquiv Q hQ).symm B‖ ≤ ‖B‖ / (2 * a) := by
  let c := ‖B‖ / (2 * a)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hid : (2 * c) * a = ‖B‖ := by dsimp [c]; field_simp
  have hscaled : ‖B‖ • (1 : Matrix n n ℂ) ≤ (2 * c) • Q := by
    have h := smul_le_smul_of_nonneg_left hfloor (by positivity : 0 ≤ 2 * c)
    simpa only [smul_smul, hid] using h
  have hupper : B ≤ (2 * c) • Q := by
    have h := hB.isSelfAdjoint.le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one] at h
    exact h.trans hscaled
  have hlower : -(2 * c) • Q ≤ B := by
    have h := hB.isSelfAdjoint.neg_algebraMap_norm_le_self
    rw [Algebra.algebraMap_eq_smul_one] at h
    have hn := neg_le_neg hscaled
    simpa only [neg_smul] using hn.trans h
  have hu := KSSylvesterOrder.inverse_mono Q hQ hupper
  have hl := KSSylvesterOrder.inverse_mono Q hQ hlower
  rw [inverse_smul_coefficient] at hu
  have he : -(2 * c) = 2 * (-c) := by ring
  rw [he, inverse_smul_coefficient] at hl
  exact KrausContraction.norm_le_of_order_interval
    (sylvester_inverse_isHermitian Q hQ hB) hc hl hu

/-- The continuous inverse on the genuine real Hermitian normed space. -/
theorem hermitian_inverse_opNorm_le (Q : selfAdjoint (Matrix n n ℂ))
    (hQ : (Q : Matrix n n ℂ).PosDef) {a : ℝ} (ha : 0 < a)
    (hfloor : a • (1 : Matrix n n ℂ) ≤ (Q : Matrix n n ℂ)) :
    ‖(hermitianSylvester Q hQ).symm.toContinuousLinearMap‖ ≤ (2 * a)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro B
  have h := inverse_norm_le (Q : Matrix n n ℂ) hQ ha hfloor B.property
  change ‖(sylvesterEquiv (Q : Matrix n n ℂ) hQ).symm (B : Matrix n n ℂ)‖ ≤ _
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- The actual square-root derivative, with an explicit floor of its root. -/
theorem sqrt_fderiv_norm_le (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) {a : ℝ} (ha : 0 < a)
    (hfloor : a • (1 : Matrix n n ℂ) ≤ CFC.sqrt (S : Matrix n n ℂ)) :
    ‖fderiv ℝ hermitianSqrt S‖ ≤ (2 * a)⁻¹ := by
  rw [fderiv_hermitianSqrt_eq S hS]
  exact hermitian_inverse_opNorm_le (hermitianSqrt S) hS.posDef_sqrt ha hfloor

end MatrixSpencer.RectangularRidgeSylvesterBound
