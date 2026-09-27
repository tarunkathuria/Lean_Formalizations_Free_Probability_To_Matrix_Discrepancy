import MatrixSpencer.DyadicRootDerivative

/-!
# Trace identities for the actual matrix-power derivative

Cyclicity removes the noncommutative derivative sum only after taking its
trace. The weighted identity requires the weight to commute with the base
matrix, but puts no commutation or Hermitian condition on the direction.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance matrixPowerTraceCStar : CStarAlgebra (Matrix n n ℂ) := {}

theorem trace_weight_mul_matrixPowerDerivative (p : ℕ) (Q W X : Matrix n n ℂ)
    (hW : Commute W Q) :
    Matrix.trace (W * matrixPowerDerivative p Q X) =
      (p : ℂ) * Matrix.trace (W * Q ^ (p - 1) * X) := by
  rw [matrixPowerDerivative_apply, Matrix.mul_sum, Matrix.trace_sum]
  have hterm : ∀ i ∈ Finset.range p,
      Matrix.trace (W * (Q ^ (p - 1 - i) * X * Q ^ i)) =
        Matrix.trace (W * Q ^ (p - 1) * X) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have he : i + (p - 1 - i) = p - 1 := by omega
    calc
      _ = Matrix.trace ((W * Q ^ (p - 1 - i)) * X * Q ^ i) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Q ^ i * (W * Q ^ (p - 1 - i)) * X) :=
        Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace (W * (Q ^ i * Q ^ (p - 1 - i)) * X) := by
        rw [← Matrix.mul_assoc (Q ^ i) W, ← (hW.pow_right i).eq,
          Matrix.mul_assoc W]
      _ = _ := by rw [← pow_add, he]
  rw [Finset.sum_congr rfl hterm]
  simp

theorem realTrace_weight_mul_matrixPowerDerivative (p : ℕ) (Q W X : Matrix n n ℂ)
    (hW : Commute W Q) :
    realTrace (W * matrixPowerDerivative p Q X) =
      (p : ℝ) * realTrace (W * Q ^ (p - 1) * X) := by
  simp only [realTrace, trace_weight_mul_matrixPowerDerivative p Q W X hW]
  simp

theorem trace_matrixPowerDerivative (p : ℕ) (Q X : Matrix n n ℂ) :
    Matrix.trace (matrixPowerDerivative p Q X) =
      (p : ℂ) * Matrix.trace (Q ^ (p - 1) * X) := by
  simpa only [Matrix.one_mul] using
    trace_weight_mul_matrixPowerDerivative p Q 1 X (Commute.one_left Q)

theorem realTrace_matrixPowerDerivative (p : ℕ) (Q X : Matrix n n ℂ) :
    realTrace (matrixPowerDerivative p Q X) =
      (p : ℝ) * realTrace (Q ^ (p - 1) * X) := by
  simpa only [Matrix.one_mul] using
    realTrace_weight_mul_matrixPowerDerivative p Q 1 X (Commute.one_left Q)

theorem matrix_inv_mul_power_pred {p : ℕ} (hp : 2 ≤ p)
    (Q : Matrix n n ℂ) (hQ : IsUnit Q) :
    Q⁻¹ * Q ^ (p - 1) = Q ^ (p - 2) := by
  have hdet := Q.isUnit_iff_isUnit_det.mp hQ
  rw [show p - 1 = (p - 2) + 1 by omega, pow_succ', ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul Q hdet, Matrix.one_mul]

theorem trace_inv_mul_matrixPowerDerivative_of_isUnit {p : ℕ} (hp : 2 ≤ p)
    (Q X : Matrix n n ℂ) (hQ : IsUnit Q) :
    Matrix.trace (Q⁻¹ * matrixPowerDerivative p Q X) =
      (p : ℂ) * Matrix.trace (Q ^ (p - 2) * X) := by
  have hdet := Q.isUnit_iff_isUnit_det.mp hQ
  have hcomm : Commute Q⁻¹ Q := by
    change Q⁻¹ * Q = Q * Q⁻¹
    rw [Matrix.nonsing_inv_mul Q hdet, Matrix.mul_nonsing_inv Q hdet]
  rw [trace_weight_mul_matrixPowerDerivative p Q Q⁻¹ X hcomm,
    matrix_inv_mul_power_pred hp Q hQ]

theorem realTrace_inv_mul_matrixPowerDerivative_of_isUnit {p : ℕ} (hp : 2 ≤ p)
    (Q X : Matrix n n ℂ) (hQ : IsUnit Q) :
    realTrace (Q⁻¹ * matrixPowerDerivative p Q X) =
      (p : ℝ) * realTrace (Q ^ (p - 2) * X) := by
  simp only [realTrace, trace_inv_mul_matrixPowerDerivative_of_isUnit hp Q X hQ]
  simp

theorem trace_inv_mul_matrixPowerDerivative {p : ℕ} (hp : 2 ≤ p)
    (Q X : Matrix n n ℂ) (hQ : Q.PosDef) :
    Matrix.trace (Q⁻¹ * matrixPowerDerivative p Q X) =
      (p : ℂ) * Matrix.trace (Q ^ (p - 2) * X) :=
  trace_inv_mul_matrixPowerDerivative_of_isUnit hp Q X hQ.isUnit

theorem realTrace_inv_mul_matrixPowerDerivative {p : ℕ} (hp : 2 ≤ p)
    (Q X : Matrix n n ℂ) (hQ : Q.PosDef) :
    realTrace (Q⁻¹ * matrixPowerDerivative p Q X) =
      (p : ℝ) * realTrace (Q ^ (p - 2) * X) :=
  realTrace_inv_mul_matrixPowerDerivative_of_isUnit hp Q X hQ.isUnit

/-- The normalization needed when differentiating the trace of the predecessor power. -/
theorem normalized_pred_power_trace_eq {p : ℕ} (hp : 2 ≤ p)
    (Q X : Matrix n n ℂ) (hQ : IsUnit Q) :
    (p : ℝ) / (p - 1 : ℝ) * realTrace (matrixPowerDerivative (p - 1) Q X) =
      realTrace (Q⁻¹ * matrixPowerDerivative p Q X) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hpne : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [realTrace_matrixPowerDerivative, realTrace_inv_mul_matrixPowerDerivative_of_isUnit hp Q X hQ,
    show p - 1 - 1 = p - 2 by omega, Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one]
  field_simp [hpne]

/-- The real trace paired with an arbitrary fixed physical weight. -/
def matrixWeightedTraceCLM (W : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  realTraceCLM.comp (ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) W 1)

@[simp] theorem matrixWeightedTraceCLM_apply (W X : Matrix n n ℂ) :
    matrixWeightedTraceCLM W X = realTrace (W * X) := by
  simp [matrixWeightedTraceCLM, ContinuousLinearMap.mulLeftRight_apply]

/-- This is the strict derivative of the actual weighted trace-power function. -/
theorem hasStrictFDerivAt_weightedTrace_matrixPower (p : ℕ) (Q W : Matrix n n ℂ)
    (hW : Commute W Q) :
    HasStrictFDerivAt (fun X : Matrix n n ℂ => realTrace (W * X ^ p))
      ((p : ℝ) • matrixWeightedTraceCLM (W * Q ^ (p - 1))) Q := by
  have h := (matrixWeightedTraceCLM W).hasStrictFDerivAt.comp Q (hasStrictFDerivAt_matrixPower p Q)
  have he : (matrixWeightedTraceCLM W).comp (matrixPowerDerivative p Q) =
      (p : ℝ) • matrixWeightedTraceCLM (W * Q ^ (p - 1)) := by
    ext X
    simp only [ContinuousLinearMap.comp_apply, matrixWeightedTraceCLM_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact realTrace_weight_mul_matrixPowerDerivative p Q W X hW
  rw [he] at h
  simpa only [Function.comp_def, matrixWeightedTraceCLM_apply] using h

theorem hasStrictFDerivAt_realTrace_matrixPower (p : ℕ) (Q : Matrix n n ℂ) :
    HasStrictFDerivAt (fun X : Matrix n n ℂ => realTrace (X ^ p))
      ((p : ℝ) • matrixWeightedTraceCLM (Q ^ (p - 1))) Q := by
  simpa only [Matrix.one_mul] using
    hasStrictFDerivAt_weightedTrace_matrixPower p Q 1 (Commute.one_left Q)

theorem fderiv_realTrace_matrixPower_apply (p : ℕ) (Q X : Matrix n n ℂ) :
    fderiv ℝ (fun Y : Matrix n n ℂ => realTrace (Y ^ p)) Q X =
      (p : ℝ) * realTrace (Q ^ (p - 1) * X) := by
  rw [(hasStrictFDerivAt_realTrace_matrixPower p Q).hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.smul_apply, matrixWeightedTraceCLM_apply, smul_eq_mul]

end MatrixSpencer
