import MatrixSpencer.TraceGeometry
import MatrixSpencer.DyadicRoot
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Weighted trace Cauchy–Schwarz and its dyadic iteration. All traces are
actual real parts of matrix traces, without a commutation assumption. -/

open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
noncomputable section
namespace MatrixSpencer
namespace DyadicTraceInterpolation

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Cauchy–Schwarz for the positive trace functional X↦Tr(YX). -/
theorem weightedTrace_sq_le {Y T : Matrix n n ℂ}
    (hY : Y.PosSemidef) (hT : T.IsHermitian) :
    realTrace (Y * T) ^ 2 ≤ realTrace Y * realTrace (Y * (T * T)) := by
  have hpoly : ∀ t : ℝ, 0 ≤ realTrace Y * (t * t) +
      (-2 * realTrace (Y * T)) * t + realTrace (Y * (T * T)) := by
    intro t
    have h := realTrace_mul_nonneg hY (Matrix.posSemidef_conjTranspose_mul_self
      (T - t • (1 : Matrix n n ℂ)))
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hT.eq,
      Matrix.conjTranspose_one, star_trivial, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      realTrace_sub, realTrace_smul] at h
    nlinarith
  have hd := discrim_le_zero hpoly
  unfold discrim at hd
  nlinarith

/-- A square-root step halves the interpolation exponent. -/
theorem weightedTrace_sqrt_sq_le {Y A : Matrix n n ℂ}
    (hY : Y.PosSemidef) (hA : A.PosSemidef) :
    realTrace (Y * CFC.sqrt A) ^ 2 ≤ realTrace Y * realTrace (Y * A) := by
  have h := weightedTrace_sq_le hY (CFC.sqrt_nonneg A).posSemidef.isHermitian
  simpa only [CFC.sqrt_mul_sqrt_self A hA.nonneg] using h

theorem weightedTrace_sqrt_le {Y A : Matrix n n ℂ}
    (hY : Y.PosSemidef) (hA : A.PosSemidef) :
    realTrace (Y * CFC.sqrt A) ≤ Real.sqrt (realTrace Y * realTrace (Y * A)) := by
  apply (Real.le_sqrt (realTrace_mul_nonneg hY (CFC.sqrt_nonneg A).posSemidef)
    (mul_nonneg (realTrace_nonneg hY) (realTrace_mul_nonneg hY hA))).mpr
  exact weightedTrace_sqrt_sq_le hY hA

/-- The scalar exponent after m square-root interpolation steps. -/
def exponent (m : ℕ) : ℝ := ((2 : ℝ) ^ m)⁻¹

@[simp] lemma exponent_zero : exponent 0 = 1 := by norm_num [exponent]

lemma exponent_pos (m : ℕ) : 0 < exponent m := by unfold exponent; positivity

lemma exponent_le_one (m : ℕ) : exponent m ≤ 1 := by
  unfold exponent
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

lemma exponent_succ (m : ℕ) : exponent (m + 1) = exponent m / 2 := by
  simp only [exponent, pow_succ, _root_.mul_inv_rev, div_eq_mul_inv]
  ring

lemma sqrt_interpolation_step {w b e : ℝ} (hw : 0 ≤ w) (hb : 0 ≤ b)
    (he : e ≤ 1) :
    Real.sqrt (w * (w ^ (1 - e) * b ^ e)) = w ^ (1 - e / 2) * b ^ (e / 2) := by
  by_cases hw0 : w = 0
  · have he' : 1 - e / 2 ≠ 0 := by linarith
    simp [hw0, Real.zero_rpow he']
  · have hwp : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    have hpow : w * w ^ (1 - e) = w ^ (2 - e) := by
      calc
        _ = w ^ (1 : ℝ) * w ^ (1 - e) := by rw [Real.rpow_one]
        _ = w ^ (1 + (1 - e)) := (Real.rpow_add hwp _ _).symm
        _ = _ := by congr 1; ring
    rw [← mul_assoc, hpow, Real.sqrt_eq_rpow,
      Real.mul_rpow (Real.rpow_nonneg hw _) (Real.rpow_nonneg hb _),
      ← Real.rpow_mul hw, ← Real.rpow_mul hb]
    congr 1 <;> congr 1 <;> ring

/-- An actual nonnegative sequence of weighted square-root inequalities interpolates its endpoints. -/
theorem sequence_le_interpolation (a : ℕ → ℝ) {w : ℝ} (hw : 0 ≤ w)
    (ha : ∀ j, 0 ≤ a j) (hstep : ∀ j, a (j + 1) ^ 2 ≤ w * a j) (m : ℕ) :
    a m ≤ w ^ (1 - exponent m) * (a 0) ^ exponent m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hroot : a (m + 1) ≤ Real.sqrt (w * a m) :=
      (Real.le_sqrt (ha _) (mul_nonneg hw (ha _))).mpr (hstep m)
    apply hroot.trans
    calc
      _ ≤ Real.sqrt (w * (w ^ (1 - exponent m) * (a 0) ^ exponent m)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ih hw)
      _ = _ := by rw [sqrt_interpolation_step hw (ha 0) (exponent_le_one m), exponent_succ]

/-- Iteration starts at the square-root endpoint, with no shared eigenbasis required. -/
theorem weightedTrace_dyadic_from_sqrt (m : ℕ) {Y S : Matrix n n ℂ}
    (hY : Y.PosSemidef) (hS : S.PosSemidef) :
    realTrace (Y * dyadicRoot (m + 1) S) ≤
      (realTrace Y) ^ (1 - exponent m) * (realTrace (Y * CFC.sqrt S)) ^ exponent m := by
  have h := sequence_le_interpolation (fun j => realTrace (Y * dyadicRoot (j + 1) S))
    (realTrace_nonneg hY)
    (fun j => realTrace_mul_nonneg hY (dyadicRoot_posSemidef (j + 1) hS))
    (fun j => weightedTrace_sqrt_sq_le hY (dyadicRoot_posSemidef (j + 1) hS)) m
  exact h

lemma exponent_predecessor (m : ℕ) : exponent m = 2 / (2 : ℝ) ^ (m + 1) := by
  simp only [exponent, pow_succ]
  field_simp

/-- The paired trace exponent is exactly twice the regularizer root exponent. -/
theorem weightedTrace_dyadic_le (m : ℕ) (hm : 1 ≤ m) {Y S : Matrix n n ℂ}
    (hY : Y.PosSemidef) (hS : S.PosSemidef) :
    realTrace (Y * dyadicRoot m S) ≤
      (realTrace Y) ^ (1 - 2 / (2 : ℝ) ^ m) *
        (realTrace (Y * CFC.sqrt S)) ^ (2 / (2 : ℝ) ^ m) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  simpa only [exponent_predecessor] using weightedTrace_dyadic_from_sqrt j hY hS

omit [DecidableEq n] in
lemma trace_congruence_pairing (V T X : Matrix n n ℂ) :
    realTrace ((V * T * Vᴴ) * X) = realTrace ((Vᴴ * X * V) * T) := by
  simpa only [Matrix.mul_assoc] using realTrace_mul_cycle V T (Vᴴ * X)

/-- The exact correlated-trace form used after the balanced change of variables. -/
theorem correlated_trace_dyadic_le (m : ℕ) (hm : 1 ≤ m)
    (V : Matrix n n ℂ) {S X : Matrix n n ℂ} (hS : S.PosSemidef) (hX : X.PosSemidef) :
    realTrace ((V * dyadicRoot m S * Vᴴ) * X) ≤
      (realTrace ((V * Vᴴ) * X)) ^ (1 - 2 / (2 : ℝ) ^ m) *
        (realTrace ((V * CFC.sqrt S * Vᴴ) * X)) ^ (2 / (2 : ℝ) ^ m) := by
  have h := weightedTrace_dyadic_le m hm (hX.conjTranspose_mul_mul_same V) hS
  have hw : realTrace (Vᴴ * X * V) = realTrace ((V * Vᴴ) * X) := by
    simpa only [Matrix.mul_one] using (trace_congruence_pairing V 1 X).symm
  rw [← trace_congruence_pairing V (dyadicRoot m S) X, hw,
    ← trace_congruence_pairing V (CFC.sqrt S) X] at h
  exact h

end DyadicTraceInterpolation
end MatrixSpencer
