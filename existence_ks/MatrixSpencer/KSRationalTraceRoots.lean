import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# Rational matrix traces as sums over characteristic-polynomial roots

The matrix is arbitrary complex, without normality or diagonalizability.
Roots are a multiset, so their algebraic multiplicities are retained.
The proof uses a polynomial determinant identity and the logarithmic
derivative of the characteristic polynomial, not a spectral decomposition.
-/

open Matrix Polynomial
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSRationalTraceRoots

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Polynomial factorization by an invertible constant matrix. -/
theorem det_shift_polynomial (D : Matrix n n ℂ) (hD : IsUnit D) :
    Matrix.det (D.map C + (X : ℂ[X]) • (1 : Matrix n n ℂ[X])) =
      C D.det * Matrix.det (1 + (X : ℂ[X]) • D⁻¹.map C) := by
  have hdet := (Matrix.isUnit_iff_isUnit_det D).mp hD
  have hi : D.map C * D⁻¹.map C = (1 : Matrix n n ℂ[X]) := by
    simpa using congrArg (fun A : Matrix n n ℂ => A.map C) (Matrix.mul_nonsing_inv D hdet)
  have hm : D.map C + (X : ℂ[X]) • (1 : Matrix n n ℂ[X]) =
      D.map C * (1 + (X : ℂ[X]) • D⁻¹.map C) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hi]
  rw [hm, Matrix.det_mul]
  congr 1
  exact (RingHom.map_det C D).symm

theorem derivative_det_shift (D : Matrix n n ℂ) (hD : IsUnit D) :
    (Matrix.det (D.map C + (X : ℂ[X]) • (1 : Matrix n n ℂ[X]))).derivative.eval 0 =
      D.det * Matrix.trace D⁻¹ := by
  rw [det_shift_polynomial D hD]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.eval_mul, Polynomial.eval_C, Matrix.derivative_det_one_add_X_smul]

theorem charpoly_shift (M : Matrix n n ℂ) (z : ℂ) :
    M.charpoly.comp (X + C z) =
      Matrix.det ((z • (1 : Matrix n n ℂ) - M).map C +
        (X : ℂ[X]) • (1 : Matrix n n ℂ[X])) := by
  apply Polynomial.funext
  intro t
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Matrix.eval_charpoly, _root_.eval_det, matPolyEquiv_eval_eq_map]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij, Matrix.scalar_apply] <;> ring

/-- Jacobi's determinant identity specialized to a scalar resolvent. -/
theorem trace_inverse_eq_log_derivative (M : Matrix n n ℂ) (z : ℂ)
    (hz : IsUnit (z • (1 : Matrix n n ℂ) - M)) :
    Matrix.trace (z • (1 : Matrix n n ℂ) - M)⁻¹ =
      M.charpoly.derivative.eval z / M.charpoly.eval z := by
  have he := congrArg (fun p : ℂ[X] => p.derivative.eval 0) (charpoly_shift M z)
  dsimp only at he
  rw [derivative_det_shift _ hz] at he
  simp only [Polynomial.derivative_comp, Polynomial.derivative_add, Polynomial.derivative_X,
    Polynomial.derivative_C, add_zero, one_mul, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add] at he
  have hid : Matrix.scalar n z = z • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.scalar_apply]
  have hn : M.charpoly.eval z ≠ 0 := by
    rw [Matrix.eval_charpoly, hid]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hz).ne_zero
  rw [Matrix.eval_charpoly, hid] at hn ⊢
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using he.symm

/-- The scalar resolvent trace, retaining every algebraic root multiplicity. -/
theorem trace_inverse_eq_sum_roots (M : Matrix n n ℂ) (z : ℂ)
    (hz : IsUnit (z • (1 : Matrix n n ℂ) - M)) :
    Matrix.trace (z • (1 : Matrix n n ℂ) - M)⁻¹ =
      (M.charpoly.roots.map (fun root => 1 / (z - root))).sum := by
  rw [trace_inverse_eq_log_derivative M z hz]
  apply Polynomial.eval_derivative_div_eval_of_ne_zero_of_splits (IsAlgClosed.splits _)
  rw [Matrix.eval_charpoly]
  have hid : Matrix.scalar n z = z • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.scalar_apply]
  rw [hid]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hz).ne_zero

theorem inverse_smul (D : Matrix n n ℂ) (hD : IsUnit D) (c : ℂ) (hc : c ≠ 0) :
    (c • D)⁻¹ = c⁻¹ • D⁻¹ := by
  apply Matrix.inv_eq_right_inv
  simp [smul_smul,
    Matrix.mul_nonsing_inv D ((Matrix.isUnit_iff_isUnit_det D).mp hD), hc]

theorem roots_card (M : Matrix n n ℂ) : M.charpoly.roots.card = Fintype.card n := by
  have hh := Polynomial.natDegree_eq_card_roots (IsAlgClosed.splits M.charpoly)
  simpa only [Polynomial.map_id, Matrix.charpoly_natDegree_eq_dim] using hh.symm

theorem trace_mul_inverse_resolvent (M : Matrix n n ℂ) (z : ℂ)
    (hz : IsUnit (z • (1 : Matrix n n ℂ) - M)) :
    Matrix.trace (M * (z • (1 : Matrix n n ℂ) - M)⁻¹) =
      z * Matrix.trace (z • (1 : Matrix n n ℂ) - M)⁻¹ - (Fintype.card n : ℂ) := by
  have he := congrArg Matrix.trace (Matrix.mul_nonsing_inv
    (z • (1 : Matrix n n ℂ) - M) ((Matrix.isUnit_iff_isUnit_det _).mp hz))
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul, Matrix.trace_one] at he
  linear_combination -he

theorem trace_rational_nonzero_slope (M : Matrix n n ℂ) (a b : ℂ) (hb : b ≠ 0)
    (hD : IsUnit (a • (1 : Matrix n n ℂ) + b • M)) :
    Matrix.trace (M * (a • (1 : Matrix n n ℂ) + b • M)⁻¹) =
      (M.charpoly.roots.map (fun root => root / (a + b * root))).sum := by
  let z : ℂ := -a / b
  let D : Matrix n n ℂ := z • (1 : Matrix n n ℂ) - M
  have hscale : a • (1 : Matrix n n ℂ) + b • M = (-b) • D := by
    dsimp [D, z]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    field_simp
    ring
  have hdet : D.det ≠ 0 := by
    intro hzero
    have hh := ((Matrix.isUnit_iff_isUnit_det _).mp hD).ne_zero
    apply hh
    rw [hscale, Matrix.det_smul, hzero, mul_zero]
  have hunit : IsUnit D := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have heval : M.charpoly.eval z ≠ 0 := by
    rw [Matrix.eval_charpoly]
    have hid : Matrix.scalar n z = z • (1 : Matrix n n ℂ) := by
      ext i j
      by_cases hij : i = j <;> simp [hij, Matrix.scalar_apply]
    rwa [hid]
  have hroot (root : ℂ) (hr : root ∈ M.charpoly.roots) : z - root ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hzroot
    apply heval
    rw [hzroot]
    exact (Polynomial.mem_roots M.charpoly_monic.ne_zero).mp hr
  calc
    _ = (-b)⁻¹ * Matrix.trace (M * D⁻¹) := by
      rw [hscale, inverse_smul D hunit (-b) (neg_ne_zero.mpr hb),
        Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    _ = (-b)⁻¹ * (z * (M.charpoly.roots.map (fun root => 1 / (z - root))).sum -
        (Fintype.card n : ℂ)) := by
      rw [trace_mul_inverse_resolvent M z hunit, trace_inverse_eq_sum_roots M z hunit]
    _ = (M.charpoly.roots.map (fun root => (-b)⁻¹ * (z * (1 / (z - root)) - 1))).sum := by
      rw [Multiset.sum_map_mul_left, Multiset.sum_map_sub, Multiset.sum_map_mul_left]
      simp only [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one, roots_card]
    _ = _ := by
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro root hr
      have hd := hroot root hr
      have hre : a + b * root = (-b) * (z - root) := by
        dsimp [z]
        field_simp
        ring
      rw [hre]
      field_simp [hb, hd]
      ring

/-- Rational trace identity for arbitrary complex matrices. Invertibility
of the denominator is the only spectral hypothesis; nonzero scalar root
denominators are derived internally. -/
theorem trace_rational_eq_sum_roots (M : Matrix n n ℂ) (a b : ℂ)
    (hD : IsUnit (a • (1 : Matrix n n ℂ) + b • M)) :
    Matrix.trace (M * (a • (1 : Matrix n n ℂ) + b • M)⁻¹) =
      (M.charpoly.roots.map (fun root => root / (a + b * root))).sum := by
  by_cases hb : b = 0
  · subst b
    by_cases ha : a = 0
    · subst a
      simp
    · rw [zero_smul, add_zero, inverse_smul (1 : Matrix n n ℂ) isUnit_one a ha,
        inv_one, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul,
        Matrix.trace_eq_sum_roots_charpoly]
      simp only [zero_mul, add_zero, div_eq_mul_inv, Multiset.sum_map_mul_right, Multiset.map_id']
      ring
  · exact trace_rational_nonzero_slope M a b hb hD

/-- The compact real-parameter kernel used in the trace-root integral. -/
theorem trace_interval_kernel_eq_sum_roots (M : Matrix n n ℂ) (t : ℝ)
    (hD : IsUnit (((t : ℂ)^2) • (1 : Matrix n n ℂ) + ((1-(t : ℂ))^2) • M)) :
    Matrix.trace (M * (((t : ℂ)^2) • (1 : Matrix n n ℂ) + ((1-(t : ℂ))^2) • M)⁻¹) =
      (M.charpoly.roots.map (fun root => root / ((t : ℂ)^2 + (1-(t : ℂ))^2 * root))).sum :=
  trace_rational_eq_sum_roots M ((t : ℂ)^2) ((1-(t : ℂ))^2) hD

end MatrixSpencer.KSRationalTraceRoots
