import MatrixSpencer.KSComplexRootTraceBound

/-!
# Explicit complex objective value bounds

These inequalities control the linear, fidelity-trace and regularizer-trace
terms on a complex neighborhood. The matrices need not be normal. The trace
terms' analytic identification is separate from this scalar norm arithmetic.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSComplexObjectiveBound

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem norm_trace_le_card_mul_norm (A : Matrix n n ℂ) :
    ‖Matrix.trace A‖ ≤ (Fintype.card n : ℝ) * ‖A‖ := by
  have hs : Real.sqrt ‖A * A‖ ≤ ‖A‖ :=
    Real.sqrt_le_iff.mpr ⟨norm_nonneg A, by simpa only [pow_two] using norm_mul_le A A⟩
  exact (KSComplexRootTraceBound.trace_norm_le_card_sqrt_norm (Q := A) rfl).trans
    (mul_le_mul_of_nonneg_left hs (by positivity))

theorem norm_trace_mul_le_card_mul_norm (H S : Matrix n n ℂ) :
    ‖Matrix.trace (H * S)‖ ≤ (Fintype.card n : ℝ) * ‖H‖ * ‖S‖ := by
  have hh := mul_le_mul_of_nonneg_left (norm_mul_le H S)
    (show (0 : ℝ) ≤ Fintype.card n from by positivity)
  exact (norm_trace_le_card_mul_norm (H * S)).trans (by simpa only [mul_assoc] using hh)

def value (H S : Matrix n n ℂ) (q r : ℂ) (θ : ℝ) : ℂ :=
  Matrix.trace (H * S) + 2 * q + 2 * (θ : ℂ) * r

def valueCap (d : ℕ) (R s m θ : ℝ) : ℝ :=
  (d : ℝ) * R * s + 2 * d * Real.sqrt (s * m) + 2 * θ * d * Real.sqrt s

theorem valueCap_nonneg (d : ℕ) {R s m θ : ℝ}
    (hR : 0 ≤ R) (hs : 0 ≤ s) (hθ : 0 ≤ θ) : 0 ≤ valueCap d R s m θ := by
  unfold valueCap
  positivity

theorem value_norm_le (H S : Matrix n n ℂ) (q r : ℂ) {R s m θ : ℝ}
    (hθ : 0 ≤ θ) (hR : 0 ≤ R)
    (hH : ‖H‖ ≤ R) (hS : ‖S‖ ≤ s)
    (hq : ‖q‖ ≤ (Fintype.card n : ℝ) * Real.sqrt (s * m))
    (hr : ‖r‖ ≤ (Fintype.card n : ℝ) * Real.sqrt s) :
    ‖value H S q r θ‖ ≤ valueCap (Fintype.card n) R s m θ := by
  have hlin := norm_trace_mul_le_card_mul_norm H S
  have hlin' : ‖Matrix.trace (H * S)‖ ≤ (Fintype.card n : ℝ) * R * s := by
    exact hlin.trans (by gcongr)
  unfold value valueCap
  calc _ ≤ ‖Matrix.trace (H * S)‖ + ‖2 * q‖ + ‖2 * (θ : ℂ) * r‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ = ‖Matrix.trace (H * S)‖ + 2 * ‖q‖ + 2 * θ * ‖r‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ]
      norm_num
    _ ≤ (Fintype.card n : ℝ) * R * s +
        2 * ((Fintype.card n : ℝ) * Real.sqrt (s * m)) +
        2 * θ * ((Fintype.card n : ℝ) * Real.sqrt s) := by gcongr
    _ = _ := by ring

end MatrixSpencer.KSComplexObjectiveBound
