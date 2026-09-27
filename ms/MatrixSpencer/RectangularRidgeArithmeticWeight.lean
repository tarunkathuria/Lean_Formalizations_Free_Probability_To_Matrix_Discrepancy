import MatrixSpencer.RectangularRidgePrimitiveParameters

/-! Exact arithmetic evaluation of the tuned Tsallis weight. Only repeated
scalar square roots and field operations occur in the definition below;
real powers are used in its specification and correctness proof. -/
noncomputable section
namespace MatrixSpencer.RectangularRidgeArithmeticWeight
open RectangularRidgeTuning RectangularRidgePrimitiveParameters

def root : ℕ → ℝ → ℝ
  | 0, t => t
  | m+1, t => Real.sqrt (root m t)

theorem root_eq_rpow (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    root m t = t ^ (1 / (2 : ℝ)^m) := by
  induction m with
  | zero => simp [root]
  | succ m ih =>
    rw [root, ih, Real.sqrt_eq_rpow, ← Real.rpow_mul ht]
    congr 1
    rw [pow_succ]
    ring

def evaluate (N D : ℕ) (hN : 1 ≤ N) : ℝ :=
  let m := depth N D hN
  let p : ℝ := order N D hN
  Real.sqrt ((1-1/p) * root m 4096 * ((N : ℝ) / root m N) / ((1/p) * root m D))

/-- The formula uses three root chains of length `depth`, one final square
root and a fixed number of scalar field operations. -/
theorem evaluate_eq_weight {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    evaluate N D hN = weight N D hN := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  unfold evaluate weight RectangularParameters.strength exponent order
  dsimp only
  rw [root_eq_rpow _ (by norm_num : (0 : ℝ) ≤ 4096), root_eq_rpow _ hn.le,
    root_eq_rpow _ hd.le]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.rpow_sub hn, Real.rpow_one]

/-- An explicit polynomial bound for the scalar arithmetic used by the
displayed weight formula, including all square-root evaluations. -/
theorem operation_budget {N D : ℕ} (hN : 1 ≤ N) :
    3 * depth N D hN + 12 ≤ 3 * D + 15 := by
  have h := depth_le N D hN
  omega

end MatrixSpencer.RectangularRidgeArithmeticWeight
