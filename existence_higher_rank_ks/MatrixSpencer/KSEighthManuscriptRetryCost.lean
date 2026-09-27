import MatrixSpencer.KSEighthManuscriptRetry

/-!
# Actual short-circuit retry work

Only trials inspected before the first acceptance incur cost. The supplied
per-trial cost is explicit bookkeeping, to be instantiated by an execution
cost theorem; these lemmas alone are not a primitive-operation runtime claim.
-/
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptRetryCost
open KSEighthManuscriptRetry
variable {L : Type} [Fintype L]

def work (cost : L → ℕ) (accept : L → Bool) : (r : ℕ) → Draws L r → ℕ
  | 0, _ => 0
  | r+1, z => cost z.1 + if accept z.1 then 0 else work cost accept r z.2

theorem work_le (cost : L → ℕ) (accept : L → Bool) {B : ℕ}
    (hcost : ∀ l, cost l ≤ B) : ∀ r z, work cost accept r z ≤ r*B := by
  intro r
  induction r with
  | zero => intro z; simp [work]
  | succ r ih =>
    intro z
    rw [work]
    split_ifs
    · simpa only [add_zero, Nat.succ_mul] using
        (hcost z.1).trans (Nat.le_add_left B (r*B))
    · have h := Nat.add_le_add (hcost z.1) (ih z.2)
      simpa only [Nat.succ_mul, Nat.add_comm] using h

def expectedWork (w : L → ℝ) (cost : L → ℕ) (accept : L → Bool) (r : ℕ) : ℝ :=
  ∑ z : Draws L r, weight w r z * work cost accept r z

theorem expectedWork_nonneg (w : L → ℝ) (hw : ∀ l, 0 ≤ w l)
    (cost : L → ℕ) (accept : L → Bool) (r : ℕ) : 0 ≤ expectedWork w cost accept r :=
  Finset.sum_nonneg fun z _ => mul_nonneg (weight_nonneg w hw r z) (Nat.cast_nonneg _)

theorem expectedWork_succ (w : L → ℝ) (hwsum : (∑ l, w l) = 1)
    (cost : L → ℕ) (accept : L → Bool) (r : ℕ) :
    expectedWork w cost accept (r+1) = (∑ l, w l * (cost l : ℝ)) +
      singleFailure w accept * expectedWork w cost accept r := by
  change (∑ z : L × Draws L r, (w z.1 * weight w r z.2) *
    ((cost z.1 + if accept z.1 then 0 else work cost accept r z.2 : ℕ) : ℝ)) = _
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ l, (w l * (cost l : ℝ) + w l * (if accept l then 0 else 1) *
        expectedWork w cost accept r) := by
      apply Finset.sum_congr rfl
      intro l _
      cases ha : accept l
      · simp only [ha, Bool.false_eq_true, ↓reduceIte, Nat.cast_add, mul_add,
          Finset.sum_add_distrib, expectedWork, Finset.mul_sum, mul_one]
        rw [show (∑ z : Draws L r, w l * weight w r z * (cost l : ℝ)) =
          w l * (cost l : ℝ) by
            calc
              _ = (w l * (cost l : ℝ)) * ∑ z : Draws L r, weight w r z := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
              _ = _ := by rw [weight_sum w hwsum r, mul_one]]
        congr 1
        apply Finset.sum_congr rfl
        intro z _
        ring
      · simp only [ha, ↓reduceIte, add_zero, zero_mul, mul_zero]
        calc
          _ = (w l * (cost l : ℝ)) * ∑ z : Draws L r, weight w r z := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
          _ = _ := by rw [weight_sum w hwsum r, mul_one]
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]; rfl

/-- With at least half acceptance, the expected inspected trial work is
at most twice a uniform per-trial work bound, regardless of the retry cap. -/
theorem expectedWork_le_two (w : L → ℝ) (hw : ∀ l, 0 ≤ w l)
    (hwsum : (∑ l, w l) = 1) (cost : L → ℕ) (accept : L → Bool)
    {B : ℝ} (hB : 0 ≤ B) (hcost : ∀ l, (cost l : ℝ) ≤ B)
    (htrial : (1 : ℝ)/2 ≤ singleSuccess w accept) (r : ℕ) :
    expectedWork w cost accept r ≤ 2*B := by
  have hf := singleFailure_nonneg w hw accept
  have hsum := single_success_add_failure w hwsum accept
  have hfail : singleFailure w accept ≤ 1/2 := by linarith
  have hc : (∑ l, w l * (cost l : ℝ)) ≤ B := by
    calc
      _ ≤ ∑ l, w l * B := Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hcost l) (hw l)
      _ = B := by rw [← Finset.sum_mul, hwsum, one_mul]
  induction r with
  | zero => simp [expectedWork, Draws, work]; positivity
  | succ r ih =>
    rw [expectedWork_succ w hwsum]
    have h := mul_le_mul_of_nonneg_left ih hf
    have h' := mul_le_mul_of_nonneg_right hfail (show 0 ≤ 2*B by positivity)
    linarith

end MatrixSpencer.KSEighthManuscriptRetryCost
