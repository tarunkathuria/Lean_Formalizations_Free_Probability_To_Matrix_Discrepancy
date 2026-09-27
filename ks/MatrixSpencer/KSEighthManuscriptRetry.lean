import MatrixSpencer.KSEighthManuscriptBranchingDrift


open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptRetry

variable {L S : Type}

/-- The leaves of a finite independent product sampler. -/
def Draws (L : Type) : ℕ → Type
  | 0 => PUnit
  | r + 1 => L × Draws L r

instance drawsFintype [Fintype L] : (r : ℕ) → Fintype (Draws L r)
  | 0 => inferInstanceAs (Fintype PUnit)
  | r + 1 => @instFintypeProd L (Draws L r) inferInstance (drawsFintype r)

def weight (w : L → ℝ) : (r : ℕ) → Draws L r → ℝ
  | 0, _ => 1
  | r + 1, z => w z.1 * weight w r z.2

theorem weight_nonneg (w : L → ℝ) (hw : ∀ l, 0 ≤ w l) :
    ∀ r z, 0 ≤ weight w r z := by
  intro r
  induction r with
  | zero => intro z; exact zero_le_one
  | succ r ih => intro z; exact mul_nonneg (hw z.1) (ih z.2)

theorem weight_sum [Fintype L] (w : L → ℝ) (hw : (∑ l, w l) = 1) :
    ∀ r, (∑ z : Draws L r, weight w r z) = 1 := by
  intro r
  induction r with
  | zero => simp [Draws, weight]
  | succ r ih =>
    change (∑ z : L × Draws L r, w z.1 * weight w r z.2) = 1
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ih, mul_one, hw]

/-- The first accepted output; exhaustion is the explicit value `none`. -/
def firstAccepted (output : L → S) (accept : L → Bool) :
    (r : ℕ) → Draws L r → Option S
  | 0, _ => none
  | r + 1, z => if accept z.1 then some (output z.1) else firstAccepted output accept r z.2

theorem firstAccepted_sound (output : L → S) (accept : L → Bool)
    (P : S → Prop) (hsound : ∀ l, accept l = true → P (output l)) :
    ∀ r z s, firstAccepted output accept r z = some s → P s := by
  intro r
  induction r with
  | zero => intro z s h; cases h
  | succ r ih =>
    intro z s h
    simp only [firstAccepted] at h
    split_ifs at h with ha
    · cases h
      exact hsound z.1 ha
    · exact ih z.2 s h

def failureIndicator (result : Option S) : ℝ := if result.isSome then 0 else 1
def successIndicator (result : Option S) : ℝ := if result.isSome then 1 else 0

def failureProbability [Fintype L] (w : L → ℝ) (output : L → S) (accept : L → Bool)
    (r : ℕ) : ℝ :=
  ∑ z : Draws L r, weight w r z * failureIndicator (firstAccepted output accept r z)

def successProbability [Fintype L] (w : L → ℝ) (output : L → S) (accept : L → Bool)
    (r : ℕ) : ℝ :=
  ∑ z : Draws L r, weight w r z * successIndicator (firstAccepted output accept r z)

def singleSuccess [Fintype L] (w : L → ℝ) (accept : L → Bool) : ℝ :=
  ∑ l, w l * (if accept l then 1 else 0)

def singleFailure [Fintype L] (w : L → ℝ) (accept : L → Bool) : ℝ :=
  ∑ l, w l * (if accept l then 0 else 1)

theorem singleFailure_nonneg [Fintype L] (w : L → ℝ) (hw : ∀ l, 0 ≤ w l)
    (accept : L → Bool) : 0 ≤ singleFailure w accept := by
  apply Finset.sum_nonneg
  intro l _
  apply mul_nonneg (hw l)
  split_ifs <;> norm_num

theorem single_success_add_failure [Fintype L] (w : L → ℝ) (hw : (∑ l, w l) = 1)
    (accept : L → Bool) : singleSuccess w accept + singleFailure w accept = 1 := by
  unfold singleSuccess singleFailure
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ l, w l := by
      apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> ring
    _ = 1 := hw

theorem failureProbability_eq_pow [Fintype L] (w : L → ℝ) (output : L → S)
    (accept : L → Bool) : ∀ r, failureProbability w output accept r = singleFailure w accept ^ r := by
  intro r
  induction r with
  | zero => simp [failureProbability, Draws, weight, firstAccepted, failureIndicator]
  | succ r ih =>
    change (∑ z : L × Draws L r, (w z.1 * weight w r z.2) *
      failureIndicator (if accept z.1 then some (output z.1)
        else firstAccepted output accept r z.2)) = _
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ l, w l * (if accept l then 0 else 1) * failureProbability w output accept r := by
        apply Finset.sum_congr rfl
        intro l _
        cases ha : accept l
        · simp only [ha, Bool.false_eq_true, ↓reduceIte, mul_one, failureProbability,
            Finset.mul_sum, mul_assoc]
        · simp only [ha, ↓reduceIte, failureIndicator, Option.isSome_some, mul_zero,
            Finset.sum_const_zero, zero_mul]
      _ = singleFailure w accept * failureProbability w output accept r := by
        rw [← Finset.sum_mul]
        rfl
      _ = _ := by rw [ih, pow_succ]; ring

theorem success_add_failure [Fintype L] (w : L → ℝ) (hw : (∑ l, w l) = 1)
    (output : L → S) (accept : L → Bool) (r : ℕ) :
    successProbability w output accept r + failureProbability w output accept r = 1 := by
  unfold successProbability failureProbability
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ z : Draws L r, weight w r z := by
      apply Finset.sum_congr rfl
      intro z _
      unfold successIndicator failureIndicator
      split_ifs <;> ring
    _ = 1 := weight_sum w hw r

/-- A general retry bound for the actual first-success return event. -/
theorem successProbability_ge [Fintype L] (w : L → ℝ) (hw : ∀ l, 0 ≤ w l)
    (hwsum : (∑ l, w l) = 1) (output : L → S) (accept : L → Bool)
    {p : ℝ} (htrial : p ≤ singleSuccess w accept) (r : ℕ) :
    1 - (1-p)^r ≤ successProbability w output accept r := by
  have hsum := single_success_add_failure w hwsum accept
  have hfailure : singleFailure w accept ≤ 1-p := by linarith
  have hp := pow_le_pow_left₀ (singleFailure_nonneg w hw accept) hfailure r
  have htotal := success_add_failure w hwsum output accept r
  rw [failureProbability_eq_pow] at htotal
  linarith

/-- Constant single-trial success amplifies to the explicit geometric guarantee. -/
theorem successProbability_ge_half [Fintype L] (w : L → ℝ) (hw : ∀ l, 0 ≤ w l)
    (hwsum : (∑ l, w l) = 1) (output : L → S) (accept : L → Bool)
    (htrial : (1 : ℝ)/2 ≤ singleSuccess w accept) (r : ℕ) :
    1 - (1/2 : ℝ)^r ≤ successProbability w output accept r := by
  simpa only [show (1 : ℝ)-1/2=1/2 by norm_num] using
    successProbability_ge w hw hwsum output accept htrial r

end MatrixSpencer.KSEighthManuscriptRetry
