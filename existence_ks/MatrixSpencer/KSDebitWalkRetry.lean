import MatrixSpencer.KSDebitWalkAcceptance

/-!
# Finite independent retries with an explicit first-accepted output

Each draw is an actual path occurrence of the already defined finite coin
walk. The finite product weight implements independence, and `firstAccepted`
returns the first numerically accepted leaf or `none` after the stated
number of attempts. Subsequent prospective draws are ignored after success.

The failure probability is proved to be the single-attempt failure
probability to the retry count. The concrete `41/56` attempt bound gives
failure at most `(15/56)^r`. Accurate controller reports, directions, and
local potential drift remain explicit premises in the final composition.
-/

open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSDebitWalkRetry

namespace FiniteRetry

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

theorem successProbability_ge [Fintype L] (w : L → ℝ) (hw : ∀ l, 0 ≤ w l)
    (hwsum : (∑ l, w l) = 1) (output : L → S) (accept : L → Bool)
    (htrial : (41 : ℝ) / 56 ≤ singleSuccess w accept) (r : ℕ) :
    1 - ((15 : ℝ) / 56) ^ r ≤ successProbability w output accept r := by
  have hsum := single_success_add_failure w hwsum accept
  have hfailure : singleFailure w accept ≤ (15 : ℝ) / 56 := by linarith
  have hp := pow_le_pow_left₀ (singleFailure_nonneg w hw accept) hfailure r
  have htotal := success_add_failure w hwsum output accept r
  rw [failureProbability_eq_pow] at htotal
  linarith

end FiniteRetry

open KSDebitWalkRun KSDebitWalkAcceptance
variable {N d : ℕ} [Nonempty (Fin d)]

/-- A fresh attempt always starts with the specified preparation of zero. -/
abbrev Attempt (C : Controller N (Fin d)) (T : ℕ) := (run C T (initialState C)).Leaves
abbrev Draws (C : Controller N (Fin d)) (T r : ℕ) := FiniteRetry.Draws (Attempt C T) r

def retry (C : Controller N (Fin d)) (T : ℕ) (ν a : ℝ) (r : ℕ) :
    Draws C T r → Option (State C) :=
  FiniteRetry.firstAccepted (run C T (initialState C)).leafState
    (fun l => accepts C ν a ((run C T (initialState C)).leafState l)) r

theorem retry_sound (C : Controller N (Fin d)) (T : ℕ) {ν a : ℝ} (hν : 0 < ν)
    (r : ℕ) (z : Draws C T r) (s : State C) (hout : retry C T ν a r z = some s) :
    (∀ i, IsSign (s.coeff i)) ∧ ‖signedMatrix C s‖ ≤ a :=
  FiniteRetry.firstAccepted_sound (run C T (initialState C)).leafState
    (fun l => accepts C ν a ((run C T (initialState C)).leafState l))
    (fun q => (∀ i, IsSign (q.coeff i)) ∧ ‖signedMatrix C q‖ ≤ a)
    (fun l hl => accepts_sound C hν ((run C T (initialState C)).leafState l) hl) r z s hout

def successProbability (C : Controller N (Fin d)) (T : ℕ) (ν a : ℝ) (r : ℕ) : ℝ :=
  FiniteRetry.successProbability (run C T (initialState C)).leafWeight
    (run C T (initialState C)).leafState
    (fun l => accepts C ν a ((run C T (initialState C)).leafState l)) r

/-- The success event is literally `isSome` of the first-accepted output,
summed over the explicit finite independent draw weights. -/
theorem successProbability_eq_draw_sum (C : Controller N (Fin d)) (T : ℕ)
    (ν a : ℝ) (r : ℕ) :
    successProbability C T ν a r = ∑ z : Draws C T r,
      FiniteRetry.weight (run C T (initialState C)).leafWeight r z *
        (if (retry C T ν a r z).isSome then 1 else 0) := rfl

theorem successProbability_ge_of_attempt (C : Controller N (Fin d)) (T : ℕ) (ν a : ℝ)
    (htrial : (41 : ℝ) / 56 ≤ acceptanceProbability C T (initialState C) ν a) (r : ℕ) :
    1 - ((15 : ℝ) / 56) ^ r ≤ successProbability C T ν a r :=
  FiniteRetry.successProbability_ge _ (fun l => ((run C T (initialState C)).leafWeight_pos l).le)
    (run C T (initialState C)).leafWeight_sum _ _ htrial r

/-- Repeated actual numerical trials, with all controller and drift
requirements visible, succeed with the explicit geometric probability. -/
theorem successProbability_from_zero_ge (C : Controller N (Fin d))
    (hparseval : (∑ i, KSRankOne.atom (C.vectors i)) = 1)
    (hηbudget : (N : ℝ) * C.η ≤ C.δ) {ε β : ℝ} (hεpos : 0 < ε)
    (hε : ∀ i, ‖KSRankOne.atom (C.vectors i)‖ ≤ ε)
    (hθ : C.θ = ksRegularizerScale ε (Fin d)) (hδ : C.δ = Real.sqrt ε)
    (hβ : 0 ≤ β) (hdrift : KSDebitWalkQuality.LocalPotentialDrift C β)
    (hdriftBudget : β * ((N : ℝ) * (2 * Real.log 2)) ≤ C.δ)
    (T : ℕ) (hT : 0 < T)
    (htime : ((N : ℝ) * (2 * Real.log 2)) / (C.stepSize ^ 2 * (T : ℝ)) ≤ 1 / 8)
    (r : ℕ) :
    1 - ((15 : ℝ) / 56) ^ r ≤ successProbability C T
      (2 * (16 * Real.sqrt 2 + 5) * C.δ) (9 * (16 * Real.sqrt 2 + 5) * C.δ) r :=
  successProbability_ge_of_attempt C T _ _
    (acceptanceProbability_from_zero_ge C hparseval hηbudget hεpos hε hθ hδ
      hβ hdrift hdriftBudget T hT htime) r

end MatrixSpencer.KSDebitWalkRetry
