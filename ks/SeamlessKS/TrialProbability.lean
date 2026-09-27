import SeamlessKS.Progress

/-!
# Conditional finite-trial probability for the seamless KS walk

This file is a generic INTERNAL probability lemma. `StepBounds` explicitly
assumes the local entropy and potential inequalities for the supplied actual
Boolean transition. It does not construct or certify that transition. The
concrete smooth-source algorithm must discharge these hypotheses separately.

The run is the actual finite `KSFiniteCoinRun.runTree`, including unfinished
cutoff leaves. Its ledger is `F + rho + beta U`, and its final acceptance
predicate tests both completion and a numerical norm report. No old KS walk,
retirement controller, or old signing theorem is invoked.
-/

open scoped BigOperators
noncomputable section
namespace SeamlessKS.TrialProbability

open MatrixSpencer
open MatrixSpencer.KSFiniteCoinRun
open MatrixSpencer.FiniteBranchingTermination

attribute [local instance] Classical.propDecidable

variable {State : Type*}

/-- The spectral account whose local expected increase is nonpositive. -/
def ledger (F U : State → ℝ) (rho beta : ℝ) (s : State) : ℝ :=
  F s + rho + beta * U s

/-- All local analytic obligations are visible hypotheses here. In an
application the state type may be a subtype containing its proved cube and
debit invariants. `c` is the common squared movement parameter. -/
structure StepBounds (terminal : State → Prop) (step : State → Bool → State)
    (F U discrepancy report : State → ℝ) (rho beta c delta : ℝ) : Prop where
  delta_pos : 0 < delta
  c_pos : 0 < c
  beta_nonneg : 0 ≤ beta
  entropy_nonneg : ∀ s, 0 ≤ U s
  entropy_drop : ∀ s, ¬terminal s →
    (U (step s false) + U (step s true)) / 2 ≤ U s - c
  potential_drift : ∀ s, ¬terminal s →
    (F (step s false) + F (step s true)) / 2 ≤ F s + beta * c
  discrepancy_nonneg : ∀ s, 0 ≤ discrepancy s
  discrepancy_le : ∀ s, discrepancy s ≤ F s + rho
  report_accuracy : ∀ s, terminal s → |report s - discrepancy s| ≤ delta

variable {terminal : State → Prop} {step : State → Bool → State}
  {F U discrepancy report : State → ℝ} {rho beta c delta : ℝ}

/-- The two drift allowances cancel in the actual ledger. -/
theorem ledger_local (h : StepBounds terminal step F U discrepancy report rho beta c delta)
    (s : State) (hs : ¬terminal s) :
    (ledger F U rho beta (step s false) + ledger F U rho beta (step s true))/2 ≤
      ledger F U rho beta s := by
  have he := mul_le_mul_of_nonneg_left (h.entropy_drop s hs) h.beta_nonneg
  have hf := h.potential_drift s hs
  dsimp only [ledger]
  nlinarith

/-- The account dominates the actual norm-like discrepancy at every state. -/
theorem discrepancy_le_ledger
    (h : StepBounds terminal step F U discrepancy report rho beta c delta) (s : State) :
    discrepancy s ≤ ledger F U rho beta s := by
  dsimp only [ledger]
  linarith [h.discrepancy_le s, mul_nonneg h.beta_nonneg (h.entropy_nonneg s)]

theorem ledger_nonneg
    (h : StepBounds terminal step F U discrepancy report rho beta c delta) (s : State) :
    0 ≤ ledger F U rho beta s :=
  (h.discrepancy_nonneg s).trans (discrepancy_le_ledger h s)

/-- Finite-tree telescoping, valid also on unfinished cutoff leaves. -/
theorem expected_ledger_le
    (h : StepBounds terminal step F U discrepancy report rho beta c delta)
    (T : ℕ) (s : State) :
    expectation terminal step T s (ledger F U rho beta) ≤ ledger F U rho beta s := by
  change (runTree terminal step T s).expectation _ ≤ _
  apply Tree.expectation_le_of_local
  intro z b hb
  rcases hb with ⟨hz, rfl⟩
  rw [coinTransition_average]
  exact ledger_local h z hz

/-- Entropy bounds the number of actual moves, not the padded horizon. -/
theorem entropy_expected_steps_le
    (h : StepBounds terminal step F U discrepancy report rho beta c delta)
    (T : ℕ) (s : State) :
    c * expectedSteps terminal step T s ≤ U s := by
  have ht := progress_telescope terminal step (fun z => -U z) c
    (fun z hz => by have := h.entropy_drop z hz; linarith) T s
  have hn := expectation_nonneg terminal step T s U h.entropy_nonneg
  change -U s + c * expectedSteps terminal step T s ≤
    (runTree terminal step T s).expectation (fun z => -U z) at ht
  rw [Tree.expectation_neg] at ht
  change 0 ≤ (runTree terminal step T s).expectation U at hn
  linarith

/-- The stated horizon condition is the only time-budget input. -/
theorem active_probability_le_eighth
    (h : StepBounds terminal step F U discrepancy report rho beta c delta)
    (T : ℕ) (hT : 0 < T) (s : State)
    (horizon : 8 * U s ≤ c * (T : ℝ)) :
    activeProbability terminal step T s ≤ (1 : ℝ)/8 := by
  have ht := mul_le_mul_of_nonneg_left
    (horizon_mul_activeProbability_le terminal step T s) h.c_pos.le
  have he := entropy_expected_steps_le h T s
  have hp : 0 < c * (T : ℝ) := mul_pos h.c_pos (by exact_mod_cast hT)
  nlinarith

/-- Acceptance checks the actual terminal predicate and the norm report. -/
def accepts (terminal : State → Prop) (report : State → ℝ) (delta : ℝ)
    (s : State) : Bool := decide (terminal s ∧ report s ≤ 399 * delta)

theorem accepts_iff (s : State) :
    accepts terminal report delta s = true ↔ terminal s ∧ report s ≤ 399 * delta := by
  simp [accepts]

/-- Every accepted output has the deterministic discrepancy bound. -/
theorem accepts_sound
    (h : StepBounds terminal step F U discrepancy report rho beta c delta)
    (s : State) (ha : accepts terminal report delta s = true) :
    terminal s ∧ discrepancy s ≤ 400 * delta := by
  obtain ⟨ht, hr⟩ := (accepts_iff s).mp ha
  have he := (abs_le.mp (h.report_accuracy s ht)).1
  exact ⟨ht, by linarith⟩

/-- A completed state below the inner threshold is certainly accepted. -/
theorem completed_small_accepted
    (h : StepBounds terminal step F U discrepancy report rho beta c delta)
    (s : State) (ht : terminal s) (hd : discrepancy s ≤ 398 * delta) :
    accepts terminal report delta s = true := by
  apply (accepts_iff s).mpr
  have he := (abs_le.mp (h.report_accuracy s ht)).2
  exact ⟨ht, by linarith⟩

def failureProbability (terminal : State → Prop) (step : State → Bool → State)
    (report : State → ℝ) (delta : ℝ) (T : ℕ) (s : State) : ℝ :=
  expectation terminal step T s (fun z => if accepts terminal report delta z then 0 else 1)

def acceptanceProbability (terminal : State → Prop) (step : State → Bool → State)
    (report : State → ℝ) (delta : ℝ) (T : ℕ) (s : State) : ℝ :=
  expectation terminal step T s (fun z => if accepts terminal report delta z then 1 else 0)

def badNormProbability (terminal : State → Prop) (step : State → Bool → State)
    (discrepancy : State → ℝ) (a : ℝ) (T : ℕ) (s : State) : ℝ :=
  expectation terminal step T s (fun z => if a < discrepancy z then 1 else 0)

/-- A finite Markov bound obtained directly from positive leaf weights. -/
theorem bad_norm_probability_le
    (h : StepBounds terminal step F U discrepancy report rho beta c delta)
    (T : ℕ) (s : State) {a : ℝ} (ha : 0 < a) :
    badNormProbability terminal step discrepancy a T s ≤ ledger F U rho beta s / a := by
  apply (le_div_iff₀ ha).mpr
  calc
    badNormProbability terminal step discrepancy a T s * a ≤
        expectation terminal step T s (ledger F U rho beta) := by
      unfold badNormProbability expectation Tree.expectation
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro l _
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Tree.leafWeight_pos _ l).le
      dsimp only
      split_ifs with hl
      · simpa only [one_mul] using hl.le.trans (discrepancy_le_ledger h _)
      · simpa only [zero_mul] using ledger_nonneg h _
    _ ≤ ledger F U rho beta s := expected_ledger_le h T s

/-- Rejection is contained in noncompletion union the bad-norm event. -/
theorem failure_probability_le_union
    (h : StepBounds terminal step F U discrepancy report rho beta c delta)
    (T : ℕ) (s : State) :
    failureProbability terminal step report delta T s ≤
      activeProbability terminal step T s +
        badNormProbability terminal step discrepancy (398 * delta) T s := by
  unfold failureProbability activeProbability badNormProbability expectation Tree.expectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro l _
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Tree.leafWeight_pos _ l).le
  dsimp only
  let z := (runTree terminal step T s).leafState l
  change (if accepts terminal report delta z then 0 else 1) ≤
    MatrixSpencer.KSStoppedProgress.activeIndicator terminal z +
      (if 398 * delta < discrepancy z then 1 else 0)
  by_cases ht : terminal z
  · by_cases hd : discrepancy z ≤ 398 * delta
    · have ha := completed_small_accepted h z ht hd
      simp [ha, MatrixSpencer.KSStoppedProgress.activeIndicator, ht, not_lt.mpr hd]
    · have hb : 398 * delta < discrepancy z := lt_of_not_ge hd
      simp only [MatrixSpencer.KSStoppedProgress.activeIndicator, if_pos ht, hb,
        ↓reduceIte, zero_add]
      split_ifs <;> norm_num
  · simp only [MatrixSpencer.KSStoppedProgress.activeIndicator, if_neg ht]
    split_ifs <;> norm_num

theorem acceptance_add_failure (T : ℕ) (s : State) :
    acceptanceProbability terminal step report delta T s +
      failureProbability terminal step report delta T s = 1 := by
  unfold acceptanceProbability failureProbability expectation Tree.expectation
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ l, (runTree terminal step T s).leafWeight l := by
      apply Finset.sum_congr rfl
      intro l _
      dsimp only
      split_ifs <;> ring
    _ = 1 := Tree.leafWeight_sum _

/-- The precise one-trial rejection estimate, under explicit step bounds. -/
theorem one_trial_failure_le
    (h : StepBounds terminal step F U discrepancy report rho beta c delta)
    (T : ℕ) (hT : 0 < T) (s : State)
    (horizon : 8 * U s ≤ c * (T : ℝ))
    (initial : ledger F U rho beta s ≤ 36 * delta) :
    failureProbability terminal step report delta T s ≤ (1 : ℝ)/8 + 36/398 := by
  have hdelta := h.delta_pos
  have hactive := active_probability_le_eighth h T hT s horizon
  have hbad := bad_norm_probability_le h T s (a := 398*delta) (by positivity)
  have hratio : ledger F U rho beta s / (398*delta) ≤ (36 : ℝ)/398 := by
    apply (div_le_iff₀ (show 0 < 398*delta by positivity)).mpr
    nlinarith [initial]
  exact (failure_probability_le_union h T s).trans (add_le_add hactive (hbad.trans hratio))

theorem one_trial_failure_lt_quarter
    (h : StepBounds terminal step F U discrepancy report rho beta c delta)
    (T : ℕ) (hT : 0 < T) (s : State)
    (horizon : 8 * U s ≤ c * (T : ℝ))
    (initial : ledger F U rho beta s ≤ 36 * delta) :
    failureProbability terminal step report delta T s < (1 : ℝ)/4 :=
  (one_trial_failure_le h T hT s horizon initial).trans_lt (by norm_num)

theorem one_trial_acceptance_ge_three_quarters
    (h : StepBounds terminal step F U discrepancy report rho beta c delta)
    (T : ℕ) (hT : 0 < T) (s : State)
    (horizon : 8 * U s ≤ c * (T : ℝ))
    (initial : ledger F U rho beta s ≤ 36 * delta) :
    (3 : ℝ)/4 ≤ acceptanceProbability terminal step report delta T s := by
  have hf := one_trial_failure_lt_quarter h T hT s horizon initial
  have ht := acceptance_add_failure (terminal := terminal) (step := step)
    (report := report) (delta := delta) T s
  linarith


theorem initial_ledger_bound (s : State)
    (hF : F s ≤ 34 * delta) (hrho : rho ≤ delta)
    (hentropy : beta * U s ≤ delta) :
    ledger F U rho beta s ≤ 36 * delta := by
  dsimp only [ledger]
  linarith

/-- The checked coordinate entropy bound supplies a dimension-only
initial budget for every cube state. -/
theorem entropy_le_two_labels {N : ℕ} (x : Fin N → ℝ)
    (hx : ∀ i, |x i| ≤ 1) : Progress.entropy x ≤ 2 * (N : ℝ) := by
  have hu := (Progress.entropy_bounds hx).2
  have hl : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hmul := mul_le_mul_of_nonneg_left hl (show 0 ≤ (N : ℝ) from Nat.cast_nonneg N)
  nlinarith


theorem horizon_from_labels {N : ℕ} (x : Fin N → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (T : ℕ) (horizon : 16 * (N : ℝ) ≤ c * (T : ℝ)) :
    8 * Progress.entropy x ≤ c * (T : ℝ) := by
  have hu := entropy_le_two_labels x hx
  linarith

/-! The following independent finite-product sampler is generic. It uses
fresh trial weights and returns the first accepted outcome. All its
normalization and multiplication identities are proved here. -/
namespace Retry

universe v w
variable {L : Type v} {S : Type w}

/-- The leaves of a finite independent product sampler. -/
def Draws (L : Type v) : ℕ → Type v
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

end Retry

/-- Literal first-accepted output on independent copies of the actual
truncated coin-run leaves. It does not select a favorable leaf. -/
def trialRetry (terminal : State → Prop) (step : State → Bool → State)
    (report : State → ℝ) (delta : ℝ) (T : ℕ) (s : State) (r : ℕ) :
    Retry.Draws (runTree terminal step T s).Leaves r → Option State :=
  Retry.firstAccepted (runTree terminal step T s).leafState
    (fun l => accepts terminal report delta ((runTree terminal step T s).leafState l)) r

theorem trialRetry_sound
    (h : StepBounds terminal step F U discrepancy report rho beta c delta)
    (T : ℕ) (s : State) (r : ℕ)
    (z : Retry.Draws (runTree terminal step T s).Leaves r) (out : State)
    (hout : trialRetry terminal step report delta T s r z = some out) :
    terminal out ∧ discrepancy out ≤ 400 * delta := by
  exact Retry.firstAccepted_sound _ _ (fun q => terminal q ∧ discrepancy q ≤ 400 * delta)
    (fun l hl => accepts_sound h _ hl) r z out hout

/-- Independent repetition of the actual trial has geometric failure. -/
theorem trialRetry_failure_le
    (h : StepBounds terminal step F U discrepancy report rho beta c delta)
    (T : ℕ) (hT : 0 < T) (s : State)
    (horizon : 8 * U s ≤ c * (T : ℝ))
    (initial : ledger F U rho beta s ≤ 36 * delta) (r : ℕ) :
    Retry.failureProbability (runTree terminal step T s).leafWeight
      (runTree terminal step T s).leafState
      (fun l => accepts terminal report delta ((runTree terminal step T s).leafState l)) r ≤
        (1/4 : ℝ)^r := by
  rw [Retry.failureProbability_eq_pow]
  apply pow_le_pow_left₀
    (Retry.singleFailure_nonneg _ (fun l => (Tree.leafWeight_pos _ l).le) _)
  change failureProbability terminal step report delta T s ≤ (1 : ℝ)/4
  exact (one_trial_failure_lt_quarter h T hT s horizon initial).le

/-- The probability is the finite product-weight sum of the actual
first-accepted return event. -/
theorem trialRetry_success_ge
    (h : StepBounds terminal step F U discrepancy report rho beta c delta)
    (T : ℕ) (hT : 0 < T) (s : State)
    (horizon : 8 * U s ≤ c * (T : ℝ))
    (initial : ledger F U rho beta s ≤ 36 * delta) (r : ℕ) :
    1-(1/4 : ℝ)^r ≤
    Retry.successProbability (runTree terminal step T s).leafWeight
      (runTree terminal step T s).leafState
      (fun l => accepts terminal report delta ((runTree terminal step T s).leafState l)) r := by
  have hf := trialRetry_failure_le h T hT s horizon initial r
  have hs := Retry.success_add_failure (runTree terminal step T s).leafWeight
    (Tree.leafWeight_sum _) (runTree terminal step T s).leafState
    (fun l => accepts terminal report delta ((runTree terminal step T s).leafState l)) r
  linarith

end SeamlessKS.TrialProbability
