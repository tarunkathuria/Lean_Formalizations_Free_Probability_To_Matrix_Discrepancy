import MatrixSpencer.KSFullManuscriptDrift
import MatrixSpencer.KSFullManuscriptAcceptance
import MatrixSpencer.KSDebitWalkRetry


open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptAlgorithm
open KSDebitWalkRun KSFullManuscriptParameters KSDebitWalkRetry.FiniteRetry
variable {N d : ℕ} [Nonempty (Fin d)]

def taylorBudget (v : Fin N → Fin d → ℂ) (ε : ℝ) : ℝ :=
  KSFullManuscriptTaylor.budget v (Real.sqrt ε) (debitTolerance N (Real.sqrt ε))
    (ksRegularizerScale ε (Fin d))

theorem taylorBudget_pos (v : Fin N → Fin d → ℂ) (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) : 0 < taylorBudget v ε :=
  KSFullManuscriptTaylor.budget_pos v (Real.sqrt_pos.mpr hε)
    (debitTolerance_pos hN (Real.sqrt_pos.mpr hε)).le (ksRegularizerScale_pos (n := Fin d) hε)

def controller (v : Fin N → Fin d → ℂ) (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) : Controller N (Fin d) :=
  KSFullManuscriptController.controller v hN (Real.sqrt_pos.mpr hε)
    (debitTolerance_pos hN (Real.sqrt_pos.mpr hε)) (ksRegularizerScale_pos (n := Fin d) hε)
    (taylorBudget_pos v hN hε) hd

def horizon (v : Fin N → Fin d → ℂ) (ε : ℝ) : ℕ :=
  cutoff N (Real.sqrt ε) (taylorBudget v ε)

def attempt (v : Fin N → Fin d → ℂ) (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) :=
  run (controller v hN hε hd) (horizon v ε) (initialState (controller v hN hε hd))

abbrev Draws (v : Fin N → Fin d → ℂ) (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ) :=
  KSDebitWalkRetry.FiniteRetry.Draws (attempt v hN hε hd).Leaves r

/-- Return the first numerically accepted full signing, or explicit failure. -/
def output (v : Fin N → Fin d → ℂ) (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ) : Draws v hN hε hd r → Option (Fin N → ℝ) :=
  firstAccepted (fun l => ((attempt v hN hε hd).leafState l).coeff)
    (fun l => KSFullManuscriptAcceptance.accepts (controller v hN hε hd)
      ((attempt v hN hε hd).leafState l)) r

def drawWeight (v : Fin N → Fin d → ℂ) (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ) : Draws v hN hε hd r → ℝ :=
  weight (attempt v hN hε hd).leafWeight r

theorem drawWeight_nonneg (v : Fin N → Fin d → ℂ) (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ) (z : Draws v hN hε hd r) :
    0 ≤ drawWeight v hN hε hd r z :=
  weight_nonneg _ (fun l => ((attempt v hN hε hd).leafWeight_pos l).le) r z

theorem drawWeight_sum (v : Fin N → Fin d → ℂ) (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ) :
    (∑z : Draws v hN hε hd r, drawWeight v hN hε hd r z) = 1 :=
  weight_sum _ (attempt v hN hε hd).leafWeight_sum r

/-- Soundness of every actual returned signing, with the original labels. -/
theorem output_sound (v : Fin N → Fin d → ℂ) (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ) (z : Draws v hN hε hd r)
    (σ : Fin N → ℝ) (hout : output v hN hε hd r z = some σ) :
    (∀i, IsSign (σ i)) ∧
      ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤ 9*(16*Real.sqrt 2+5)*Real.sqrt ε := by
  apply firstAccepted_sound _ _
    (fun σ => (∀i, IsSign (σ i)) ∧
      ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤ 9*(16*Real.sqrt 2+5)*Real.sqrt ε) _ r z σ hout
  intro l hl
  exact ⟨(KSFullManuscriptAcceptance.accepts_sound _ _ hl).1,
    (KSFullManuscriptAcceptance.accepts_norm_lt_nine _ _ hl).le⟩

/-- Legality of every trajectory, independently of acceptance. -/
theorem attempt_leaf_mem_cube (v : Fin N → Fin d → ℂ) (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (l : (attempt v hN hε hd).Leaves) :
    ((attempt v hN hε hd).leafState l).coeff ∈ ksCube 1 :=
  ((attempt v hN hε hd).leafState l).cube

private theorem entropy_drift_budget (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) :
    driftCoefficient N δ * ((N : ℝ)*(2*Real.log 2)) ≤ δ := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hl : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have he : driftCoefficient N δ * ((N : ℝ)*(2*Real.log 2)) = δ*(2*Real.log 2)/25 := by
    unfold driftCoefficient
    field_simp
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hl hδ.le]

private theorem entropy_cutoff_budget (hN : 0 < N) {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 < M) :
    ((N : ℝ)*(2*Real.log 2)) /
      (movementStep N δ M ^ 2 * (cutoff N δ M : ℝ)) ≤ 1/8 := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have ht := movementStep_pos hN hδ hM
  have hT : (0 : ℝ) < cutoff N δ M := Nat.cast_pos.mpr (cutoff_pos hN hδ hM)
  have hl : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  apply (div_le_iff₀ (mul_pos (sq_pos_of_pos ht) hT)).mpr
  have hb := cutoff_bound hN hδ hM
  nlinarith [mul_le_mul_of_nonneg_left hl hn.le]


theorem attempt_acceptance_ge (v : Fin N → Fin d → ℂ) (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (hparseval : (∑i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀i, ‖KSRankOne.atom (v i)‖ ≤ ε) :
    (41 : ℝ)/56 ≤ KSFullManuscriptAcceptance.acceptanceProbability
      (controller v hN hε hd) (horizon v ε) (initialState (controller v hN hε hd)) := by
  have hδ := Real.sqrt_pos.mpr hε
  exact KSFullManuscriptAcceptance.acceptanceProbability_from_zero_ge
    (controller v hN hε hd) hparseval (debitTolerance_budget hN (Real.sqrt ε)).le
    hε hsize rfl rfl (by unfold driftCoefficient; positivity)
    (KSFullManuscriptDrift.localPotentialDrift v hN hδ (debitTolerance_pos hN hδ)
      (ksRegularizerScale_pos (n := Fin d) hε) hd)
    (entropy_drift_budget hN hδ) (horizon v ε) (cutoff_pos hN hδ (taylorBudget_pos v hN hε))
    (entropy_cutoff_budget hN hδ (taylorBudget_pos v hN hε))

/-- Probability is the literal `some` event of the actual first-accepted output. -/
def successProbability (v : Fin N → Fin d → ℂ) (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ) : ℝ :=
  ∑z : Draws v hN hε hd r, drawWeight v hN hε hd r z *
    (if (output v hN hε hd r z).isSome then 1 else 0)

theorem output_event_probability_ge (v : Fin N → Fin d → ℂ) (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (hparseval : (∑i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀i, ‖KSRankOne.atom (v i)‖ ≤ ε) (r : ℕ) :
    1-((15 : ℝ)/56)^r ≤ ∑z : Draws v hN hε hd r,
      drawWeight v hN hε hd r z * (if (output v hN hε hd r z).isSome then 1 else 0) :=
  KSDebitWalkRetry.FiniteRetry.successProbability_ge _
    (fun l => ((attempt v hN hε hd).leafWeight_pos l).le)
    (attempt v hN hε hd).leafWeight_sum _ _ (attempt_acceptance_ge v hN hε hd hparseval hsize) r

end MatrixSpencer.KSFullManuscriptAlgorithm
