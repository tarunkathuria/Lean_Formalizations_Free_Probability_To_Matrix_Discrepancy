import MatrixSpencer.KSJointInputAlgorithm
import MatrixSpencer.KSInputJointBounds

/-!
# Input-only finite Kadison–Singer signing algorithm

All controller and Taylor parameters are explicit expressions in the original
vector entries and error bound. The actual joint derivative certificate is
proved internally. The finite output event has success probability at least
`1-(15/56)^r`; every output signs every original label and obeys the stated
operator-norm discrepancy bound. The zero-error and zero-dimensional
existence cases are handled separately. No operation-cost theorem is claimed.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
namespace MatrixSpencer.KSExplicitWalkAlgorithm
variable {N d : ℕ}

/-- Explicit input-entry cap; no derivative bound is supplied to the algorithm. -/
def jointCap (v : Fin N → Fin d → ℂ) (ε : ℝ) : ℝ :=
  KSJointBoundParameters.jointCap v (Real.sqrt ε) (KSDebitInputAlgorithm.debitTolerance N ε)
    (ksRegularizerScale ε (Fin d))

theorem jointCap_pos (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) :
    0 < jointCap v ε := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact KSJointBoundParameters.jointCap_pos v (Real.sqrt_pos.mpr hε)
    (KSDebitInputAlgorithm.debitTolerance_pos N hε).le (ksRegularizerScale_pos (n := Fin d) hε)

def taylorBudget (v : Fin N → Fin d → ℂ) (ε : ℝ) : ℝ :=
  KSJointInputAlgorithm.taylorBudget N d ε (jointCap v ε)

theorem taylorBudget_pos (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) :
    0 < taylorBudget v ε := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact KSJointInputAlgorithm.taylorBudget_pos N hε (jointCap_pos v hε hd).le

abbrev Draws (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ) :=
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  KSDebitInputAlgorithm.Draws v hε (taylorBudget_pos v hε hd).le hd r

/-- The actual finite attempt-and-retry output with all numerical budgets fixed by the input. -/
def output (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ)
    (z : Draws v hε hd r) : Option (Fin N → ℝ) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact KSDebitInputAlgorithm.output v hε (taylorBudget_pos v hε hd).le hd r z

/-- The weight of an actual finite sequence of independent finite walk draws. -/
def drawWeight (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ)
    (z : Draws v hε hd r) : ℝ := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let C := KSDebitInputAlgorithm.controller v hε (taylorBudget_pos v hε hd).le hd
  exact KSDebitWalkRetry.FiniteRetry.weight
    (KSDebitWalkRun.run C (KSDebitInputAlgorithm.cutoff N ε (taylorBudget v ε))
      (KSDebitWalkRun.initialState C)).leafWeight r z

theorem drawWeight_nonneg (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε)
    (hd : 0 < d) (r : ℕ) (z : Draws v hε hd r) : 0 ≤ drawWeight v hε hd r z := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let C := KSDebitInputAlgorithm.controller v hε (taylorBudget_pos v hε hd).le hd
  let T := KSDebitWalkRun.run C (KSDebitInputAlgorithm.cutoff N ε (taylorBudget v ε))
    (KSDebitWalkRun.initialState C)
  exact KSDebitWalkRetry.FiniteRetry.weight_nonneg T.leafWeight
    (fun l => (T.leafWeight_pos l).le) r z

theorem drawWeight_sum (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε)
    (hd : 0 < d) (r : ℕ) : (∑ z : Draws v hε hd r, drawWeight v hε hd r z) = 1 := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let C := KSDebitInputAlgorithm.controller v hε (taylorBudget_pos v hε hd).le hd
  let T := KSDebitWalkRun.run C (KSDebitInputAlgorithm.cutoff N ε (taylorBudget v ε))
    (KSDebitWalkRun.initialState C)
  exact KSDebitWalkRetry.FiniteRetry.weight_sum T.leafWeight T.leafWeight_sum r

/-- Probability of the literal returned-`some` event. -/
def successProbability (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ) : ℝ :=
  ∑ z : Draws v hε hd r, drawWeight v hε hd r z * (if (output v hε hd r z).isSome then 1 else 0)

private theorem successProbability_eq (v : Fin N → Fin d → ℂ) {ε : ℝ}
    (hε : 0 < ε) (hd : 0 < d) (r : ℕ) :
    successProbability v hε hd r =
      letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      KSDebitInputAlgorithm.successProbability v hε (taylorBudget_pos v hε hd).le hd r := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact (KSDebitInputAlgorithm.successProbability_eq_output_event v hε
    (taylorBudget_pos v hε hd).le hd r).symm

/-- Every reported result is a full signing of every original label. -/
theorem output_sound (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (r : ℕ) (z : Draws v hε hd r) (σ : Fin N → ℝ) (hout : output v hε hd r z = some σ) :
    (∀ i, IsSign (σ i)) ∧
      ‖∑ i, σ i • KSRankOne.atom (v i)‖ ≤ 9*(16*Real.sqrt 2+5)*Real.sqrt ε := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact KSDebitInputAlgorithm.output_sound v hε (taylorBudget_pos v hε hd).le hd r z σ hout

/-- Input-only success bound: the actual joint derivative certificate is proved internally. -/
theorem successProbability_ge (v : Fin N → Fin d → ℂ) {ε : ℝ}
    (hε : 0 < ε) (hd : 0 < d) (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖^2 ≤ ε) (r : ℕ) :
    1-((15:ℝ)/56)^r ≤ successProbability v hε hd r := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [successProbability_eq]
  exact KSJointInputAlgorithm.successProbability_ge v hε (jointCap_pos v hε hd).le hd
    hparseval hsize (KSInputJointBounds.jointBounds v (Real.sqrt_pos.mpr hε)
      (KSDebitInputAlgorithm.debitTolerance_pos N hε).le
      (ksRegularizerScale_pos (n := Fin d) hε) hd) r

/-- The probability bound spelled out as the actual finite output event. -/
theorem output_event_probability_ge (v : Fin N → Fin d → ℂ) {ε : ℝ}
    (hε : 0 < ε) (hd : 0 < d) (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖^2 ≤ ε) (r : ℕ) :
    1-((15:ℝ)/56)^r ≤ ∑ z : Draws v hε hd r,
      drawWeight v hε hd r z * (if (output v hε hd r z).isSome then 1 else 0) :=
  successProbability_ge v hε hd hparseval hsize r

theorem one_attempt_success (v : Fin N → Fin d → ℂ) {ε : ℝ}
    (hε : 0 < ε) (hd : 0 < d) (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖^2 ≤ ε) :
    (41:ℝ)/56 ≤ successProbability v hε hd 1 := by
  have hh := successProbability_ge v hε hd hparseval hsize 1
  norm_num at hh ⊢
  exact hh

/-- Positive finite success probability gives an actual successful finite draw. -/
theorem exists_output (v : Fin N → Fin d → ℂ) {ε : ℝ}
    (hε : 0 < ε) (hd : 0 < d) (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖^2 ≤ ε) :
    ∃ (z : Draws v hε hd 1) (σ : Fin N → ℝ), output v hε hd 1 z = some σ := by
  classical
  have hp := one_attempt_success v hε hd hparseval hsize
  by_contra! hn
  have ho : ∀ z : Draws v hε hd 1, output v hε hd 1 z = none := by
    intro z
    cases he : output v hε hd 1 z with
    | none => rfl
    | some σ => exact False.elim (hn z σ he)
  simp [successProbability, ho] at hp
  norm_num at hp

/-- Total normalized existence from the finite walk, with the zero-error and
zero-dimensional cases discharged by the constant full signing. -/
theorem exists_full_signing (v : Fin N → Fin d → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖^2 ≤ ε) :
    ∃ σ : Fin N → ℝ, (∀ i, IsSign (σ i)) ∧
      ‖∑ i, σ i • KSRankOne.atom (v i)‖ ≤ 9*(16*Real.sqrt 2+5)*Real.sqrt ε := by
  classical
  rcases eq_or_lt_of_le hε with he | he
  · have hz : ∀ i, v i = 0 := by
      intro i
      have hn := hsize i
      have hn0 := norm_nonneg (WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))
      have hnz : ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖ = 0 := by nlinarith
      exact WithLp.toLp_injective 2 (norm_eq_zero.mp hnz)
    refine ⟨fun _ => 1, fun _ => by simp [IsSign], ?_⟩
    simp [hz, ← he]
  · by_cases hd : d = 0
    · subst d
      have hz : ∀ i, KSRankOne.atom (v i) = 0 := fun _ => Subsingleton.elim _ _
      refine ⟨fun _ => 1, fun _ => by simp [IsSign], ?_⟩
      simp only [hz, smul_zero, Finset.sum_const_zero, norm_zero]
      positivity
    · obtain ⟨z, σ, ho⟩ := exists_output v he (Nat.pos_of_ne_zero hd) hparseval hsize
      exact ⟨σ, output_sound v he (Nat.pos_of_ne_zero hd) 1 z σ ho⟩

end MatrixSpencer.KSExplicitWalkAlgorithm
