import MatrixSpencer.KSDebitNumericalController
import MatrixSpencer.KSDebitWalkRetry

/-!
# Input-scaled finite signing algorithm and unconditional output soundness

The regularizer, debit, movement step, cutoff and numerical acceptance
thresholds are fixed by explicit formulas. The scalar fourth-derivative
budget `M` still needs its input-derived certificate for a success lower
bound. Independently of that missing certificate, every returned signing is
proved valid by the actual numerical acceptance test.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSDebitInputAlgorithm

variable {N d : ℕ} [Nonempty (Fin d)]

def debitTolerance (N : ℕ) (ε : ℝ) : ℝ := Real.sqrt ε / ((N : ℝ) + 1)

theorem debitTolerance_pos (N : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < debitTolerance N ε := by
  unfold debitTolerance
  positivity

theorem debitTolerance_budget (N : ℕ) (ε : ℝ) :
    (N : ℝ) * debitTolerance N ε ≤ Real.sqrt ε := by
  have hden : 0 < (N : ℝ) + 1 := by positivity
  unfold debitTolerance
  rw [← mul_div_assoc, div_le_iff₀ hden]
  nlinarith [Real.sqrt_nonneg ε]

def controller (v : Fin N → Fin d → ℂ) {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) (hd : 0 < d) :
    KSDebitWalkRun.Controller N (Fin d) :=
  KSDebitNumericalController.controller v (Real.sqrt_pos.mpr hε)
    (debitTolerance_pos N hε) (ksRegularizerScale_pos (n := Fin d) hε) hM hd

def cutoff (N : ℕ) (ε M : ℝ) : ℕ := KSControllerParameters.cutoff N (Real.sqrt ε) M
def normTolerance (ε : ℝ) : ℝ := 2 * (16 * Real.sqrt 2 + 5) * Real.sqrt ε
def threshold (ε : ℝ) : ℝ := 9 * (16 * Real.sqrt 2 + 5) * Real.sqrt ε

abbrev Draws (v : Fin N → Fin d → ℂ) {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (hd : 0 < d) (r : ℕ) :=
  KSDebitWalkRetry.Draws (controller v hε hM hd) (cutoff N ε M) r

/-- The actual output is either a coefficient signing or an explicit failure. -/
def output (v : Fin N → Fin d → ℂ) {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (hd : 0 < d) (r : ℕ) (z : Draws v hε hM hd r) : Option (Fin N → ℝ) :=
  (KSDebitWalkRetry.retry (controller v hε hM hd) (cutoff N ε M)
    (normTolerance ε) (threshold ε) r z).map (fun s => s.coeff)

def successProbability (v : Fin N → Fin d → ℂ) {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (hd : 0 < d) (r : ℕ) : ℝ :=
  KSDebitWalkRetry.successProbability (controller v hε hM hd) (cutoff N ε M)
    (normTolerance ε) (threshold ε) r

/-- The success event is literally that this signing-valued algorithm
returns `some`, under its actual finite independent draw weights. -/
theorem successProbability_eq_output_event (v : Fin N → Fin d → ℂ) {ε M : ℝ}
    (hε : 0 < ε) (hM : 0 ≤ M) (hd : 0 < d) (r : ℕ) :
    successProbability v hε hM hd r = ∑ z : Draws v hε hM hd r,
      KSDebitWalkRetry.FiniteRetry.weight
        (KSDebitWalkRun.run (controller v hε hM hd) (cutoff N ε M)
          (KSDebitWalkRun.initialState (controller v hε hM hd))).leafWeight r z *
        (if (output v hε hM hd r z).isSome then 1 else 0) := by
  unfold successProbability
  rw [KSDebitWalkRetry.successProbability_eq_draw_sum]
  apply Finset.sum_congr rfl
  intro z _
  simp only [output, Option.isSome_map]

/-- Every output passes both the exact original-label sign condition and
the actual spectral discrepancy bound. This theorem alone gives no lower
bound on how often a signing is returned. -/
theorem output_sound (v : Fin N → Fin d → ℂ) {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (hd : 0 < d) (r : ℕ) (z : Draws v hε hM hd r) (σ : Fin N → ℝ)
    (hout : output v hε hM hd r z = some σ) :
    (∀ i, IsSign (σ i)) ∧ ‖∑ i, σ i • KSRankOne.atom (v i)‖ ≤ threshold ε := by
  have hν : 0 < normTolerance ε := by unfold normTolerance; positivity
  obtain ⟨s, hs, hcoeff⟩ := Option.map_eq_some_iff.mp hout
  have h := KSDebitWalkRetry.retry_sound (controller v hε hM hd) (cutoff N ε M) hν r z s hs
  subst σ
  exact h

/-- Input scaling discharges the initial drift and timeout scalar budgets;
the actual local drift is the only remaining premise of this intermediate
probability composition. The final theorem must discharge it too. -/
theorem successProbability_of_localDrift (v : Fin N → Fin d → ℂ) {ε M : ℝ}
    (hε : 0 < ε) (hM : 0 ≤ M) (hd : 0 < d)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsmall : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε)
    (hdrift : KSDebitWalkQuality.LocalPotentialDrift (controller v hε hM hd)
      (KSControllerParameters.driftCoefficient N (Real.sqrt ε))) (r : ℕ) :
    1 - ((15 : ℝ) / 56) ^ r ≤ successProbability v hε hM hd r := by
  have hδ := Real.sqrt_pos.mpr hε
  apply KSDebitWalkRetry.successProbability_from_zero_ge (controller v hε hM hd)
    hparseval (debitTolerance_budget N ε) hε hsmall rfl rfl
    (KSControllerParameters.driftCoefficient_nonneg N hδ) hdrift
    (by simpa only [mul_assoc, mul_left_comm, mul_comm] using
      KSControllerParameters.entropy_drift_budget N hδ)
    (cutoff N ε M) (KSControllerParameters.cutoff_pos N (Real.sqrt ε) M)
    (by
      change (N : ℝ) * (2 * Real.log 2) /
        (KSControllerParameters.movementStep N (Real.sqrt ε) M ^ 2 *
          (KSControllerParameters.cutoff N (Real.sqrt ε) M : ℝ)) ≤ 1 / 8
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        KSControllerParameters.entropy_cutoff_budget N hδ hM) r

end MatrixSpencer.KSDebitInputAlgorithm
