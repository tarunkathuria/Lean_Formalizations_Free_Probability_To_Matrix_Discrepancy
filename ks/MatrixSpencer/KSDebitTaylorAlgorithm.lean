import MatrixSpencer.KSDebitInputAlgorithm
import MatrixSpencer.KSDebitNumericalDrift

/-!
# Success of the finite numerical signing algorithm from actual Taylor bounds

Input scaling supplies the regularizer, debit, step, tolerance, and cutoff.
The theorem here requires only the isolated actual fourth-derivative
certificate in addition to the Parseval and atom-size input conditions.
The local potential drift is proved from that certificate, rather than
assumed. Every returned value is a full original-label signing and has the
stated spectral discrepancy by the existing numerical acceptance proof.

This remains a certificate-conditional algorithm theorem: an adequate `M`
and its input-derived actual Taylor bounds are not constructed in this file.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSDebitTaylorAlgorithm

variable {N d : ℕ} [Nonempty (Fin d)]
open KSDebitInputAlgorithm

/-- Only actual query-line and movement-line smoothness/fourth derivatives
remain in the certificate after the input scaling is fixed. -/
abbrev TaylorBounds (v : Fin N → Fin d → ℂ) (ε M : ℝ) (hd : 0 < d) : Prop :=
  KSDebitNumericalDrift.RemainingTaylorBounds v (Real.sqrt ε)
    (debitTolerance N ε) (ksRegularizerScale ε (Fin d)) M hd

/-- Each independent finite attempt starts from the actual preparation of
zero, and the output is the first signing accepted by the numerical test. -/
theorem successProbability_ge (v : Fin N → Fin d → ℂ) {ε M : ℝ}
    (hε : 0 < ε) (hM : 0 ≤ M) (hd : 0 < d)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsmall : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε)
    (hTaylor : TaylorBounds v ε M hd) (r : ℕ) :
    1 - ((15 : ℝ) / 56) ^ r ≤ successProbability v hε hM hd r := by
  apply successProbability_of_localDrift v hε hM hd hparseval hsmall _ r
  exact KSDebitNumericalDrift.localPotentialDrift v (Real.sqrt_pos.mpr hε)
    (debitTolerance_pos N hε) (ksRegularizerScale_pos (n := Fin d) hε) hM hd hTaylor

theorem one_attempt_success (v : Fin N → Fin d → ℂ) {ε M : ℝ}
    (hε : 0 < ε) (hM : 0 ≤ M) (hd : 0 < d)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsmall : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε)
    (hTaylor : TaylorBounds v ε M hd) :
    (41 : ℝ) / 56 ≤ successProbability v hε hM hd 1 := by
  have hh := successProbability_ge v hε hM hd hparseval hsmall hTaylor 1
  norm_num only [pow_one] at hh
  linarith

/-- The probability bound as the literal finite weighted event that the
implemented signing-valued output is `some`, not an abstract success oracle. -/
theorem output_event_probability_ge (v : Fin N → Fin d → ℂ) {ε M : ℝ}
    (hε : 0 < ε) (hM : 0 ≤ M) (hd : 0 < d)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsmall : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε)
    (hTaylor : TaylorBounds v ε M hd) (r : ℕ) :
    1 - ((15 : ℝ) / 56) ^ r ≤ ∑ z : Draws v hε hM hd r,
      KSDebitWalkRetry.FiniteRetry.weight
        (KSDebitWalkRun.run (controller v hε hM hd) (cutoff N ε M)
          (KSDebitWalkRun.initialState (controller v hε hM hd))).leafWeight r z *
        (if (output v hε hM hd r z).isSome then 1 else 0) := by
  rw [← successProbability_eq_output_event]
  exact successProbability_ge v hε hM hd hparseval hsmall hTaylor r

/-- Soundness and the explicit probability bound for this same actual
algorithm. Soundness holds even for inputs `M` without Taylor certificates;
the certificate is used only to bound the chance of returning a signing. -/
theorem algorithm_guarantee (v : Fin N → Fin d → ℂ) {ε M : ℝ}
    (hε : 0 < ε) (hM : 0 ≤ M) (hd : 0 < d)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsmall : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε)
    (hTaylor : TaylorBounds v ε M hd) :
    (∀ (r : ℕ) (z : Draws v hε hM hd r) (σ : Fin N → ℝ),
      output v hε hM hd r z = some σ →
      (∀ i, IsSign (σ i)) ∧
        ‖∑ i, σ i • KSRankOne.atom (v i)‖ ≤ 9 * (16 * Real.sqrt 2 + 5) * Real.sqrt ε) ∧
    ∀ r : ℕ, 1 - ((15 : ℝ) / 56) ^ r ≤ successProbability v hε hM hd r := by
  constructor
  · intro r z σ hout
    exact output_sound v hε hM hd r z σ hout
  · exact successProbability_ge v hε hM hd hparseval hsmall hTaylor

end MatrixSpencer.KSDebitTaylorAlgorithm
