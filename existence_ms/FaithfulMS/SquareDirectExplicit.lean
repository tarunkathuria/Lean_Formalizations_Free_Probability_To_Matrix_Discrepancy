import MatrixSpencer.MSManuscriptNumericalExplicit
import FaithfulMS.SquareDirectAlgorithm
import MatrixSpencer.MSManuscriptReturnedEvent

/-! Original-input numerical Matrix Spencer output, including dimension zero.
The success event is also stated literally as returning full signs with the
required operator norm bound. Existence follows from that actual event. -/
open Matrix
open scoped BigOperators
noncomputable section
open MatrixSpencer
namespace FaithfulMS.SquareDirectExplicit
variable [SquareDirectOracle.Oracle]
open MSManuscriptAdaptive MSManuscriptNumericalHalfPhase
variable {N D : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4000
set_option maxHeartbeats 1500000

def output : {D : ℕ} → (A : Fin N → CMatrix D) → (∀ i, (A i).IsHermitian) →
    (∀ i, spectralNorm (A i) ≤ 1) → ℕ → Sampler (Option (Fin N → ℝ))
  | 0, _, _, _, _ => Sampler.pure (some (fun _ => 1))
  | d+1, A, hA, hN, r => SquareDirectAlgorithm.output A hA hN r

theorem output_sound (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (hDN : D ≤ N) (r : ℕ)
    (z : (output A hA hN r).Draws) (σ : Fin N → ℝ)
    (ho : (output A hA hN r).value z = some σ) :
    IsFullSigning σ ∧ spectralNorm (signedSum A σ) ≤ 10651761 * Real.sqrt (N : ℝ) := by
  cases D with
  | zero =>
    have he : (fun _ : Fin N => (1 : ℝ)) = σ := Option.some.inj ho
    subst σ
    exact ⟨isFullSigning_one N, by rw [spectralNorm_zeroDimension]; positivity⟩
  | succ d => exact SquareDirectAlgorithm.output_sound A hA hN hDN r z σ ho

theorem output_event_probability (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (r : ℕ) :
    1 - ((N+1 : ℕ) : ℝ) * ((epochCalls : ℝ) * epochFailure r) ≤
      ∑ z, (output A hA hN r).weight z *
        (if ((output A hA hN r).value z).isSome then 1 else 0) := by
  cases D with
  | zero => simp only [output, Sampler.pure]; simp; unfold epochFailure; positivity
  | succ d => exact SquareDirectAlgorithm.output_event_probability A hA hN r

theorem constant_success (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) :
    (1 : ℝ)/2 ≤ ∑ z,
      (output A hA hN (MSManuscriptRetryBudget.retries N epochCalls)).weight z *
        (if ((output A hA hN (MSManuscriptRetryBudget.retries N epochCalls)).value z).isSome
          then 1 else 0) := by
  cases D with
  | zero =>
    change (1 : ℝ)/2 ≤ ∑ _z : PUnit, (1 : ℝ) * 1
    norm_num
  | succ d => exact SquareDirectAlgorithm.constant_success A hA hN

theorem valid_output_probability (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (hDN : D ≤ N) :
    let P := output A hA hN (MSManuscriptRetryBudget.retries N epochCalls)
    (1 : ℝ)/2 ≤ ∑ z, P.weight z *
      (if ∃ σ, P.value z = some σ ∧ IsFullSigning σ ∧
        spectralNorm (signedSum A σ) ≤ 10651761 * Real.sqrt (N : ℝ) then 1 else 0) := by
  dsimp only
  have he := Sampler.valid_event_eq
    (output A hA hN (MSManuscriptRetryBudget.retries N epochCalls))
    (fun σ => IsFullSigning σ ∧ spectralNorm (signedSum A σ) ≤ 10651761 * Real.sqrt (N : ℝ))
    (output_sound A hA hN hDN (MSManuscriptRetryBudget.retries N epochCalls))
  convert (constant_success A hA hN).trans_eq he.symm using 1
  congr 1
  funext z
  split_ifs <;> rfl

theorem exists_full_signing (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (hDN : D ≤ N) :
    ∃ σ : Fin N → ℝ, IsFullSigning σ ∧
      spectralNorm (signedSum A σ) ≤ 10651761 * Real.sqrt (N : ℝ) := by
  have hp := constant_success A hA hN
  obtain ⟨z, σ, ho⟩ := Sampler.exists_return_of_positive_event
    (output A hA hN (MSManuscriptRetryBudget.retries N epochCalls)) (lt_of_lt_of_le (by norm_num) hp)
  exact ⟨σ, output_sound A hA hN hDN _ z σ ho⟩

theorem matrix_spencer : squareStatementWithConstant 10651761 := by
  intro N D hDN A hA hN
  exact exists_full_signing A hA hN hDN

end FaithfulMS.SquareDirectExplicit
