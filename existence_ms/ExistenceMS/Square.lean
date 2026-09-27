import ExistenceMS.RealInput
import MatrixSpencer.MSManuscriptNumericalExplicit

/-! Existence extracted from positive success mass of the actual revised
projection walk. The final statement contains only real matrix input. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace ExistenceMS
open MatrixSpencer

theorem exists_square : Frozen.squareStatement 100000000 := by
  intro N d hDN A hA hAn
  apply RealInput.signing_bound_of_complex A _
  let B : Fin N → CMatrix d := fun i => realMatrixEmbedding (A i)
  have hB : ∀ i, (B i).IsHermitian :=
    fun i => RealInput.embedding_hermitian_of_symmetric (A i) (hA i)
  have hBn : ∀ i, MatrixSpencer.spectralNorm (B i) ≤ 1 := by
    intro i
    simpa only [B,MatrixSpencer.spectralNorm,RealInput.realMatrixEmbedding_norm] using hAn i
  let r := MSManuscriptRetryBudget.retries N MSManuscriptNumericalHalfPhase.epochCalls
  let P := MSManuscriptNumericalExplicit.output B hB hBn r
  have hsuccess : (1 : ℝ)/2 ≤ ∑ z, P.weight z *
      (if (P.value z).isSome then 1 else 0) :=
    MSManuscriptNumericalExplicit.constant_success B hB hBn
  obtain ⟨z,s,ho⟩ := MSManuscriptAdaptive.Sampler.exists_return_of_positive_event P
    (lt_of_lt_of_le (by norm_num) hsuccess)
  have h := MSManuscriptNumericalExplicit.output_sound B hB hBn hDN r z s ho
  refine ⟨s,h.1,h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by norm_num : (10651761 : ℝ) ≤ 100000000)
    (Real.sqrt_nonneg (N : ℝ))

end ExistenceMS
