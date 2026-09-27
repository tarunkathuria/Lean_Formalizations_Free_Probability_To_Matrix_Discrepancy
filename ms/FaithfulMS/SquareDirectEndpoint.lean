import FaithfulMS.SquareDirectSampling
import FaithfulMS.SquareDirectPolynomial
import FaithfulMS.Confidence

/-! Original-input square Matrix Spencer with direct primal-density reports,
derived conditional-uniform code law, arbitrary confidence, and uniform
polynomial bounds on every execution. The only solver parameter is the
permitted exact polynomial affine-SDP service. -/
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.SquareDirectEndpoint
open MatrixSpencer MSCountedSampler SquareDirectRuntime
open SquareDirectPolynomial (confidenceRetries)
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run
variable {N D : ℕ}

def Good (A : Fin N→CMatrix D) (out : Option (Fin N→ℝ)) : Prop :=
  ∃σ, out=some σ ∧ IsFullSigning σ ∧
    spectralNorm (signedSum A σ)≤10651761*Real.sqrt (N:ℝ)

theorem success_probability (P : DirectSDP.PolynomialService)
    (A : Fin N→CMatrix D) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i)≤1) (k : ℕ) :
    1-(1/2:ℝ)^k ≤ ∑z,(sampler P A hA hN (confidenceRetries N k)).weight z *
      (if ((sampler P A hA hN (confidenceRetries N k)).value z).isSome then 1 else 0) := by
  have hf := Confidence.retry_failure ((N+1)*MSManuscriptNumericalHalfPhase.epochCalls) k
    (q:=301/800) (by norm_num) (by norm_num)
  have hp := @SquareDirectExplicit.output_event_probability ⟨P.service⟩ N D A hA hN
    (confidenceRetries N k)
  apply le_trans _ hp
  apply sub_le_sub_left _ 1
  simpa only [confidenceRetries,MSManuscriptNumericalHalfPhase.epochFailure,
    Nat.cast_mul,mul_assoc] using hf

theorem bounded_execution_probability (P : DirectSDP.PolynomialService)
    (A : Fin N→CMatrix D) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i)≤1) (hDN : D≤N) (k : ℕ) :
    let r := confidenceRetries N k
    let E := implementation P A hA hN r
    let code := SquareDirectSampling.Runtime.implementation P A hA hN r
    1-(1/2:ℝ)^k ≤ ∑z,code.mass z *
      (if ∃out cost draws, E.Executes z out cost draws ∧ cost≤operations P N D r ∧
        draws≤SquareDirectRuntime.draws N D r ∧ Good A out then 1 else 0) := by
  dsimp only
  rw [Refinement.bounded_event
    (SquareDirectSampling.Runtime.implementation P A hA hN (confidenceRetries N k))
    (implementation_bounded P A hA hN (confidenceRetries N k))]
  refine (success_probability P A hA hN k).trans (le_of_eq ?_)
  unfold MSManuscriptAdaptive.Sampler.expectation
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  cases hv : (sampler P A hA hN (confidenceRetries N k)).value z with
  | none => simp [Good]
  | some σ =>
    have hs := @SquareDirectExplicit.output_sound ⟨P.service⟩ N D A hA hN hDN
      (confidenceRetries N k) z σ hv
    simp only [Option.isSome_some,↓reduceIte]
    exact (if_pos ⟨σ,rfl,hs⟩).symm

/-- One work polynomial is chosen from the solver before the input dimensions
and confidence parameter. The success event and execution bounds refer to
exactly the same compiled direct-density implementation. -/
theorem polynomial_algorithm (P : DirectSDP.PolynomialService) :
    ∃C e : ℕ, 0<C ∧ ∀ (N D : ℕ) (A : Fin N→CMatrix D)
      (hA : ∀i,(A i).IsHermitian) (hN : ∀i,spectralNorm (A i)≤1) (hDN : D≤N) (k : ℕ),
      let r := confidenceRetries N k
      let E := implementation P A hA hN r
      let code := SquareDirectSampling.Runtime.implementation P A hA hN r
      (1-(1/2:ℝ)^k ≤ ∑z,code.mass z *
        (if ∃out cost draws, E.Executes z out cost draws ∧
          cost≤C*(N+D+k+2)^e ∧ draws≤C*(N+D+k+2)^e ∧ Good A out then 1 else 0)) ∧
      (∀z, ∃cost draws, E.Executes z ((sampler P A hA hN r).value z) cost draws ∧
        cost≤C*(N+D+k+2)^e ∧ draws≤C*(N+D+k+2)^e) := by
  obtain ⟨C,e,hC,hb⟩ := SquareDirectPolynomial.confidence_majorant P
  refine ⟨C,e,hC,?_⟩
  intro N D A hA hN hDN k
  dsimp only
  constructor
  · refine (bounded_execution_probability P A hA hN hDN k).trans ?_
    apply Finset.sum_le_sum
    intro z hz
    apply mul_le_mul_of_nonneg_left _
      ((SquareDirectSampling.Runtime.implementation P A hA hN (confidenceRetries N k)).mass_nonneg z)
    split_ifs with hg hh hh
    · exact le_rfl
    · obtain ⟨out,cost,draws,he,hc,hr,hgood⟩ := hg
      exact False.elim (hh ⟨out,cost,draws,he,hc.trans (hb N D k).1,hr.trans (hb N D k).2,hgood⟩)
    · norm_num
    · exact le_rfl
  · intro z
    obtain ⟨cost,draws,he,hc,hr⟩ := execution_bounded P A hA hN (confidenceRetries N k) z
    exact ⟨cost,draws,he,hc.trans (hb N D k).1,hr.trans (hb N D k).2⟩

#print axioms polynomial_algorithm
end FaithfulMS.SquareDirectEndpoint
