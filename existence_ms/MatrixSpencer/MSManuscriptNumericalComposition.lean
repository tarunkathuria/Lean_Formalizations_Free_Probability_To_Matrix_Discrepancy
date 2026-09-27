import MatrixSpencer.MSManuscriptNumericalFullSigning
import MatrixSpencer.MSManuscriptRetryBudget
import MatrixSpencer.SigningExtraction

/-!
# Matrix signing extraction from the numerical adaptive composition

The numerical epoch provider remains an explicit input, to be filled by the
concrete run/moment/reindex assembly. This module defines the actual finite
output and proves original-label signs, the square-case norm bound, and its
weighted success probability from that provider. It has no analytic-report
fallback and does not assert an unconditional numerical endpoint yet.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalComposition
open PhaseRestriction MSManuscriptAdaptive MSManuscriptPhase MSManuscriptNumericalHalfPhase
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run
attribute [local irreducible] MSManuscriptNumericalFullSigning.output
set_option maxRecDepth 4000
set_option maxHeartbeats 1500000
variable {N D : ℕ} [NeZero D]
local instance : CStarAlgebra (Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ)) := inferInstance

abbrev Point (N : ℕ) := MSManuscriptPhase.Point (ι := Fin N) (signingEpsilon (Fin N))

lemma lifted_contractions (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) : ∀ i, ‖signedLift (A i)‖ ≤ 1 := by
  intro i
  rw [signedLift_norm (hA i), ← spectralNorm_eq_scopedMatrixNorm]
  exact hN i

/-- The visible remaining actual epoch integration interface. -/
abbrev Provider (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian) (r : ℕ) :=
  MSManuscriptNumericalFullSigning.EpochProvider 0 (fun i => signedLift (A i))
    (fun i => signedLift_isHermitian (hA i)) (signingEpsilon (Fin N)) (epochFailure r)

def pointSampler (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (r : ℕ) (provider : Provider A hA r) : Sampler (Option (Point N)) :=
  MSManuscriptNumericalFullSigning.output 0 (fun i => signedLift (A i)) (fun i => signedLift_isHermitian (hA i))
    (lifted_contractions A hA hN) (signingEpsilon (Fin N)) (epochFailure r) provider (by unfold epochFailure; positivity) ⟨0, signing_zero_regular⟩

theorem pointSampler_sound (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (hDN : D ≤ N) (r : ℕ) (provider : Provider A hA r)
    (z : (pointSampler A hA hN r provider).Draws) (y : Point N)
    (ho : (pointSampler A hA hN r provider).value z = some y) :
    (∀ i, IsSign (y.val i)) ∧ spectralNorm (signedSum A (WithLp.ofLp y.val)) ≤ 10651761*Real.sqrt (N:ℝ) := by
  have ht := MSManuscriptNumericalFullSigning.output_sound 0 (fun i => signedLift (A i))
    (fun i => signedLift_isHermitian (hA i)) (lifted_contractions A hA hN)
    (signingEpsilon (Fin N)) (epochFailure r) provider (by unfold epochFailure; positivity) ⟨0, signing_zero_regular⟩ z y ho
  have hd : Fintype.card (Fin D ⊕ Fin D) ≤ 2*Fintype.card (Fin N) := by simp; omega
  have hi := remainingPotential_zero_le_five (fun i => signedLift (A i))
    (fun i => signedLift_isHermitian (hA i)) (lifted_contractions A hA hN) hd
  have hc : (Fintype.card (Live (0:EuclideanSpace ℝ (Fin N))):ℝ) ≤ N := by
    have hc : Fintype.card (Live (0:EuclideanSpace ℝ (Fin N))) ≤ N := by
      simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin N => i ∉ frozenCoordinates (0:EuclideanSpace ℝ (Fin N)))
    exact_mod_cast hc
  have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hc)
    (show 0 ≤ 4*phaseCost by norm_num [phaseCost,epochCost,epochCalls])
  have hp : remainingPotential 0 (fun i => signedLift (A i))
      (fun i => signedLift_isHermitian (hA i)) y.val ≤ 10651761*Real.sqrt (N:ℝ) := by
    norm_num only [Fintype.card_fin] at hi
    have hh := ht.2
    norm_num only [phaseCost,epochCost,epochCalls] at hh hs
    linarith
  have hz : Fintype.card (Live y.val) = 0 := by
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun i => i.property ((mem_frozenCoordinates y.val i).mpr (ht.1 i))⟩
  exact ⟨ht.1, (SigningExtraction.spectralNorm_le_remainingPotential A hA y.val hz).trans hp⟩

def output (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (r : ℕ) (provider : Provider A hA r) : Sampler (Option (Fin N → ℝ)) :=
  (pointSampler A hA hN r provider).map (Option.map (fun y => WithLp.ofLp y.val))

theorem output_sound (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (hDN : D ≤ N) (r : ℕ) (provider : Provider A hA r)
    (z : (output A hA hN r provider).Draws) (σ : Fin N → ℝ) (ho : (output A hA hN r provider).value z = some σ) :
    IsFullSigning σ ∧ spectralNorm (signedSum A σ) ≤ 10651761*Real.sqrt (N:ℝ) := by
  exact Sampler.map_option_sound (pointSampler A hA hN r provider) (fun y => WithLp.ofLp y.val)
    (fun y => (∀ i, IsSign (y.val i)) ∧ spectralNorm (signedSum A (WithLp.ofLp y.val)) ≤ 10651761*Real.sqrt (N:ℝ))
    (fun σ => IsFullSigning σ ∧ spectralNorm (signedSum A σ) ≤ 10651761*Real.sqrt (N:ℝ))
    (pointSampler_sound A hA hN hDN r provider) (fun _ h => h) z σ ho

theorem output_event_probability (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (r : ℕ) (provider : Provider A hA r) :
    1-((N+1:ℕ):ℝ)*((epochCalls:ℝ)*epochFailure r) ≤ ∑ z, (output A hA hN r provider).weight z *
      (if ((output A hA hN r provider).value z).isSome then 1 else 0) := by
  have ht := MSManuscriptNumericalFullSigning.output_event_probability 0 (fun i => signedLift (A i))
    (fun i => signedLift_isHermitian (hA i)) (lifted_contractions A hA hN)
    (signingEpsilon (Fin N)) (epochFailure r) provider (by unfold epochFailure; positivity) ⟨0, signing_zero_regular⟩
  have hf := Sampler.failure_map (pointSampler A hA hN r provider) (fun y => WithLp.ofLp y.val)
  have h1 := success_add_failure (pointSampler A hA hN r provider)
  have h2 := success_add_failure (output A hA hN r provider)
  change 1-((N+1:ℕ):ℝ)*((epochCalls:ℝ)*epochFailure r) ≤ (output A hA hN r provider).expectation success
  change 1-((Fintype.card (Fin N)+1:ℕ):ℝ)*((epochCalls:ℝ)*epochFailure r) ≤ (pointSampler A hA hN r provider).expectation success at ht
  simp only [Fintype.card_fin] at ht
  change (output A hA hN r provider).expectation MSManuscriptAdaptive.failure = _ at hf
  linarith

theorem constant_success (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1)
    (provider : Provider A hA (MSManuscriptRetryBudget.retries N epochCalls)) :
    (1:ℝ)/2 ≤ ∑ z, (output A hA hN (MSManuscriptRetryBudget.retries N epochCalls) provider).weight z *
      (if ((output A hA hN (MSManuscriptRetryBudget.retries N epochCalls) provider).value z).isSome then 1 else 0) := by
  have hp := output_event_probability A hA hN (MSManuscriptRetryBudget.retries N epochCalls) provider
  have hb := MSManuscriptRetryBudget.failure_budget N epochCalls
  have hpow : epochFailure (MSManuscriptRetryBudget.retries N epochCalls) ≤
      ((1:ℝ)/2)^(MSManuscriptRetryBudget.retries N epochCalls) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hm := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ ((N+1:ℕ):ℝ)*(epochCalls:ℝ) from by positivity)
  nlinarith

end MatrixSpencer.MSManuscriptNumericalComposition
