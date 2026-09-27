import MatrixSpencer.DyadicManuscriptFullSigning
import MatrixSpencer.MSManuscriptRetryBudget
import MatrixSpencer.DyadicGlobalEpochInputs
import MatrixSpencer.RectangularTunedParameters
import MatrixSpencer.RectangularStatement


open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.DyadicManuscriptAnalyticAlgorithm
open PhaseRestriction MSManuscriptAdaptive MSManuscriptPhase
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run
attribute [local irreducible] DyadicManuscriptFullSigning.output
set_option maxRecDepth 4000
set_option maxHeartbeats 1500000
variable {N D : ℕ} [NeZero D]
local instance : CStarAlgebra (Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ)) := inferInstance

abbrev Point (N : ℕ) := MSManuscriptPhase.Point (ι := Fin N) (signingEpsilon (Fin N))
abbrev depth (N D : ℕ) := RectangularTunedParameters.depth N D
abbrev weight (N D : ℕ) := RectangularTunedParameters.weight N D
abbrev coefficient (N D : ℕ) := RectangularTunedParameters.coefficient N D

def epochInputs : DyadicPhasePotential.HasEpochInputs (Fin D ⊕ Fin D)
    (depth N D) (weight N D) (coefficient N D) (Fintype.card (Fin N)) := by
  simpa only [Fintype.card_fin] using
    hasEpochInputs_globalCoefficient (Fin D ⊕ Fin D) (depth N D) (weight N D) N

lemma lifted_contractions (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) : ∀ i, ‖signedLift (A i)‖ ≤ 1 := by
  intro i
  rw [signedLift_norm (hA i), ← spectralNorm_eq_scopedMatrixNorm]
  exact hN i

variable (hNpos : 0 < N) (hND : N ≤ D)

def pointSampler (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (r : ℕ) : Sampler (Option (Point N)) :=
  DyadicManuscriptFullSigning.output (depth N D) (RectangularTunedParameters.depth_positive N D)
    (weight N D) (RectangularTunedParameters.weight_positive hNpos hND)
    (coefficient N D) (RectangularTunedParameters.coefficient_two_le hNpos hND)
    0 (fun i => signedLift (A i)) (fun i => signedLift_isHermitian (hA i)) (lifted_contractions A hA hN)
    (signingEpsilon (Fin N)) signingEpsilon_pos signingEpsilon_count_small epochInputs
    (DyadicManuscriptFullSigning.analyticReports _ _ _ _ _ _ _ _ _ _ _ _ _ _) r ⟨0, signing_zero_regular⟩

theorem pointSampler_sound (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (r : ℕ)
    (z : (pointSampler hNpos hND A hA hN r).Draws) (y : Point N)
    (ho : (pointSampler hNpos hND A hA hN r).value z = some y) :
    (∀ i, IsSign (y.val i)) ∧ spectralNorm (signedSum A (WithLp.ofLp y.val)) ≤
      6796548*Real.sqrt ((N:ℝ)*rectangularLog N D) := by
  have ht := DyadicManuscriptFullSigning.output_sound (depth N D) (RectangularTunedParameters.depth_positive N D)
    (weight N D) (RectangularTunedParameters.weight_positive hNpos hND)
    (coefficient N D) (RectangularTunedParameters.coefficient_two_le hNpos hND)
    0 (fun i => signedLift (A i)) (fun i => signedLift_isHermitian (hA i)) (lifted_contractions A hA hN)
    (signingEpsilon (Fin N)) signingEpsilon_pos signingEpsilon_count_small epochInputs
    (DyadicManuscriptFullSigning.analyticReports _ _ _ _ _ _ _ _ _ _ _ _ _ _) r ⟨0, signing_zero_regular⟩ z y ho
  have hi := lifted_rectangularRemainingPotential_zero_le (RectangularTunedParameters.depth_positive N D)
    (RectangularTunedParameters.weight_positive hNpos hND).le A hA hN
  have hc : (Fintype.card (Live (0:EuclideanSpace ℝ (Fin N))):ℝ) ≤ N := by
    have hc : Fintype.card (Live (0:EuclideanSpace ℝ (Fin N))) ≤ N := by
      simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin N => i ∉ frozenCoordinates (0:EuclideanSpace ℝ (Fin N)))
    exact_mod_cast hc
  have hB := RectangularTunedParameters.coefficient_two_le hNpos hND
  have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hc)
    (show 0 ≤ 4*DyadicHalfPhase.phaseCost (coefficient N D) by
      exact mul_nonneg (by norm_num) (DyadicHalfPhase.phaseCost_nonneg hB))
  have hp : rectangularRemainingPotential (depth N D) (weight N D) 0 (fun i => signedLift (A i))
      (fun i => signedLift_isHermitian (hA i)) y.val ≤
      2*Real.sqrt (N:ℝ)+(weight N D)*(2*(D:ℝ))^(1/(2^(depth N D):ℝ))/(1-1/(2^(depth N D):ℝ))+
        (304*23)*((coefficient N D)+1)*Real.sqrt (N:ℝ) := by
    have hh := ht.2
    dsimp only [DyadicHalfPhase.phaseCost] at hh hs
    linarith
  have hledger := RectangularTunedParameters.ledger_le hNpos hND (K := (304*23:ℝ)) (by norm_num)
  have hp' : rectangularRemainingPotential (depth N D) (weight N D) 0 (fun i => signedLift (A i))
      (fun i => signedLift_isHermitian (hA i)) y.val ≤ 6796548*Real.sqrt ((N:ℝ)*rectangularLog N D) := by
    apply hp.trans
    convert hledger using 1; norm_num [depth, weight, coefficient, RectangularTunedParameters.exponent, rectangularLog]
  have hz : Fintype.card (Live y.val) = 0 := by
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun i => i.property ((mem_frozenCoordinates y.val i).mpr (ht.1 i))⟩
  exact ⟨ht.1, (spectralNorm_le_rectangularRemainingPotential
    (RectangularTunedParameters.depth_positive N D) (RectangularTunedParameters.weight_positive hNpos hND).le A hA y.val hz).trans hp'⟩

def output (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (r : ℕ) : Sampler (Option (Fin N → ℝ)) :=
  (pointSampler hNpos hND A hA hN r).map (Option.map (fun y => WithLp.ofLp y.val))

theorem output_sound (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (r : ℕ)
    (z : (output hNpos hND A hA hN r).Draws) (σ : Fin N → ℝ) (ho : (output hNpos hND A hA hN r).value z = some σ) :
    IsFullSigning σ ∧ spectralNorm (signedSum A σ) ≤ 6796548*Real.sqrt ((N:ℝ)*rectangularLog N D) := by
  exact Sampler.map_option_sound (pointSampler hNpos hND A hA hN r) (fun y => WithLp.ofLp y.val)
    (fun y => (∀ i, IsSign (y.val i)) ∧ spectralNorm (signedSum A (WithLp.ofLp y.val)) ≤ 6796548*Real.sqrt ((N:ℝ)*rectangularLog N D))
    (fun σ => IsFullSigning σ ∧ spectralNorm (signedSum A σ) ≤ 6796548*Real.sqrt ((N:ℝ)*rectangularLog N D))
    (pointSampler_sound hNpos hND A hA hN r) (fun _ h => h) z σ ho

theorem output_event_probability (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (r : ℕ) :
    1-((N+1:ℕ):ℝ)*((RectangularEpochParameters.count (coefficient N D):ℝ)*((1:ℝ)/2)^r) ≤
      ∑ z, (output hNpos hND A hA hN r).weight z *
        (if ((output hNpos hND A hA hN r).value z).isSome then 1 else 0) := by
  have ht := DyadicManuscriptFullSigning.output_event_probability (depth N D) (RectangularTunedParameters.depth_positive N D)
    (weight N D) (RectangularTunedParameters.weight_positive hNpos hND)
    (coefficient N D) (RectangularTunedParameters.coefficient_two_le hNpos hND)
    0 (fun i => signedLift (A i)) (fun i => signedLift_isHermitian (hA i)) (lifted_contractions A hA hN)
    (signingEpsilon (Fin N)) signingEpsilon_pos signingEpsilon_count_small epochInputs
    (DyadicManuscriptFullSigning.analyticReports _ _ _ _ _ _ _ _ _ _ _ _ _ _) r ⟨0, signing_zero_regular⟩
  have hf := Sampler.failure_map (pointSampler hNpos hND A hA hN r) (fun y => WithLp.ofLp y.val)
  have h1 := success_add_failure (pointSampler hNpos hND A hA hN r)
  have h2 := success_add_failure (output hNpos hND A hA hN r)
  change 1-((N+1:ℕ):ℝ)*((RectangularEpochParameters.count (coefficient N D):ℝ)*((1:ℝ)/2)^r) ≤
    (output hNpos hND A hA hN r).expectation success
  change 1-((Fintype.card (Fin N)+1:ℕ):ℝ)*((RectangularEpochParameters.count (coefficient N D):ℝ)*((1:ℝ)/2)^r) ≤
    (pointSampler hNpos hND A hA hN r).expectation success at ht
  simp only [Fintype.card_fin] at ht
  change (output hNpos hND A hA hN r).expectation MSManuscriptAdaptive.failure = _ at hf
  linarith

theorem constant_success (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) :
    (1:ℝ)/2 ≤ ∑ z, (output hNpos hND A hA hN (MSManuscriptRetryBudget.retries N (RectangularEpochParameters.count (coefficient N D)))).weight z *
      (if ((output hNpos hND A hA hN (MSManuscriptRetryBudget.retries N (RectangularEpochParameters.count (coefficient N D)))).value z).isSome then 1 else 0) := by
  have hp := output_event_probability hNpos hND A hA hN
    (MSManuscriptRetryBudget.retries N (RectangularEpochParameters.count (coefficient N D)))
  have hb := MSManuscriptRetryBudget.failure_budget N (RectangularEpochParameters.count (coefficient N D))
  nlinarith

end MatrixSpencer.DyadicManuscriptAnalyticAlgorithm
