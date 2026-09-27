import MatrixSpencer.MSManuscriptNumericalAlgorithm
import MatrixSpencer.MSConvexNumericalProvider
import MatrixSpencer.MSManuscriptNumericalComposition


open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexNumericalAlgorithm
variable [MSConvexOwnerValue.Oracle]
open MSManuscriptAdaptive MSManuscriptPhase MSManuscriptNumericalHalfPhase
variable {N D : ℕ} [NeZero D]
local instance : CStarAlgebra (Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ)) := inferInstance
set_option maxRecDepth 4000
set_option maxHeartbeats 1500000

def provider (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (r : ℕ) :
    MSManuscriptNumericalComposition.Provider A hA r :=
  MSConvexNumericalProvider.provider finSumFinEquiv.symm
    (by have := NeZero.pos D; omega) 0 (fun i => signedLift (A i))
    (fun i => signedLift_isHermitian (hA i))
    (MSManuscriptNumericalComposition.lifted_contractions A hA hN)
    (signingEpsilon (Fin N)) signingEpsilon_pos signingEpsilon_count_small r

def output (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (r : ℕ) : Sampler (Option (Fin N → ℝ)) :=
  MSManuscriptNumericalComposition.output A hA hN r (provider A hA hN r)

theorem output_sound (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (hDN : D ≤ N) (r : ℕ)
    (z : (output A hA hN r).Draws) (σ : Fin N → ℝ)
    (ho : (output A hA hN r).value z = some σ) :
    IsFullSigning σ ∧ spectralNorm (signedSum A σ) ≤ 10651761 * Real.sqrt (N : ℝ) :=
  MSManuscriptNumericalComposition.output_sound A hA hN hDN r (provider A hA hN r) z σ ho

theorem output_event_probability (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) (r : ℕ) :
    1 - ((N+1 : ℕ) : ℝ) * ((epochCalls : ℝ) * epochFailure r) ≤
      ∑ z, (output A hA hN r).weight z *
        (if ((output A hA hN r).value z).isSome then 1 else 0) :=
  MSManuscriptNumericalComposition.output_event_probability A hA hN r (provider A hA hN r)

theorem constant_success (A : Fin N → CMatrix D) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, spectralNorm (A i) ≤ 1) :
    (1 : ℝ)/2 ≤ ∑ z,
      (output A hA hN (MSManuscriptRetryBudget.retries N epochCalls)).weight z *
        (if ((output A hA hN (MSManuscriptRetryBudget.retries N epochCalls)).value z).isSome
          then 1 else 0) :=
  MSManuscriptNumericalComposition.constant_success A hA hN
    (provider A hA hN (MSManuscriptRetryBudget.retries N epochCalls))

end MatrixSpencer.MSConvexNumericalAlgorithm
