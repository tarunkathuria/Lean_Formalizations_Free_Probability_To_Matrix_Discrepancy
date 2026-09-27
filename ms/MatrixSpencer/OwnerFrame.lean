import MatrixSpencer.CoefficientResponse
import MatrixSpencer.CompressedGram

/-!
# Concrete owner data on the actual physical source support

The owner density is the original global maximizer. Only its source-support
compression enters the auxiliary unconstrained response estimate.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]

local instance ownerFrameCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ownerFrameNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def observedOwnerDensity (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) : Matrix n n ℂ :=
  hermitianDensityOptimizer (H : Matrix n n ℂ) (covarianceKraus A C) θ

def observedSourceDensity (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) :=
  krausCompressedDensity (covarianceKraus A C) (observedOwnerDensity H A C θ)

def observedSourceTransport (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) :=
  transportOptimizer (observedSourceDensity H A C θ)
    (krausChannel (krausReducedFamily (covarianceKraus A C)) (observedSourceDensity H A C θ))

def observedOwnedTransport (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) : Matrix n n ℂ :=
  krausSupportEmbedding (covarianceKraus A C) * observedSourceTransport H A C θ *
    (krausSupportEmbedding (covarianceKraus A C))ᴴ

def observedOwnedGram (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) : Matrix ι ι ℝ :=
  covarianceGram A (observedOwnerDensity H A C θ) (observedOwnedTransport H A C θ)

theorem observedOwnerDensity_posDef (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) {θ : ℝ} (hθ : 0 < θ) : (observedOwnerDensity H A C θ).PosDef :=
  hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) (covarianceKraus A C) hθ

theorem observedOwnerDensity_trace (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) : realTrace (observedOwnerDensity H A C θ) = 1 :=
  hermitianDensityOptimizer_trace (H : Matrix n n ℂ) (covarianceKraus A C) θ

theorem observedSourceDensity_posDef (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) {θ : ℝ} (hθ : 0 < θ) : (observedSourceDensity H A C θ).PosDef :=
  krausCompressedDensity_posDef (covarianceKraus A C) (observedOwnerDensity_posDef H A C hθ)

theorem observedSourceSource_posDef (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) {θ : ℝ} (hθ : 0 < θ) :
    (krausChannel (krausReducedFamily (covarianceKraus A C)) (observedSourceDensity H A C θ)).PosDef :=
  krausReducedFamily_source_posDef (covarianceKraus A C) (covarianceKraus_isHermitian A hA C)
    (observedOwnerDensity_posDef H A C hθ)

theorem observedSourceTransport_posDef (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) {θ : ℝ} (hθ : 0 < θ) :
    (observedSourceTransport H A C θ).PosDef :=
  transportOptimizer_posDef (observedSourceDensity_posDef H A C hθ) (observedSourceSource_posDef H A hA C hθ)

theorem observedOwnedGram_posSemidef (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) {θ : ℝ} (hθ : 0 < θ) :
    (observedOwnedGram H A C θ).PosSemidef :=
  covarianceGram_posSemidef A hA _ _ (observedOwnerDensity_posDef H A C hθ).posSemidef
    ((observedSourceTransport_posDef H A hA C hθ).posSemidef.mul_mul_conjTranspose_same _)

/-- The original count, rather than either support dimension, bounds the actual reduced balanced data. -/
theorem observedOwner_balanced_budgets (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1) {θ : ℝ} (hθ : 0 < θ) :
    realTrace (balancedDensity (observedSourceDensity H A C θ) (observedSourceTransport H A C θ)) ≤
        Real.sqrt (Fintype.card ι : ℝ) ∧
      realTrace (balancedRoot (observedSourceDensity H A C θ) (observedSourceTransport H A C θ) *
        balancedRoot (observedSourceDensity H A C θ) (observedSourceTransport H A C θ)) ≤ (Fintype.card ι : ℝ) := by
  let V := krausSupportEmbedding (covarianceKraus A C)
  let A₀ := compressedOriginalFamily A V
  have hA₀ : ∀ i, (A₀ i).IsHermitian := fun i => isometry_compression_isHermitian V (hA i)
  have hB₀ : covarianceKraus A₀ C = krausReducedFamily (covarianceKraus A C) :=
    (krausReducedFamily_eq_covarianceKraus_compressed A C).symm
  have heq : covarianceSource A₀ C (observedSourceDensity H A C θ) =
      krausChannel (krausReducedFamily (covarianceKraus A C)) (observedSourceDensity H A C θ) := by
    rw [covarianceSource_eq_kraus A₀ hA₀ hC0, hB₀]
  have hM : (covarianceSource A₀ C (observedSourceDensity H A C θ)).PosDef := by
    rw [heq]
    exact observedSourceSource_posDef H A hA C hθ
  have h := compressed_balancedTransport_budgets A hA hN hC0 hC1 V
    (krausSupportEmbedding_isometry (covarianceKraus A C)) (observedOwnerDensity_posDef H A C hθ)
    (observedOwnerDensity_trace H A C θ).le hM
  change realTrace (balancedDensity (observedSourceDensity H A C θ)
      (transportOptimizer (observedSourceDensity H A C θ) (covarianceSource A₀ C (observedSourceDensity H A C θ)))) ≤ _ ∧
    realTrace (balancedRoot (observedSourceDensity H A C θ)
      (transportOptimizer (observedSourceDensity H A C θ) (covarianceSource A₀ C (observedSourceDensity H A C θ))) *
      balancedRoot (observedSourceDensity H A C θ)
      (transportOptimizer (observedSourceDensity H A C θ) (covarianceSource A₀ C (observedSourceDensity H A C θ)))) ≤ _ at h
  rwa [heq] at h

end MatrixSpencer
