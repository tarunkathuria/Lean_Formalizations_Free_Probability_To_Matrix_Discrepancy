import MatrixSpencer.DyadicPotentialResponse
import MatrixSpencer.DyadicBalancedModel
import MatrixSpencer.CompressedGram

/-!
# Actual dyadic owner data on the physical source support

The owner density is the original global maximizer. Only its source-support
compression enters the auxiliary unconstrained response estimate.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer
namespace DyadicOwnerFrame

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]

local instance ownerFrameCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ownerFrameNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def observedOwnerDensity (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (m : ℕ) (θ : ℝ) : Matrix n n ℂ :=
  hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) (covarianceKraus A C) m θ

def observedSourceDensity (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (m : ℕ) (θ : ℝ) :=
  krausCompressedDensity (covarianceKraus A C) (observedOwnerDensity H A C m θ)

def observedSourceTransport (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (m : ℕ) (θ : ℝ) :=
  transportOptimizer (observedSourceDensity H A C m θ)
    (krausChannel (krausReducedFamily (covarianceKraus A C)) (observedSourceDensity H A C m θ))

def observedOwnedTransport (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (m : ℕ) (θ : ℝ) : Matrix n n ℂ :=
  krausSupportEmbedding (covarianceKraus A C) * observedSourceTransport H A C m θ *
    (krausSupportEmbedding (covarianceKraus A C))ᴴ

def observedOwnedGram (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (m : ℕ) (θ : ℝ) : Matrix ι ι ℝ :=
  covarianceGram A (observedOwnerDensity H A C m θ) (observedOwnedTransport H A C m θ)

theorem observedOwnerDensity_posDef (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (m : ℕ) (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) : (observedOwnerDensity H A C m θ).PosDef :=
  hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) (covarianceKraus A C) m hm θ hθ

theorem observedOwnerDensity_trace (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (m : ℕ) (θ : ℝ) : realTrace (observedOwnerDensity H A C m θ) = 1 :=
  hermitianDyadicDensityOptimizer_trace (H : Matrix n n ℂ) (covarianceKraus A C) m θ

theorem observedSourceDensity_posDef (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (m : ℕ) (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) : (observedSourceDensity H A C m θ).PosDef :=
  krausCompressedDensity_posDef (covarianceKraus A C) (observedOwnerDensity_posDef H A C m hm hθ)

theorem observedSourceSource_posDef (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (m : ℕ) (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) :
    (krausChannel (krausReducedFamily (covarianceKraus A C)) (observedSourceDensity H A C m θ)).PosDef :=
  krausReducedFamily_source_posDef (covarianceKraus A C) (mixedKraus_isHermitian A (CFC.sqrt C) hA)
    (observedOwnerDensity_posDef H A C m hm hθ)

theorem observedSourceTransport_posDef (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (m : ℕ) (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) :
    (observedSourceTransport H A C m θ).PosDef :=
  transportOptimizer_posDef (observedSourceDensity_posDef H A C m hm hθ) (observedSourceSource_posDef H A hA C m hm hθ)

theorem observedOwnedGram_posSemidef (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (m : ℕ) (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) :
    (observedOwnedGram H A C m θ).PosSemidef :=
  covarianceGram_posSemidef A hA _ _ (observedOwnerDensity_posDef H A C m hm hθ).posSemidef
    ((observedSourceTransport_posDef H A hA C m hm hθ).posSemidef.mul_mul_conjTranspose_same _)

/-- The original count, rather than either support dimension, bounds the actual reduced balanced data. -/
theorem observedOwner_balanced_budgets (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1) (m : ℕ) (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) :
    realTrace (balancedDensity (observedSourceDensity H A C m θ) (observedSourceTransport H A C m θ)) ≤
        Real.sqrt (Fintype.card ι : ℝ) ∧
      realTrace (balancedRoot (observedSourceDensity H A C m θ) (observedSourceTransport H A C m θ) *
        balancedRoot (observedSourceDensity H A C m θ) (observedSourceTransport H A C m θ)) ≤ (Fintype.card ι : ℝ) := by
  let V := krausSupportEmbedding (covarianceKraus A C)
  let A₀ := compressedOriginalFamily A V
  have hA₀ : ∀ i, (A₀ i).IsHermitian := fun i => isometry_compression_isHermitian V (hA i)
  have hB₀ : covarianceKraus A₀ C = krausReducedFamily (covarianceKraus A C) :=
    (krausReducedFamily_eq_covarianceKraus_compressed A C).symm
  have heq : covarianceSource A₀ C (observedSourceDensity H A C m θ) =
      krausChannel (krausReducedFamily (covarianceKraus A C)) (observedSourceDensity H A C m θ) := by
    rw [covarianceSource_eq_kraus A₀ hA₀ hC0, hB₀]
  have hM : (covarianceSource A₀ C (observedSourceDensity H A C m θ)).PosDef := by
    rw [heq]
    exact observedSourceSource_posDef H A hA C m hm hθ
  have h := compressed_balancedTransport_budgets A hA hN hC0 hC1 V
    (krausSupportEmbedding_isometry (covarianceKraus A C)) (observedOwnerDensity_posDef H A C m hm hθ)
    (observedOwnerDensity_trace H A C m θ).le hM
  change realTrace (balancedDensity (observedSourceDensity H A C m θ)
      (transportOptimizer (observedSourceDensity H A C m θ) (covarianceSource A₀ C (observedSourceDensity H A C m θ)))) ≤ _ ∧
    realTrace (balancedRoot (observedSourceDensity H A C m θ)
      (transportOptimizer (observedSourceDensity H A C m θ) (covarianceSource A₀ C (observedSourceDensity H A C m θ))) *
      balancedRoot (observedSourceDensity H A C m θ)
      (transportOptimizer (observedSourceDensity H A C m θ) (covarianceSource A₀ C (observedSourceDensity H A C m θ)))) ≤ _ at h
  rwa [heq] at h

/-- The compressed optimizer retains trace at most one, including empty physical support. -/
theorem observedSourceDensity_trace_le_one (H : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (m : ℕ) (hm : 1 ≤ m)
    {θ : ℝ} (hθ : 0 < θ) : realTrace (observedSourceDensity H A C m θ) ≤ 1 := by
  have h := realTrace_isometry_compression_le (observedOwnerDensity_posDef H A C m hm hθ).posSemidef
    (krausSupportEmbedding (covarianceKraus A C))
    (krausSupportEmbedding_isometry (covarianceKraus A C))
  exact h.trans_eq (observedOwnerDensity_trace H A C m θ)

/-- The actual source transport solves the reduced transport equation. -/
theorem observedSourceTransport_solve (H : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (m : ℕ) (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) :
    observedSourceTransport H A C m θ *
      krausChannel (krausReducedFamily (covarianceKraus A C)) (observedSourceDensity H A C m θ) *
      observedSourceTransport H A C m θ = observedSourceDensity H A C m θ :=
  transportOptimizer_solve (observedSourceDensity_posDef H A C m hm hθ)
    (observedSourceSource_posDef H A hA C m hm hθ)

/-- The inverse-transport budget retains the original coefficient labels after compression. -/
theorem observedOwner_inverseDensity_budget (H : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1) (m : ℕ) (hm : 1 ≤ m)
    {θ : ℝ} (hθ : 0 < θ) :
    realTrace ((observedSourceTransport H A C m θ)⁻¹ *
      balancedDensity (observedSourceDensity H A C m θ) (observedSourceTransport H A C m θ)) ≤
        (Fintype.card ι : ℝ) := by
  let V := krausSupportEmbedding (covarianceKraus A C)
  let A₀ := compressedOriginalFamily A V
  have hV : Vᴴ * V = 1 := krausSupportEmbedding_isometry (covarianceKraus A C)
  have hA₀ : ∀ i, (A₀ i).IsHermitian := fun i => isometry_compression_isHermitian V (hA i)
  have hN₀ : ∀ i, ‖A₀ i‖ ≤ 1 := fun i => isometry_compression_norm_le_one V hV (hA i) (hN i)
  have hB₀ : covarianceKraus A₀ C = krausReducedFamily (covarianceKraus A C) :=
    (krausReducedFamily_eq_covarianceKraus_compressed A C).symm
  have heq : covarianceSource A₀ C (observedSourceDensity H A C m θ) =
      krausChannel (krausReducedFamily (covarianceKraus A C)) (observedSourceDensity H A C m θ) := by
    rw [covarianceSource_eq_kraus A₀ hA₀ hC0, hB₀]
  have hM : (covarianceSource A₀ C (observedSourceDensity H A C m θ)).PosDef := by
    rw [heq]
    exact observedSourceSource_posDef H A hA C m hm hθ
  have h := DyadicBalancedModel.balancedTransport_inverseDensity_budget A₀ hA₀ hN₀ hC0 hC1
    (observedSourceDensity_posDef H A C m hm hθ)
    (observedSourceDensity_trace_le_one H A C m hm hθ) hM
  dsimp only at h
  rw [heq] at h
  exact h

/-- All three dyadic endpoint budgets are properties of the actual owner frame. -/
theorem observedOwner_three_budgets (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1) (m : ℕ) (hm : 1 ≤ m)
    {θ : ℝ} (hθ : 0 < θ) :
    realTrace (balancedDensity (observedSourceDensity H A C m θ) (observedSourceTransport H A C m θ)) ≤
        Real.sqrt (Fintype.card ι : ℝ) ∧
      realTrace (balancedRoot (observedSourceDensity H A C m θ) (observedSourceTransport H A C m θ) *
        balancedRoot (observedSourceDensity H A C m θ) (observedSourceTransport H A C m θ)) ≤
        (Fintype.card ι : ℝ) ∧
      realTrace ((observedSourceTransport H A C m θ)⁻¹ *
        balancedDensity (observedSourceDensity H A C m θ) (observedSourceTransport H A C m θ)) ≤
        (Fintype.card ι : ℝ) := by
  have hb := observedOwner_balanced_budgets H A hA hN hC0 hC1 m hm hθ
  exact ⟨hb.1, hb.2, observedOwner_inverseDensity_budget H A hA hN hC0 hC1 m hm hθ⟩

/-- The owner range cap becomes the same physical Gram cap on the actual source support. -/
theorem observedOwner_balancedGram_cap (H : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1) (m : ℕ) (hm : 1 ≤ m)
    {θ t : ℝ} (hθ : 0 < θ) (ht : 0 ≤ t)
    (hcap : ∀ u : EuclideanSpace ℝ ι,
      u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap →
      WithLp.ofLp u ⬝ᵥ (observedOwnedGram H A C m θ *ᵥ WithLp.ofLp u) ≤
        t * (WithLp.ofLp u ⬝ᵥ WithLp.ofLp u)) :
    physicalRealGram
      (balancedDensity (observedSourceDensity H A C m θ) (observedSourceTransport H A C m θ))
      (balancedKraus (krausReducedFamily (covarianceKraus A C)) (observedSourceTransport H A C m θ)) ≤
      algebraMap ℝ (Matrix ι ι ℝ) t :=
  compressed_balancedGram_cap A hA hC0 hC1 (observedOwnerDensity_posDef H A C m hm hθ).posSemidef
    (observedSourceTransport H A C m θ) (observedSourceTransport_posDef H A hA C m hm hθ) ht hcap

/-- The actual reduced balanced Kraus family is Hermitian and fixes its positive density. -/
theorem observedOwner_balanced_family_data (H : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (m : ℕ) (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) :
    let S₀ := observedSourceDensity H A C m θ
    let Z₀ := observedSourceTransport H A C m θ
    let D := balancedKraus (krausReducedFamily (covarianceKraus A C)) Z₀
    (∀ a, (D a).IsHermitian) ∧
      krausChannel D (balancedDensity S₀ Z₀) = balancedDensity S₀ Z₀ := by
  dsimp only
  have hB := mixedKraus_isHermitian A (CFC.sqrt C) hA
  exact ⟨balancedKraus_isHermitian _ (krausReducedFamily_isHermitian _ hB) _,
    balancedKraus_fixedPoint _ (observedSourceTransport_posDef H A hA C m hm hθ)
      (observedSourceTransport_solve H A hA C m hm hθ)⟩

end DyadicOwnerFrame
end MatrixSpencer
