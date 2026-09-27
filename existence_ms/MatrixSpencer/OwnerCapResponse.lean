import MatrixSpencer.OwnerFrame
import MatrixSpencer.SingularBalancedResponse
import MatrixSpencer.ObservedCapResponse

/-!
# Cap-to-response for the actual owner at every covariance rank

Both the coefficient covariance and its physical source may be singular.
The actual global optimizer, original contraction count, and Tsallis
parameter are retained throughout the comparison.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]

local instance ownerCapCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ownerCapNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- The actual optimized center response obeys the sharp cap bound, with no source-rank restriction. -/
theorem owner_response_le_of_ownedGram_cap
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    {θ L : ℝ} (hθ : 0 < θ) (hL : 0 < L) (hk : 0 < Fintype.card ι)
    (hcap : ∀ u : EuclideanSpace ℝ ι,
      u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap →
      WithLp.ofLp u ⬝ᵥ (observedOwnedGram H A C θ *ᵥ WithLp.ofLp u) ≤
        (L / Real.sqrt (Fintype.card ι : ℝ)) * (WithLp.ofLp u ⬝ᵥ WithLp.ofLp u)) :
    realTrace (C * ownerCoefficientResponse A hA C θ H) ≤
      (2 + 12 * Real.sqrt L / θ) * Real.sqrt (Fintype.card ι : ℝ) := by
  let B := covarianceKraus A C
  have hB : ∀ a, (B a).IsHermitian := covarianceKraus_isHermitian A hA C
  let B₀ := krausReducedFamily B
  have hB₀ : ∀ a, (B₀ a).IsHermitian := krausReducedFamily_isHermitian B hB
  let S₀ := observedSourceDensity H A C θ
  let Z₀ := observedSourceTransport H A C θ
  have hS₀ : S₀.PosDef := observedSourceDensity_posDef H A C hθ
  have hM₀ : (krausChannel B₀ S₀).PosDef := observedSourceSource_posDef H A hA C hθ
  have hZ₀ : Z₀.PosDef := observedSourceTransport_posDef H A hA C hθ
  have ht : 0 ≤ L / Real.sqrt (Fintype.card ι : ℝ) := div_nonneg hL.le (Real.sqrt_nonneg _)
  have hgram := compressed_balancedGram_cap A hA hC0 hC1
    (observedOwnerDensity_posDef H A C hθ).posSemidef Z₀ hZ₀ ht hcap
  have hbud := observedOwner_balanced_budgets H A hA hN hC0 hC1 hθ
  have htrace := ObservedCapResponse.response_trace_le_budget
    (balancedKraus B₀ Z₀) (balancedKraus_isHermitian B₀ hB₀ Z₀) hθ
    (balancedDensity_posDef hS₀ hZ₀) (balancedRoot_posDef hS₀ hZ₀)
    (Nat.cast_pos.mpr hk) hL hbud.1 hbud.2 hgram
    (balancedKraus_fixedPoint B₀ hZ₀ (transportOptimizer_solve hS₀ hM₀))
  rw [ownerCoefficientResponse_trace_eq A hA hC0 θ H]
  exact (singular_observed_response_le H B hB θ hθ).trans htrace

end MatrixSpencer
