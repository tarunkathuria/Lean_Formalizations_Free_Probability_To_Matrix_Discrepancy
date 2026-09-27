import MatrixSpencer.OwnerPreparation
import MatrixSpencer.OwnerShavingDerivative
import MatrixSpencer.OwnerCapResponse
import MatrixSpencer.OwnerResponseGeometry

/-!
# Actual paid preparation supplies the observed response bound

The cap is obtained by differentiating supported shaves of an actual
compact minimizer; neither a derivative nor a cap oracle is assumed.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Set
noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance preparedOwnerCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance preparedOwnerSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- The actual owned Gram is capped on the minimizer's actual coefficient range. -/
theorem owner_minimizer_ownedGram_cap
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C K : Matrix ι ι ℝ}
    {θ t : ℝ} (hθ : 0 < θ) (hK : K ∈ Icc 0 C)
    (hmin : IsMinOn (covarianceObjective C
      (fun Q => ownerPotential (H : Matrix n n ℂ) A Q θ) t) (Icc 0 C) K) :
    ∀ u : EuclideanSpace ℝ ι,
      u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) K).toLinearMap →
      WithLp.ofLp u ⬝ᵥ (observedOwnedGram H A K θ *ᵥ WithLp.ofLp u) ≤
        t * (WithLp.ofLp u ⬝ᵥ WithLp.ofLp u) := by
  intro u hu
  have hc := covariance_minimizer_directional_cap hK hmin hu
    (hasDerivAt_ownerPotential_supported_shave H A hA hK.1.posSemidef u hu hθ)
  have hn : ‖u‖ ^ 2 = WithLp.ofLp u ⬝ᵥ WithLp.ofLp u := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
      (real_inner_self_eq_norm_sq u).symm
  rwa [hn] at hc

/-- A real compact preparation simultaneously pays its trace loss and bounds actual response. -/
theorem exists_prepared_owner_response
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    {θ L : ℝ} (hθ : 0 < θ) (hL : 0 < L) (hk : 0 < Fintype.card ι) :
    ∃ K ∈ Icc 0 C,
      ownerPotential (H : Matrix n n ℂ) A K θ +
        (L / Real.sqrt (Fintype.card ι : ℝ)) * realTrace (C - K) ≤
          ownerPotential (H : Matrix n n ℂ) A C θ ∧
      realTrace (C - K) ≤ 2 * (Fintype.card ι : ℝ) / L ∧
      (∀ u : EuclideanSpace ℝ ι,
        u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) K).toLinearMap →
        WithLp.ofLp u ⬝ᵥ (observedOwnedGram H A K θ *ᵥ WithLp.ofLp u) ≤
          (L / Real.sqrt (Fintype.card ι : ℝ)) * (WithLp.ofLp u ⬝ᵥ WithLp.ofLp u)) ∧
      realTrace (K * ownerCoefficientResponse A hA K θ H) ≤
        (2 + 12 * Real.sqrt L / θ) * Real.sqrt (Fintype.card ι : ℝ) := by
  have hs : 0 < Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)
  obtain ⟨K, hK, hmin, hpaid, _, hbudget⟩ := exists_owner_preparation_trace_budget
    (H : Matrix n n ℂ) A hA hN hC0 hC1 θ (div_pos hL hs)
  have hcap := owner_minimizer_ownedGram_cap H A hA hθ hK hmin
  refine ⟨K, hK, hpaid, ?_, hcap,
    owner_response_le_of_ownedGram_cap H A hA hN hK.1.posSemidef (hK.2.trans hC1)
      hθ hL hk hcap⟩
  convert hbudget using 1
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ Fintype.card ι)
  field_simp
  nlinarith

end MatrixSpencer
