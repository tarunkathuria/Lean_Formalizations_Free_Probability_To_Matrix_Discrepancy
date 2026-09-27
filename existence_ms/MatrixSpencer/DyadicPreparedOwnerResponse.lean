import MatrixSpencer.RegularizedOwnerPreparation
import MatrixSpencer.DyadicOwnerShavingDerivative
import MatrixSpencer.DyadicOwnerCapResponse

/-! Actual compact paid preparation for the dyadic owner potential.
The range cap follows from its own supported derivative, and the actual
coefficient response follows from the proved all-rank cap theorem. -/

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Set
noncomputable section
namespace MatrixSpencer
namespace DyadicPreparedOwnerResponse

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance preparedDyadicCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance preparedDyadicSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def responseBound (m : ℕ) (θ L k : ℝ) : ℝ :=
  2 * Real.sqrt k + (6 * L ^ (1 / (2 : ℝ) ^ m) / (θ * (1 / (2 : ℝ) ^ m))) *
    k ^ (1 - 1 / (2 : ℝ) ^ m)

/-- An actual minimizer's owned Gram is capped on its actual covariance range. -/
theorem owner_minimizer_ownedGram_cap
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C K : Matrix ι ι ℝ}
    (m : ℕ) (hm : 1 ≤ m) {θ t : ℝ} (hθ : 0 < θ) (hK : K ∈ Icc 0 C)
    (hmin : IsMinOn (covarianceObjective C
      (fun Q => regularizedOwnerPotential (H : Matrix n n ℂ) A Q (dyadicTsallisRegularizer m θ)) t)
      (Icc 0 C) K) :
    ∀ u : EuclideanSpace ℝ ι,
      u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) K).toLinearMap →
      WithLp.ofLp u ⬝ᵥ (DyadicOwnerFrame.observedOwnedGram H A K m θ *ᵥ WithLp.ofLp u) ≤
        t * (WithLp.ofLp u ⬝ᵥ WithLp.ofLp u) := by
  intro u hu
  have hc := covariance_minimizer_directional_cap hK hmin hu
    (hasDerivAt_dyadicOwnerPotential_supported_shave H A hA hK.1.posSemidef u hu m hm θ hθ)
  have hn : ‖u‖ ^ 2 = WithLp.ofLp u ⬝ᵥ WithLp.ofLp u := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
      (real_inner_self_eq_norm_sq u).symm
  rwa [hn] at hc

/-- Compact minimization gives actual paid trace, actual range cap, and actual response. -/
theorem exists_prepared_owner_response
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    (m : ℕ) (hm : 1 ≤ m) {θ L : ℝ} (hθ : 0 < θ) (hL : 0 < L) (hk : 0 < Fintype.card ι) :
    ∃ K ∈ Icc 0 C,
      regularizedOwnerPotential (H : Matrix n n ℂ) A K (dyadicTsallisRegularizer m θ) +
        (L / Real.sqrt (Fintype.card ι : ℝ)) * realTrace (C - K) ≤
          regularizedOwnerPotential (H : Matrix n n ℂ) A C (dyadicTsallisRegularizer m θ) ∧
      realTrace (C - K) ≤ 2 * (Fintype.card ι : ℝ) / L ∧
      (∀ u : EuclideanSpace ℝ ι,
        u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) K).toLinearMap →
        WithLp.ofLp u ⬝ᵥ (DyadicOwnerFrame.observedOwnedGram H A K m θ *ᵥ WithLp.ofLp u) ≤
          (L / Real.sqrt (Fintype.card ι : ℝ)) * (WithLp.ofLp u ⬝ᵥ WithLp.ofLp u)) ∧
      realTrace (K * dyadicOwnerCoefficientResponse A hA K m θ H) ≤
        responseBound m θ L (Fintype.card ι : ℝ) := by
  have hs : 0 < Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)
  obtain ⟨K, hK, hmin, hpaid, _, hbudget⟩ := exists_regularized_owner_preparation_trace_budget
    (H : Matrix n n ℂ) A hA hN hC0 hC1 (dyadicTsallisRegularizer m θ)
    (continuousOn_density_dyadicTsallisRegularizer m θ) (div_pos hL hs)
  have hcap := owner_minimizer_ownedGram_cap H A hA m hm hθ hK hmin
  refine ⟨K, hK, hpaid, ?_, hcap,
    DyadicOwnerCapResponse.owner_response_le_of_ownedGram_cap H A hA hN
      hK.1.posSemidef (hK.2.trans hC1) m hm hθ hL hk hcap⟩
  convert hbudget using 1
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ Fintype.card ι)
  field_simp
  nlinarith

end DyadicPreparedOwnerResponse
end MatrixSpencer
