import MatrixSpencer.CoefficientResponse
import MatrixSpencer.ObservedCapResponse
import MatrixSpencer.BalancedBudgets

/-!
# Actual owner response bound on faithful-source charts

The original contraction count controls both physical budgets. The left hand
side is the trace of the original coefficient covariance against half the
actual optimized center Hessian.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

local instance faithfulOwnerCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance faithfulOwnerNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance faithfulOwnerFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

/-- All scalar budgets for the spectral estimate are discharged using the original contractions. -/
theorem faithful_owner_response_le_of_physical_cap [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    {θ L : ℝ} (hθ : 0 < θ) (hL : 0 < L) (hk : 0 < Fintype.card ι)
    (hM : (krausChannel (covarianceKraus A C)
      (densityOptimizer (H : Matrix n n ℂ) (covarianceKraus A C) θ)).PosDef)
    (hcap : let S := hermitianDensityOptimizer (H : Matrix n n ℂ) (covarianceKraus A C) θ
      let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel (covarianceKraus A C) (S : Matrix n n ℂ))
      physicalRealGram (balancedDensity S Z) (balancedKraus (covarianceKraus A C) Z) ≤
        algebraMap ℝ (Matrix ι ι ℝ) (L / Real.sqrt (Fintype.card ι : ℝ))) :
    realTrace (C * ownerCoefficientResponse A hA C θ H) ≤
      (2 + 12 * Real.sqrt L / θ) * Real.sqrt (Fintype.card ι : ℝ) := by
  let B := covarianceKraus A C
  have hB : ∀ a, (B a).IsHermitian := covarianceKraus_isHermitian A hA C
  let S := hermitianDensityOptimizer (H : Matrix n n ℂ) B θ
  have hS : (S : Matrix n n ℂ).PosDef := hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ
  have hMS : (krausChannel B (S : Matrix n n ℂ)).PosDef :=
    hermitianDensityOptimizer_source_posDef (H : Matrix n n ℂ) B θ hM
  let Z := transportOptimizer (S : Matrix n n ℂ) (krausChannel B (S : Matrix n n ℂ))
  have hZ : Z.PosDef := transportOptimizer_posDef hS hMS
  have hMc : (covarianceSource A C (S : Matrix n n ℂ)).PosDef := by
    rw [covarianceSource_eq_kraus A hA hC0]
    exact hMS
  have hbud := balancedTransport_covariance_budgets A hA hN hC0 hC1 hS
    (hermitianDensityOptimizer_trace (H : Matrix n n ℂ) B θ).le hMc
  rw [covarianceSource_eq_kraus A hA hC0] at hbud
  have htrace := ObservedCapResponse.response_trace_le_budget
    (balancedKraus B Z) (balancedKraus_isHermitian B hB Z) hθ
    (balancedDensity_posDef hS hZ) (balancedRoot_posDef hS hZ)
    (Nat.cast_pos.mpr hk) hL hbud.1 hbud.2 hcap
    (balancedKraus_fixedPoint B hZ (transportOptimizer_solve hS hMS))
  rw [ownerCoefficientResponse_trace_eq A hA hC0 θ H]
  exact (faithful_observed_response_le H B hB hθ hM).trans htrace

end MatrixSpencer
