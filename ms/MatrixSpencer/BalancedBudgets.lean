import MatrixSpencer.BalancedTransport
import MatrixSpencer.CovarianceBounds

/-!
# Balanced budgets for the actual original contractions

The physical dimension is unrestricted in these local estimates. The trace
may be below one, as required after source-support compression.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

/-- The original covariance fidelity bound is homogeneous in the density trace. -/
theorem covarianceFidelity_le_sqrt_card_mul_trace (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    fidelity S (covarianceSource A C S) ≤ Real.sqrt (Fintype.card ι : ℝ) * realTrace S := by
  have hs0 := realTrace_nonneg hS
  have hfsq := fidelity_sq_le_trace_mul hS (covarianceSource_posSemidef A hA hC0 hS)
  have hcap := mul_le_mul_of_nonneg_left
    (realTrace_covarianceSource_le_card A hA hN hC0 hC1 hS) hs0
  have hroot := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ Fintype.card ι)
  have hr0 := Real.sqrt_nonneg (Fintype.card ι : ℝ)
  have hsq : fidelity S (covarianceSource A C S) ^ 2 ≤
      (Real.sqrt (Fintype.card ι : ℝ) * realTrace S) ^ 2 := by
    rw [mul_pow, hroot]
    nlinarith
  exact (sq_le_sq₀ (fidelity_nonneg S _) (mul_nonneg hr0 hs0)).mp hsq

/-- Subnormalized inputs satisfy the same retained-label fidelity budget. -/
theorem covarianceFidelity_le_sqrt_card_of_trace_le_one (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) (htrace : realTrace S ≤ 1) :
    fidelity S (covarianceSource A C S) ≤ Real.sqrt (Fintype.card ι : ℝ) := by
  have h := covarianceFidelity_le_sqrt_card_mul_trace A hA hN hC0 hC1 hS
  have hb := mul_le_mul_of_nonneg_left htrace (Real.sqrt_nonneg (Fintype.card ι : ℝ))
  simpa only [mul_one] using h.trans hb

/-- The physical balanced trace budgets use the original retained label count, at actual transport. -/
theorem balancedTransport_covariance_budgets (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    {S : Matrix n n ℂ} (hS : S.PosDef) (htrace : realTrace S ≤ 1)
    (hM : (covarianceSource A C S).PosDef) :
    let Z := transportOptimizer S (covarianceSource A C S)
    realTrace (balancedDensity S Z) ≤ Real.sqrt (Fintype.card ι : ℝ) ∧
      realTrace (balancedRoot S Z * balancedRoot S Z) ≤ (Fintype.card ι : ℝ) := by
  dsimp only
  have hZ := transportOptimizer_posDef hS hM
  have ht := transportOptimizer_solve hS hM
  have heq := covarianceSource_eq_kraus A hA hC0 S
  have hM' : (krausChannel (covarianceKraus A C) S).PosDef := by rw [← heq]; exact hM
  have hP := realTrace_balancedDensity_actual (covarianceKraus A C) hS hM'
  rw [← heq] at hP
  refine ⟨?_, ?_⟩
  · rw [hP]
    exact covarianceFidelity_le_sqrt_card_of_trace_le_one A hA hN hC0 hC1 hS.posSemidef htrace
  · have hR := realTrace_balancedRoot_square_le hS.posSemidef hZ ht
    have hsource := realTrace_covarianceSource_le_card A hA hN hC0 hC1 hS.posSemidef
    have hlast := mul_le_mul_of_nonneg_left htrace (Nat.cast_nonneg (Fintype.card ι) :
      (0 : ℝ) ≤ Fintype.card ι)
    simpa only [mul_one] using hR.trans (hsource.trans hlast)

end MatrixSpencer
