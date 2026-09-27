import FaithfulMS.RectangularDirectSolver
import MatrixSpencer.KSJacobiPolynomialBounds

/-! A polynomial bound on the directly computed Gram, obtained from its
weighted trace and fidelity, without any finite-difference value queries. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularDirectMagnitude
open FaithfulMS.DirectDensity RectangularRidgeOwnerFrame
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance {j : Type*} [Fintype j] [DecidableEq j] : CStarAlgebra (Matrix j j ℂ) := {}

lemma trace_gram (B : ι → Matrix n n ℂ) (hB : ∀ i, (B i).IsHermitian)
    (S Z : Matrix n n ℂ) :
    realTrace (covarianceGram B S Z) = realTrace (krausChannel B S * Z) := by
  change (∑ i, realTrace (S * B i * Z * B i)) = _
  simp only [krausChannel, Matrix.sum_mul, realTrace_sum, fun i => (hB i).eq]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = realTrace (B i * (S * B i * Z)) := realTrace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

lemma trace_covariance_gram (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {S : Matrix n n ℂ} (hS : S.PosDef) :
    realTrace (C * gamma A C S) = fidelity S (krausChannel (covarianceKraus A C) S) := by
  have he := covarianceGram_compressed_factor A hA C S (sourceTransport A C S)
  have ht := congrArg realTrace he
  have hB : ∀ i, (covarianceKraus A C i).IsHermitian := mixedKraus_isHermitian A (CFC.sqrt C) hA
  have hB₀ : ∀ i, (krausReducedFamily (covarianceKraus A C) i).IsHermitian :=
    krausReducedFamily_isHermitian (covarianceKraus A C) hB
  rw [trace_gram (krausReducedFamily (covarianceKraus A C)) hB₀] at ht
  change realTrace (krausChannel (krausReducedFamily (covarianceKraus A C)) (sourceDensity A C S) *
    transportOptimizer (sourceDensity A C S)
      (krausChannel (krausReducedFamily (covarianceKraus A C)) (sourceDensity A C S))) = _ at ht
  rw [trace_transportOptimizer_eq_fidelity (sourceDensity_posDef A C hS)
    (sourceSource_posDef A hA C hS)] at ht
  dsimp only [sourceDensity] at ht
  rw [krausReducedFamily_channel (covarianceKraus A C)
    hB] at ht
  rw [← fidelity_kraus_support_compression (covarianceKraus A C) hS.posSemidef] at ht
  change _ = realTrace (CFC.sqrt C * gamma A C S * CFC.sqrt C) at ht
  rw [realTrace_mul_comm (CFC.sqrt C * gamma A C S) (CFC.sqrt C),
    ← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self C hC.nonneg] at ht
  exact ht.symm

end MatrixSpencer.RectangularDirectMagnitude
