import HigherRankKS.ReducedSourceVelocity
import HigherRankKS.SupportedSourceMetric

open Matrix MatrixSpencer Filter Set
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace HigherRankKS.BalancedSourceResponse
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance balancedSourceCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance balancedSourceSpace :
    NormedSpace ℝ (selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) := inferInstance

/-- Partial source forcing at fixed density. -/
def forcing (A : ι → Matrix n n ℂ) (β : ℝ) (dc : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :=
  ∑ i, dc i • SupportedSourceMetric.term A β Z i S

/-- The actual nonlinear density channel, keeping the full input variation. -/
def channel (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :=
  ∑ i, c i • fderiv ℝ (SupportedSourceMetric.term A β Z i) S X


theorem mismatch_eq (A : ι → Matrix n n ℂ)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ → ι → ℝ) (hcs : ContDiffAt ℝ 2 c 0)
    (hc : ∀ i, 0 < c 0 i)
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) :
    let G := fun t : ℝ => jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (c t, S + t • X)
    BalancedTransportResponse.mismatch Z
      ((deriv G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
      ((deriv G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) =
      balancedDensity (SupportedSpin.density A X) Z - channel A ((1 : ℝ) / 2 ^ k) (c 0) Z S X -
        forcing A ((1 : ℝ) / 2 ^ k) (fun i => deriv (fun t => c t i) 0) Z S := by
  dsimp only
  rw [ReducedSourceVelocity.mismatch_eq A k hk c hcs hc S X hS Z]
  have hfirst (i : ι) : fderiv ℝ (SupportedSourceMetric.term A ((1 : ℝ) / 2 ^ k) Z i) S X =
      CFC.sqrt Z * ((sourceEmbedding A)ᴴ *
        fderiv ℝ (SourceDerivatives.term ((1 : ℝ) / 2 ^ k) (A i)) S X * sourceEmbedding A) * CFC.sqrt Z := by
    rw [SupportedSourceMetric.term_eq_sourceOutput,
      SupportedSourceCalculus.sourceOutput_first_physical (A i) (SupportedSourceMetric.balanceMap A Z)
        k hk S X hS]
    simp only [SupportedSourceMetric.balanceMap, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, (CFC.sqrt_nonneg Z).posSemidef.isHermitian.eq,
      Matrix.mul_assoc]
  simp only [channel, hfirst, forcing, SupportedSourceMetric.term, SupportedSpin.term,
    SupportedSpin.density, KSSupportSymmetry.compress, balancedDensity, transportInverseSqrt, SourceDerivatives.term]

/-- The true source channel differs from the mass-preserving scalar channel
by exactly the defect controlled by the source metric estimate. -/
theorem channel_sub_defect (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    channel A β c Z S X - SupportedSourceMetric.defect A β c Z S X =
      ∑ i, (c i * SupportedSourceMetric.massRatio A S X i) • SupportedSourceMetric.term A β Z i S := by
  simp only [channel, SupportedSourceMetric.defect, smul_sub, Finset.sum_sub_distrib, smul_smul]
  abel

end HigherRankKS.BalancedSourceResponse
