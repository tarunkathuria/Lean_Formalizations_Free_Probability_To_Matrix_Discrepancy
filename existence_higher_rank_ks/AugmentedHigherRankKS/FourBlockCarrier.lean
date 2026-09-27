import AugmentedHigherRankKS.FourBlockSmoothness
import HigherRankKS.SourceDerivative

/-! The original atom carrier receives the full four-block marginal. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
namespace AugmentedHigherRankKS
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance carrierCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}

def carrier (A : Matrix n n ℂ) (S : Matrix (FourSpin n) (FourSpin n) ℂ) : Matrix n n ℂ :=
  HigherRankKS.carrier A (HigherRankKS.marginal S)

def compressedCarrier (A : Matrix n n ℂ) (S : Matrix (FourSpin n) (FourSpin n) ℂ) :
    Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ :=
  HigherRankKS.compressedCarrier A (HigherRankKS.marginal S)

def compressedCarrierCLM (A : Matrix n n ℂ) :
    selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) →L[ℝ]
      selfAdjoint (Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ) :=
  (HigherRankKS.compressedCarrierCLM A).comp (HigherRankKS.hermitianMarginalCLM (n := n ⊕ n))

@[simp] theorem compressedCarrierCLM_coe (A : Matrix n n ℂ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) :
    (compressedCarrierCLM A S : Matrix _ _ ℂ) = compressedCarrier A S := by
  simp only [compressedCarrierCLM, ContinuousLinearMap.comp_apply,
    HigherRankKS.compressedCarrierCLM_coe, HigherRankKS.hermitianMarginalCLM_coe,
    compressedCarrier]

theorem compressedCarrier_posDef (A : Matrix n n ℂ)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef) :
    (compressedCarrier A S).PosDef :=
  HigherRankKS.compressedCarrier_posDef A (HigherRankKS.marginal_posDef hS)

theorem carrier_posSemidef (A : Matrix n n ℂ)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef) :
    (carrier A S).PosSemidef :=
  HigherRankKS.carrier_posSemidef A (HigherRankKS.marginal_posSemidef hS)

theorem carrierPower_reconstruct (A : Matrix n n ℂ)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef) (k : ℕ) (hk : 1 ≤ k) :
    carrierPower ((1 : ℝ) / 2 ^ k) (carrier A S) =
      atomEmbedding A * carrierPower ((1 : ℝ) / 2 ^ k) (compressedCarrier A S) *
        (atomEmbedding A)ᴴ :=
  HigherRankKS.carrierPower_reconstruct A (HigherRankKS.marginal_posSemidef hS) k hk

/-- Trace adjointness of duplication and marginalization. -/
theorem realTrace_fourAtom_mul (A : Matrix n n ℂ) (X : Matrix (FourSpin n) (FourSpin n) ℂ) :
    realTrace (spinAtom A * X) = realTrace (A * marginal X) := by
  have h₁ := congrArg Complex.re (KSSpinSource.doubled_trace_mul (HigherRankKS.spinAtom A) X)
  have h₂ := congrArg Complex.re (KSSpinSource.doubled_trace_mul A (HigherRankKS.marginal X))
  exact h₁.trans h₂

theorem realTrace_compressedCarrier (A : Matrix n n ℂ) (hA : A.PosSemidef)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef) :
    realTrace (compressedCarrier A S) = realTrace (spinAtom A * S) := by
  rw [realTrace_fourAtom_mul]
  exact (HigherRankKS.SourceDerivative.realTrace_compressedCarrier A hA
    (HigherRankKS.marginal_posSemidef hS)).trans
    (congrArg Complex.re (KSSpinSource.doubled_trace_mul A (HigherRankKS.marginal S)))

end AugmentedHigherRankKS
