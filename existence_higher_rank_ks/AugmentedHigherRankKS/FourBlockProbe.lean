import AugmentedHigherRankKS.FourBlockCarrier
import AugmentedHigherRankKS.FourBlockSourceDerivatives

/-! Fixed-transport scalar probes of the actual four-block source. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
namespace AugmentedHigherRankKS.SourceDerivative
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance probeCStar {j : Type*} [Fintype j] [DecidableEq j] : CStarAlgebra (Matrix j j ℂ) := {}

def traceProbeCLM (W : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  HigherRankKS.SourceDerivative.traceProbeCLM W

@[simp] theorem traceProbeCLM_apply (W X : Matrix n n ℂ) :
    traceProbeCLM W X = realTrace (W * X) := rfl

def probe (β : ℝ) (A : Matrix n n ℂ) (Z : Matrix (FourSpin n) (FourSpin n) ℂ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) : ℝ :=
  realTrace (Z * sourceTerm β A S)

theorem contDiffAt_probe (A : Matrix n n ℂ) (Z : Matrix (FourSpin n) (FourSpin n) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (probe ((1 : ℝ) / 2 ^ k) A Z) S :=
  (traceProbeCLM Z).contDiff.contDiffAt.comp S (contDiffAt_sourceTerm A k hk S hS)

theorem realTrace_compressedCarrier (A : Matrix n n ℂ) (hA : A.PosSemidef)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef) :
    realTrace (compressedCarrier A S) = realTrace (spinAtom A * S) :=
  AugmentedHigherRankKS.realTrace_compressedCarrier A hA hS

end AugmentedHigherRankKS.SourceDerivative
