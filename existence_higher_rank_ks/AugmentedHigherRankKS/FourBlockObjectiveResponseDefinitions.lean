import AugmentedHigherRankKS.FourBlockObjectiveResponseCore

open Matrix MatrixSpencer HigherRankKS Filter Set
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace AugmentedHigherRankKS.ObjectiveResponse
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance objectiveResponseMainCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance objectiveResponseMainSpace :
    NormedSpace ℝ (selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) := inferInstance
local instance objectiveResponseMainTangentGroup : NormedAddCommGroup (densityTangent (n := FourSpin n)) := inferInstance
local instance objectiveResponseMainTangentSpace : NormedSpace ℝ (densityTangent (n := FourSpin n)) := inferInstance

/-- The actual supported transport at the basepoint of the response. -/
def responseTransport (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) :=
  let R := jointReducedSourcePair A β (c, S)
  transportOptimizer ((R.1) : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    ((R.2) : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)

/-- The actual inverse-Sylvester mismatch energy along the full response. -/
def responseEnergy (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ → ι → ℝ) (hc : ∀ i, 0 < c 0 i)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) : ℝ :=
  let R := jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (c 0, S)
  let hp := SourceResponse.reduced_pair_posDef A hA k hk (c 0, S) hc hS
  let G := reducedCurve A ((1 : ℝ) / 2 ^ k) c S X
  SylvesterMetric.energy
    (BalancedTransportResponse.weight (R.1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
      (R.2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ))
    (BalancedTransportResponse.weight_posDef hp.1 hp.2)
    (BalancedTransportResponse.mismatch (responseTransport A ((1 : ℝ) / 2 ^ k) (c 0) S)
      ((deriv G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
      ((deriv G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ))


end AugmentedHigherRankKS.ObjectiveResponse
