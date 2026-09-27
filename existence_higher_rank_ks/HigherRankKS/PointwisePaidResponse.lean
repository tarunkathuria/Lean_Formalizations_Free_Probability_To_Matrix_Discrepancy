import HigherRankKS.PointwiseResponse
import HigherRankKS.ObjectiveResponse

open Matrix MatrixSpencer Filter Set
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace HigherRankKS.PointwiseResponse
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance pointwisePaidCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance pointwisePaidSpace :
    NormedSpace ℝ (selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) := inferInstance

/-- The actual affine objective response after both source payments.
Every source, transport, derivative, and curvature input is concrete;
the density variation is an arbitrary full Hermitian matrix. -/
theorem objective_second_le (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (c : ℝ → ι → ℝ) (hcs : ContDiffAt ℝ 2 c 0) (hc : ∀ i, 0 < c 0 i)
    (H K : Matrix (n ⊕ n) (n ⊕ n) ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    let β := (1 : ℝ) / 2 ^ k
    let Z := SupportedSpin.transport A β (c 0) S
    let P := SupportedSourceMetric.balanced A β (c 0) S
    let hP := SupportedSourceMetric.balanced_posDef A hA (c 0) hc k hk S hS
    let W := frameMismatch A β (c 0) (fun i => deriv (fun t => c t i) 0) Z S X
    iteratedDeriv 2 (fun t : ℝ => hermitianObjective (H + t • K) A β (c t) θ (S + t • X)) 0 / 2 ≤
      direct A β c Z S / 2 + (1 - β) / β * budget A β c Z S +
      scalarForce A β (fun i => deriv (fun t => c t i) 0) Z K S X -
      β / 2 * SylvesterMetric.energy P hP W := by
  dsimp only
  rw [ObjectiveResponse.objective_second_affine A hA k hk c hcs hc H K θ S X hS,
    responseTransport_eq A _ (c 0) (fun i => (hc i).le) S hS.posSemidef,
    responseEnergy_eq_frame A hA k hk c hcs hc S X hS,
    sourceAcceleration_split A k hk c _
      (SupportedSpin.transport_posDef A hA hc hS k hk).posSemidef K S X hS]
  exact paid_quadratic_le A hA hne k hk c hc K θ hθ S X hS

end HigherRankKS.PointwiseResponse
