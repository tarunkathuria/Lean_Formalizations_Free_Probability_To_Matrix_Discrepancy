import MatrixSpencer.RectangularRidgeSupportedCap
import MatrixSpencer.RectangularRidgeLiveResponse
import MatrixSpencer.RectangularRidgeLiveOwnerBounds
import MatrixSpencer.RectangularRidgeLiveDomination
import MatrixSpencer.RectangularRidgePreparationData
import MatrixSpencer.RectangularRidgeUniformResponse
import MatrixSpencer.RectangularRidgeMovementDrift

/-! A successful actual preparation cap supplies the live response bound for
finite LDL movement. The original parameter count and center are retained;
only the actual live coordinate projection enters the source budget. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgePreparedResponse
open RectangularRidgePreparationData
open RectangularRidgeNumericalOptimizerFloor (size)
open RectangularRidgePrimitiveParameters
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgePreparedResponseCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgePreparedResponseSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
set_option maxHeartbeats 300000
attribute [local irreducible] RectangularRidgePotential.optimizer

/-- The actual preparation cap, together with the live projection invariant,
bounds the actual response with the original aspect-ratio-tuned coefficient. -/
theorem prepared_response (P : Parameters N d) (hP : P.Valid)
    (O : MSManuscriptSupportedOwner.Owner N) (hO : State O) (hcap : Cap P O)
    (F₀ : Finset (Fin N)) (hlive : O.physical ≤ (RectangularRidgeLiveOwner.owner F₀).physical)
    (hcount : 0 < RectangularRidgeLiveOwner.count F₀)
    (hprice : P.threshold=4096/Real.sqrt (RectangularRidgeLiveOwner.count F₀ : ℝ)) :
    realTrace (O.physical*RectangularRidgeMovementDrift.response P.count_pos P.atoms hP.1 O.physical P.center) ≤
      RectangularRidgeUniformResponse.coefficient N d P.count_pos * Real.sqrt (RectangularRidgeLiveOwner.count F₀ : ℝ) := by
  let ℓ : ℝ := RectangularRidgeLiveOwner.count F₀
  have hℓ : 0 < ℓ := by dsimp [ℓ]; exact_mod_cast hcount
  have hℓN : ℓ ≤ N := by dsimp [ℓ]; exact_mod_cast RectangularRidgeLiveOwner.count_le F₀
  have hC := hO.1.physical_posSemidef O (by norm_num [floor])
  have hm := RectangularRidgeTuning.depth_positive N d P.count_pos
  have hθ := weight_positive P.count_pos P.rectangular
  have hκ : 0 < ridge P := by
    have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by have := P.count_pos; have := P.rectangular; omega)
    dsimp [ridge]
    positivity
  let S := RectangularRidgePotential.optimizer (P.center : Matrix (Fin d) (Fin d) ℂ)
    (covarianceKraus P.atoms O.physical) (depth P) (theta P) (ridge P)
  have hS := RectangularRidgePotential.optimizer_mem (P.center : Matrix (Fin d) (Fin d) ℂ)
    (covarianceKraus P.atoms O.physical) (depth P) (theta P) (ridge P)
  have hsource : realTrace (covarianceSource P.atoms O.physical S) ≤ ℓ := by
    have hh := RectangularRidgeLiveOwnerBounds.source_trace_le P.atoms hP.1 hP.2.1 F₀ O.physical hlive S hS.1
    have htr : realTrace S=1 := hS.2
    simpa only [htr,mul_one] using hh
  have hc (u : EuclideanSpace ℝ (Fin N))
      (hu : u∈LinearMap.range (Matrix.toEuclideanCLM (𝕜:=ℝ) O.physical).toLinearMap) :
      WithLp.ofLp u ⬝ᵥ (RectangularRidgeOwnerFrame.ownedGram P.atoms O.physical S *ᵥ WithLp.ofLp u) ≤
        (4096/Real.sqrt ℓ)*(WithLp.ofLp u ⬝ᵥ WithLp.ofLp u) := by
    have hh := RectangularRidgeSupportedCap.stored_supported_cap P.center P.atoms hP.1 O (depth P) hm
      (by norm_num [floor] : 0 < floor) hO.1 hθ hκ hcap u hu
    rw [hprice] at hh
    exact hh
  have hh := RectangularRidgeLiveResponse.owner_response_le_of_source_trace_and_cap P.center P.atoms hP.1
    hC hO.2.1 (depth P) hm hθ hκ (by norm_num : (0:ℝ)<4096) hℓ hsource hc
  have hq : 1/(2:ℝ)^(depth P)=exponent N d P.count_pos := by
    simp [depth,exponent,RectangularRidgeTuning.order]
  rw [hq] at hh
  exact hh.trans (RectangularRidgeUniformResponse.local_response_le P.count_pos P.rectangular hℓ.le hℓN)

/-- The final local update uses the literal computed short and finite LDL draw.
Its expected potential increment has no separately supplied response bound. -/
theorem prepared_actual_movement (P : Parameters N d) (hP : P.Valid)
    (O : MSManuscriptSupportedOwner.Owner N) (hO : State O) (hcap : Cap P O)
    (F₀ : Finset (Fin N)) (hlive : O.physical ≤ (RectangularRidgeLiveOwner.owner F₀).physical)
    (hcount : 0 < RectangularRidgeLiveOwner.count F₀)
    (hprice : P.threshold=4096/Real.sqrt (RectangularRidgeLiveOwner.count F₀ : ℝ))
    (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hq : 0<realTrace (MSManuscriptNumericalMovement.covariance O.physical F x)) :
    let h := RectangularRidgeNumericalParameters.mesh (size d N)
    (∑s : MSManuscriptNumericalMovement.Draws O.physical F x,
      MSManuscriptNumericalMovement.weight O.physical F x s*(RectangularRidgeMovementDrift.value P.count_pos
        (P.center+h•ownerPhysicalIncrement P.atoms hP.1 (MSManuscriptNumericalMovement.increment O.physical F x s))
        P.atoms (MSManuscriptNumericalMovement.nextOwner O.physical F x h)-RectangularRidgeMovementDrift.value P.count_pos P.center P.atoms O.physical)) ≤
      h^2*(RectangularRidgeUniformResponse.coefficient N d P.count_pos*Real.sqrt (RectangularRidgeLiveOwner.count F₀ : ℝ)+1/(2:ℝ)^40) := by
  exact RectangularRidgeMovementDrift.actual_movement P.center P.atoms hP.1 hP.2.1 P.count_pos P.rectangular O
    hO.1 hO.2.1 hO.2.2 F x hq hP.2.2.1 (by norm_num [floor]) (by norm_num [floor])
    (prepared_response P hP O hO hcap F₀ hlive hcount hprice)


/-- The existing frozen-coordinate invariant supplies live support internally.
The only analytic cap is the actual cap returned by successful preparation. -/
theorem prepared_actual_movement_of_frozen (P : Parameters N d) (hP : P.Valid)
    (O : MSManuscriptSupportedOwner.Owner N) (hO : State O) (hcap : Cap P O)
    (F₀ : Finset (Fin N)) (hF₀ : ∀i∈F₀, O.physical*ᵥPi.single i 1=0)
    (hcount : 0 < RectangularRidgeLiveOwner.count F₀)
    (hprice : P.threshold=4096/Real.sqrt (RectangularRidgeLiveOwner.count F₀ : ℝ))
    (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hq : 0<realTrace (MSManuscriptNumericalMovement.covariance O.physical F x)) :
    let h := RectangularRidgeNumericalParameters.mesh (size d N)
    (∑s : MSManuscriptNumericalMovement.Draws O.physical F x,
      MSManuscriptNumericalMovement.weight O.physical F x s*(RectangularRidgeMovementDrift.value P.count_pos
        (P.center+h•ownerPhysicalIncrement P.atoms hP.1 (MSManuscriptNumericalMovement.increment O.physical F x s))
        P.atoms (MSManuscriptNumericalMovement.nextOwner O.physical F x h)-RectangularRidgeMovementDrift.value P.count_pos P.center P.atoms O.physical)) ≤
      h^2*(RectangularRidgeUniformResponse.coefficient N d P.count_pos*Real.sqrt (RectangularRidgeLiveOwner.count F₀ : ℝ)+1/(2:ℝ)^40) := by
  have hC := hO.1.physical_posSemidef O (by norm_num [floor])
  exact prepared_actual_movement P hP O hO hcap F₀
    (RectangularRidgeLiveDomination.covariance_le_projection O.physical hC hO.2.1 F₀ hF₀)
    hcount hprice F x hq

end MatrixSpencer.RectangularRidgePreparedResponse
