import AugmentedHigherRankKS.FourBlockObjectiveResponse
import AugmentedHigherRankKS.FourBlockFrameBridge
import HigherRankKS.SupportedResponseGeometry
import HigherRankKS.ResponseReduction

open Matrix MatrixSpencer HigherRankKS Filter Set
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace AugmentedHigherRankKS.PointwiseResponse
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance pointwiseResponseCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance pointwiseResponseSpace :
    NormedSpace ℝ (selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) := inferInstance

open ObjectiveResponse

def probeValue (A : ι → Matrix n n ℂ) (β : ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) (i : ι) : ℝ :=
  SourceDerivative.probe β (A i) (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S

def direct (A : ι → Matrix n n ℂ) (β : ℝ) (c : ℝ → ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) : ℝ :=
  ∑ i, iteratedDeriv 2 (fun t => c t i) 0 * probeValue A β Z S i

def budget (A : ι → Matrix n n ℂ) (β : ℝ) (c : ℝ → ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) : ℝ :=
  ∑ i, (deriv (fun t => c t i) 0) ^ 2 * probeValue A β Z S i / c 0 i

def scalarForce (A : ι → Matrix n n ℂ) (β : ℝ) (dc : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (K : Matrix (FourSpin n) (FourSpin n) ℂ)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) : ℝ :=
  tracePairing K X + ∑ i, dc i *
    (probeValue A β Z S i / realTrace (spinAtom (A i) * (S : Matrix (FourSpin n) (FourSpin n) ℂ))) *
    realTrace (spinAtom (A i) * (X : Matrix (FourSpin n) (FourSpin n) ℂ))

def frameMismatch (A : ι → Matrix n n ℂ) (β : ℝ) (c dc : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) :=
  let Y := balancedDensity (SupportedSpin.density A X) Z
  Y - TwoFrames.frameChannel
    (BalancedFrames.measurementFrame (SupportedSpin.probe A) c Z)
    (BalancedFrames.preparationFrame (SupportedSpin.probe A) (SupportedSpin.term A β S) c
      (SupportedSpin.density A S) Z) Y -
    ∑ i, dc i • SupportedSourceMetric.term A β Z i S

theorem responseTransport_eq (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosSemidef) :
    responseTransport A β c S = SupportedSpin.transport A β c S := by
  unfold responseTransport
  dsimp only
  rw [jointReducedSourcePair_snd_coe A β (c, S) hc hS]
  rfl

private theorem energy_congr {m : Type*} [Fintype m] [DecidableEq m]
    {P Q : Matrix m m ℂ} (hP : P.PosDef) (hQ : Q.PosDef) (h : P = Q)
    {X Y : Matrix m m ℂ} (hXY : X = Y) :
    SylvesterMetric.energy P hP X = SylvesterMetric.energy Q hQ Y := by
  subst Q
  subst Y
  rfl

/-- The response energy uses the concrete balanced source and concrete frame defect. -/
theorem responseEnergy_eq_frame (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (k : ℕ) (hk : 1 ≤ k)
    (c : ℝ → ι → ℝ) (hcs : ContDiffAt ℝ 2 c 0) (hc : ∀ i, 0 < c 0 i)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    let Z := SupportedSpin.transport A ((1 : ℝ) / 2 ^ k) (c 0) S
    responseEnergy A hA k hk c hc S X hS =
      SylvesterMetric.energy (SupportedSourceMetric.balanced A ((1 : ℝ) / 2 ^ k) (c 0) S)
        (SupportedSourceMetric.balanced_posDef A hA (c 0) hc k hk S hS)
        (frameMismatch A ((1 : ℝ) / 2 ^ k) (c 0) (fun i => deriv (fun t => c t i) 0) Z S X -
          SupportedSourceMetric.defect A ((1 : ℝ) / 2 ^ k) (c 0) Z S X) := by
  have hfirst : ((jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (c 0, S)).1 :
      Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) = SupportedSpin.density A S :=
    hermitianRectangularCompressionCLM_coe (sourceEmbedding A) S
  have hsecond := jointReducedSourcePair_snd_coe A ((1 : ℝ) / 2 ^ k) (c 0, S)
    (fun i => (hc i).le) hS.posSemidef
  have hZ := SupportedSpin.transport_posDef A hA hc hS k hk
  have hm := SupportedFrameBridge.mismatch_eq_frame_defect A hA k hk c hcs hc S X hS
    (SupportedSpin.transport A ((1 : ℝ) / 2 ^ k) (c 0) S) hZ
  dsimp only at hm ⊢
  have hw : BalancedTransportResponse.weight
      ((jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (c 0, S)).1 :
        Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
      ((jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (c 0, S)).2 :
        Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) =
      SupportedSourceMetric.balanced A ((1 : ℝ) / 2 ^ k) (c 0) S := by
    rw [hfirst, hsecond, BalancedTransportResponse.weight_eq_balancedDensity
      (SupportedSpin.density_posDef A hS) (compressedSource_posDef A hA hc hS k hk)]
    rfl
  unfold responseEnergy
  dsimp only
  apply energy_congr _ _ hw
  simpa only [responseTransport_eq A _ (c 0) (fun i => (hc i).le) S hS.posSemidef,
    reducedCurve, frameMismatch] using hm

/-- The root curvature is nonnegative as a cost on every full density variation. -/
theorem root_cost_nonneg (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    0 ≤ -fderiv ℝ (fderiv ℝ (tsallisPotential θ)) S X X := by
  by_cases hX : X = 0
  · simp [hX]
  · exact neg_nonneg.mpr (OptimizerResponse.tsallis_hessian_neg θ hθ S X hS hX).le



/-- With independent reserves having zero initial velocity, no scalar source residual occurs. -/
theorem sourceAcceleration_zero_velocity (A : ι → Matrix n n ℂ)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ → ι → ℝ)
    (hdc : ∀ i, deriv (fun t => c t i) 0 = 0)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosSemidef)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    sourceAcceleration A ((1 : ℝ) / 2 ^ k) c
      (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S X =
      direct A ((1 : ℝ) / 2 ^ k) c Z S -
      SupportedSourceMetric.curvature A ((1 : ℝ) / 2 ^ k) (c 0) Z S X := by
  rw [SupportedSourceMetric.curvature_eq_probe A (c 0) Z hZ k hk S X hS]
  simp only [sourceAcceleration, direct, probeValue, hdc, mul_zero, zero_mul,
    add_zero, Finset.sum_add_distrib, sub_neg_eq_add]

/-- The genuine joint Hessian is paid by source curvature and the scalar-reference channel. -/
theorem independent_response_le (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (c : ℝ → ι → ℝ) (hcs : ContDiffAt ℝ 2 c 0) (hc : ∀ i, 0 < c 0 i)
    (hdc : ∀ i, deriv (fun t => c t i) 0 = 0)
    (H K : Matrix (FourSpin n) (FourSpin n) ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    let β := (1 : ℝ) / 2 ^ k
    let Z := SupportedSpin.transport A β (c 0) S
    let P := SupportedSourceMetric.balanced A β (c 0) S
    let hP := SupportedSourceMetric.balanced_posDef A hA (c 0) hc k hk S hS
    iteratedDeriv 2 (fun t : ℝ => hermitianObjective (H+t • K) A β (c t) θ (S+t • X)) 0 / 2 ≤
      direct A β c Z S / 2 + tracePairing K X -
      (2 * β / (1 + β)) / 2 * SylvesterMetric.energy P hP
        (frameMismatch A β (c 0) (fun _ => 0) Z S X) := by
  dsimp only
  rw [objective_second_affine A hA k hk c hcs hc H K θ S X hS,
    responseTransport_eq A _ (c 0) (fun i => (hc i).le) S hS.posSemidef,
    sourceAcceleration_zero_velocity A k hk c hdc _
      (SupportedSpin.transport_posDef A hA hc hS k hk).posSemidef S X hS,
    responseEnergy_eq_frame A hA k hk c hcs hc S X hS]
  simp only [hdc]
  have hW := SupportedFrameBridge.frame_mismatch_isHermitian A ((1 : ℝ) / 2 ^ k)
    (c 0) (fun _ => 0) (SupportedSpin.transport A ((1 : ℝ) / 2 ^ k) (c 0) S) S X hS.posSemidef
  have ha := SupportedSourceMetric.actual_full_absorption A hA hne (c 0) hc k hk S X hS hW
  have hr := root_cost_nonneg θ hθ S X hS
  change _ ≤ _ at ha
  dsimp only [frameMismatch] at *
  linarith

end AugmentedHigherRankKS.PointwiseResponse
