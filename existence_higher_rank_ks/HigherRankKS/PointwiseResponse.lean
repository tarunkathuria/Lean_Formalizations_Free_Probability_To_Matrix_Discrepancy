import HigherRankKS.ObjectiveResponseDefinitions
import HigherRankKS.SupportedScalarMetric
import HigherRankKS.SupportedFrameBridge
import HigherRankKS.SupportedResponseGeometry
import HigherRankKS.ResponseReduction

open Matrix MatrixSpencer Filter Set
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace HigherRankKS.PointwiseResponse
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance pointwiseResponseCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance pointwiseResponseSpace :
    NormedSpace ℝ (selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) := inferInstance

open ObjectiveResponse

def probeValue (A : ι → Matrix n n ℂ) (β : ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) (i : ι) : ℝ :=
  SourceDerivative.probe β (A i) (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S

def direct (A : ι → Matrix n n ℂ) (β : ℝ) (c : ℝ → ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) : ℝ :=
  ∑ i, iteratedDeriv 2 (fun t => c t i) 0 * probeValue A β Z S i

def budget (A : ι → Matrix n n ℂ) (β : ℝ) (c : ℝ → ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) : ℝ :=
  ∑ i, (deriv (fun t => c t i) 0) ^ 2 * probeValue A β Z S i / c 0 i

def scalarForce (A : ι → Matrix n n ℂ) (β : ℝ) (dc : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (K : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) : ℝ :=
  tracePairing K X + ∑ i, dc i *
    (probeValue A β Z S i / realTrace (spinAtom (A i) * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))) *
    realTrace (spinAtom (A i) * (X : Matrix (n ⊕ n) (n ⊕ n) ℂ))

def frameMismatch (A : ι → Matrix n n ℂ) (β : ℝ) (c dc : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :=
  let Y := balancedDensity (SupportedSpin.density A X) Z
  Y - TwoFrames.frameChannel
    (BalancedFrames.measurementFrame (SupportedSpin.probe A) c Z)
    (BalancedFrames.preparationFrame (SupportedSpin.probe A) (SupportedSpin.term A β S) c
      (SupportedSpin.density A S) Z) Y -
    ∑ i, dc i • SupportedSourceMetric.term A β Z i S

theorem responseTransport_eq (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosSemidef) :
    responseTransport A β c S = SupportedSpin.transport A β c S := by
  unfold responseTransport
  dsimp only
  rw [jointReducedSourcePair_snd_coe A β (c, S) hc hS]
  rfl

/-- The exact scalar split uses half the source curvature for each payment. -/
theorem sourceAcceleration_split (A : ι → Matrix n n ℂ)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ → ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosSemidef)
    (K : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    2 * tracePairing K X + sourceAcceleration A ((1 : ℝ) / 2 ^ k) c
        (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S X =
      direct A ((1 : ℝ) / 2 ^ k) c Z S +
      2 * scalarForce A ((1 : ℝ) / 2 ^ k) (fun i => deriv (fun t => c t i) 0) Z K S X +
      2 * (∑ i, deriv (fun t => c t i) 0 * SupportedScalarMetric.residual A ((1 : ℝ) / 2 ^ k) Z S X i) -
      SupportedSourceMetric.curvature A ((1 : ℝ) / 2 ^ k) (c 0) Z S X := by
  rw [SupportedSourceMetric.curvature_eq_probe A (c 0) Z hZ k hk S X hS]
  simp only [sourceAcceleration, direct, scalarForce, probeValue,
    SupportedScalarMetric.residual_eq, Finset.sum_add_distrib]
  have hm : (∑ i, 2 * deriv (fun t => c t i) 0 *
      fderiv ℝ (SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i)
        (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ)) S X) =
      2 * (∑ i, deriv (fun t => c t i) 0 *
        (SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i) (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S /
          realTrace (spinAtom (A i) * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))) *
        realTrace (spinAtom (A i) * (X : Matrix (n ⊕ n) (n ⊕ n) ℂ))) +
      2 * (∑ i, deriv (fun t => c t i) 0 *
        (fderiv ℝ (SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i)
          (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ)) S X -
          (SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i) (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S /
            realTrace (spinAtom (A i) * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))) *
            realTrace (spinAtom (A i) * (X : Matrix (n ⊕ n) (n ⊕ n) ℂ)))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hm]
  ring

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
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
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
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    0 ≤ -fderiv ℝ (fderiv ℝ (tsallisPotential θ)) S X X := by
  by_cases hX : X = 0
  · simp [hX]
  · exact neg_nonneg.mpr (OptimizerResponse.tsallis_hessian_neg θ hθ S X hS hX).le

/-- Both actual source estimates are discharged before the full density response is bounded. -/
theorem paid_quadratic_le (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (c : ℝ → ι → ℝ) (hc : ∀ i, 0 < c 0 i)
    (K : Matrix (n ⊕ n) (n ⊕ n) ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    let β := (1 : ℝ) / 2 ^ k
    let Z := SupportedSpin.transport A β (c 0) S
    let P := SupportedSourceMetric.balanced A β (c 0) S
    let hP := SupportedSourceMetric.balanced_posDef A hA (c 0) hc k hk S hS
    let W := frameMismatch A β (c 0) (fun i => deriv (fun t => c t i) 0) Z S X
    (direct A β c Z S +
        2 * scalarForce A β (fun i => deriv (fun t => c t i) 0) Z K S X +
        2 * (∑ i, deriv (fun t => c t i) 0 * SupportedScalarMetric.residual A β Z S X i) -
        SupportedSourceMetric.curvature A β (c 0) Z S X +
        fderiv ℝ (fderiv ℝ (tsallisPotential θ)) S X X -
        SylvesterMetric.energy P hP (W - SupportedSourceMetric.defect A β (c 0) Z S X)) / 2 ≤
      direct A β c Z S / 2 + (1 - β) / β * budget A β c Z S +
      scalarForce A β (fun i => deriv (fun t => c t i) 0) Z K S X -
      β / 2 * SylvesterMetric.energy P hP W := by
  let β := (1 : ℝ) / 2 ^ k
  let Z := SupportedSpin.transport A β (c 0) S
  have hZ : Z.PosDef := SupportedSpin.transport_posDef A hA hc hS k hk
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ1 : β < 1 := by
    dsimp [β]
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hmetric := SupportedSourceMetric.actual_energy_le A hA hne (c 0) hc k hk S X hS
  have hscalar := SupportedScalarMetric.scalar_absorption A hA hne (c 0) hc
    (fun i => deriv (fun t => c t i) 0) Z hZ.posSemidef k hk S X hS
  have hW := SupportedFrameBridge.frame_mismatch_isHermitian A β (c 0)
    (fun i => deriv (fun t => c t i) 0) Z S X hS.posSemidef
  have hD := SupportedSourceMetric.defect_isHermitian A hA hne (c 0) Z k hk S X hS
  have hr := root_cost_nonneg θ hθ S X hS
  have h := ResponseReduction.source_payments
    (SupportedSourceMetric.balanced A β (c 0) S)
    (SupportedSourceMetric.balanced_posDef A hA (c 0) hc k hk S hS)
    hW hD (direct := direct A β c Z S)
    (force := scalarForce A β (fun i => deriv (fun t => c t i) 0) Z K S X)
    hβ hβ1 hmetric hscalar hr
  simpa only [sub_neg_eq_add] using h

end HigherRankKS.PointwiseResponse
