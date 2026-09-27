import MatrixSpencer.DyadicOptimizerStationarity

/-! The actual dyadic optimizer is a local inverse of its proved gradient chart.
This identifies its derivative with the actual trace-constrained Hessian inverse. -/
open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance dyadicResponseCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicResponseSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicResponseFinite : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
local instance dyadicResponseTangentGroup : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance dyadicResponseTangentSpace : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance dyadicResponseTangentFinite : FiniteDimensional ℝ (densityTangent (n := n)) := inferInstance
local instance dyadicResponseTangentComplete : CompleteSpace (densityTangent (n := n)) := FiniteDimensional.complete ℝ _
local instance dyadicResponseDualGroup : NormedAddCommGroup (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
local instance dyadicResponseDualSpace : NormedSpace ℝ (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance

def dyadicDensityGradientLocalInverse (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    (densityTangent (n := n) →L[ℝ] ℝ) → densityTangent (n := n) := by
  let f := dyadicDensityGradientChart (H : Matrix n n ℂ) B m θ S
  let e := dyadicDensityTangentHessianEquiv (H : Matrix n n ℂ) B m hm θ hθ S hS
  have hf : HasStrictFDerivAt f e.toContinuousLinearMap 0 :=
    hasStrictFDerivAt_dyadicDensityGradientChart (H : Matrix n n ℂ) B m hm θ hθ S hS
  exact hf.localInverse f e 0

def dyadicDensityResponseBranch (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef)
    (K : selfAdjoint (Matrix n n ℂ)) : selfAdjoint (Matrix n n ℂ) :=
  densityChart S (dyadicDensityGradientLocalInverse (H : Matrix n n ℂ) B m hm θ hθ S hS
    (densityCenterFunctional (K - H)))

def dyadicDensityResponseDerivative (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  (densityTangent (n := n)).subtypeL.comp
    ((dyadicDensityTangentHessianEquiv (H : Matrix n n ℂ) B m hm θ hθ S hS).symm.toContinuousLinearMap.comp
      densityCenterFunctional)

theorem hasStrictFDerivAt_dyadicDensityResponseBranch (H : selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef)
    (hstat : densityTangentRestriction (fderiv ℝ (hermitianDyadicDensityObjective (H : Matrix n n ℂ) B m θ) S) = 0) :
    HasStrictFDerivAt (dyadicDensityResponseBranch H B m hm θ hθ S hS)
      (dyadicDensityResponseDerivative (H : Matrix n n ℂ) B m hm θ hθ S hS) H := by
  have hf := hasStrictFDerivAt_dyadicDensityGradientChart (H : Matrix n n ℂ) B m hm θ hθ S hS
  have hf0 : dyadicDensityGradientChart (H : Matrix n n ℂ) B m θ S 0 = 0 := by
    simp only [dyadicDensityGradientChart, densityChart_zero, hstat, neg_zero]
  have hi := hf.to_localInverse
  rw [hf0] at hi
  have ht : HasStrictFDerivAt (fun K : selfAdjoint (Matrix n n ℂ) =>
      densityCenterFunctional (K - H)) densityCenterFunctional H := by
    simpa only [sub_zero, ContinuousLinearMap.comp_id] using
      (densityCenterFunctional (n := n)).hasStrictFDerivAt.comp H
        ((hasStrictFDerivAt_id H).sub (hasStrictFDerivAt_const (𝕜 := ℝ) H H))
  have hi' : HasStrictFDerivAt (hf.localInverse _ _ 0)
      (dyadicDensityTangentHessianEquiv (H : Matrix n n ℂ) B m hm θ hθ S hS).symm.toContinuousLinearMap
      (densityCenterFunctional (H - H)) := by simpa using hi
  have hbase : hf.localInverse _ _ 0 (densityCenterFunctional (H - H)) = 0 := by
    simpa only [sub_self, map_zero, hf0] using hf.localInverse_apply_image
  have hc : HasStrictFDerivAt (densityChart S) (densityTangent (n := n)).subtypeL
      (hf.localInverse _ _ 0 (densityCenterFunctional (H - H))) := by
    rw [hbase]
    exact hasStrictFDerivAt_densityChart S 0
  exact hc.comp H (hi'.comp H ht)

theorem eventually_dyadicDensityOptimizer_eq_responseBranch [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)

    (hstat : densityTangentRestriction (fderiv ℝ (hermitianDyadicDensityObjective (H : Matrix n n ℂ) B m θ) S) = 0) :
    ∀ᶠ K : selfAdjoint (Matrix n n ℂ) in 𝓝 H,
      hermitianDyadicDensityOptimizer (K : Matrix n n ℂ) B m θ = dyadicDensityResponseBranch H B m hm θ hθ S hS K := by
  have hf := hasStrictFDerivAt_dyadicDensityGradientChart (H : Matrix n n ℂ) B m hm θ hθ S hS
  have hf0 : dyadicDensityGradientChart (H : Matrix n n ℂ) B m θ S 0 = 0 := by
    simp only [dyadicDensityGradientChart, densityChart_zero, hstat, neg_zero]
  let target := fun K : selfAdjoint (Matrix n n ℂ) => densityCenterFunctional (K - H)
  have htarget : Tendsto target (𝓝 H) (𝓝 (dyadicDensityGradientChart (H : Matrix n n ℂ) B m θ S 0)) := by
    rw [hf0]
    have hc := (densityCenterFunctional (n := n)).continuous.continuousAt.comp
      (continuousAt_id.sub continuousAt_const : ContinuousAt (fun K => K - H) H)
    simpa only [ContinuousAt, Function.comp_apply, id_eq, sub_self, map_zero, target] using hc
  let inv := hf.localInverse (dyadicDensityGradientChart (H : Matrix n n ℂ) B m θ S)
    (dyadicDensityTangentHessianEquiv (H : Matrix n n ℂ) B m hm θ hθ S hS) 0
  have hinv : Tendsto (fun K => inv (target K)) (𝓝 H) (𝓝 0) := hf.localInverse_tendsto.comp htarget
  have hchart : Tendsto (fun K => densityChart S (inv (target K))) (𝓝 H) (𝓝 S) := by
    have hc := (hasStrictFDerivAt_densityChart S 0).continuousAt.tendsto.comp hinv
    simpa only [densityChart_zero] using hc
  filter_upwards [hchart.eventually (eventually_posDef_of_posDef S hS),
    htarget.eventually hf.eventually_right_inverse] with K hK heq
  change hermitianDyadicDensityOptimizer (K : Matrix n n ℂ) B m θ = densityChart S (inv (target K))
  apply dyadicDensity_stationary_eq_optimizer K B m hm θ hθ _ hK ((densityChart_trace S _).trans ht)
  rw [dyadicDensity_stationarity_center_shift H K B m θ _ hK ]
  change densityTangentRestriction
      (fderiv ℝ (hermitianDyadicDensityObjective (H : Matrix n n ℂ) B m θ) (densityChart S (inv (target K)))) + target K = 0
  change -densityTangentRestriction
      (fderiv ℝ (hermitianDyadicDensityObjective (H : Matrix n n ℂ) B m θ) (densityChart S (inv (target K)))) = target K at heq
  have hz := congrArg Neg.neg heq
  simp only [neg_neg] at hz
  exact add_eq_zero_iff_eq_neg.mpr hz

/-- The actual optimizer derivative is the inverse constrained Hessian, for arbitrary sources. -/
theorem hasStrictFDerivAt_hermitianDyadicDensityOptimizer [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    HasStrictFDerivAt (fun K : selfAdjoint (Matrix n n ℂ) => hermitianDyadicDensityOptimizer (K : Matrix n n ℂ) B m θ)
      (dyadicDensityResponseDerivative (H : Matrix n n ℂ) B m hm θ hθ (hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) B m θ)
        (hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) B m hm θ hθ)
) H := by
  have hs := dyadicDensityOptimizer_stationary (H : Matrix n n ℂ) B m hm θ hθ
  have heq := eventually_dyadicDensityOptimizer_eq_responseBranch H B m hm θ hθ
    (hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) B m θ) (hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) B m hm θ hθ)
    (hermitianDyadicDensityOptimizer_trace (H : Matrix n n ℂ) B m θ)
     hs
  exact (hasStrictFDerivAt_dyadicDensityResponseBranch H B m hm θ hθ _
    (hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) B m hm θ hθ)
           hs).congr_of_eventuallyEq (heq.mono fun _ h => h.symm)

theorem contDiffAt_dyadicDensityResponseBranch (H : selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef)
    (hstat : densityTangentRestriction (fderiv ℝ (hermitianDyadicDensityObjective (H : Matrix n n ℂ) B m θ) S) = 0) :
    ContDiffAt ℝ ∞ (dyadicDensityResponseBranch H B m hm θ hθ S hS) H := by
  have hf := hasStrictFDerivAt_dyadicDensityGradientChart (H : Matrix n n ℂ) B m hm θ hθ S hS
  have hsmooth := contDiffAt_dyadicDensityGradientChart (H : Matrix n n ℂ) B m θ S hS
  have hi : ContDiffAt ℝ ∞ (hf.localInverse _ _ 0) (dyadicDensityGradientChart (H : Matrix n n ℂ) B m θ S 0) :=
    hsmooth.to_localInverse hf.hasFDerivAt (by simp)
  have hf0 : dyadicDensityGradientChart (H : Matrix n n ℂ) B m θ S 0 = 0 := by
    simp only [dyadicDensityGradientChart, densityChart_zero, hstat, neg_zero]
  have hi' : ContDiffAt ℝ ∞ (hf.localInverse _ _ 0) (densityCenterFunctional (H - H)) := by
    simpa only [sub_self, map_zero, hf0] using hi
  exact contDiffAt_const.add ((densityTangent (n := n)).subtypeL.contDiff.contDiffAt.comp H
    (hi'.comp H ((densityCenterFunctional (n := n)).contDiff.contDiffAt.comp H
      (contDiffAt_id.sub contDiffAt_const))))

/-- The actual optimizer is smooth at every Hermitian center, including singular-source cases. -/
theorem contDiffAt_hermitianDyadicDensityOptimizer [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    ContDiffAt ℝ ∞ (fun K : selfAdjoint (Matrix n n ℂ) => hermitianDyadicDensityOptimizer (K : Matrix n n ℂ) B m θ) H := by
  have hs := dyadicDensityOptimizer_stationary (H : Matrix n n ℂ) B m hm θ hθ
  have heq := eventually_dyadicDensityOptimizer_eq_responseBranch H B m hm θ hθ
    (hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) B m θ) (hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) B m hm θ hθ)
    (hermitianDyadicDensityOptimizer_trace (H : Matrix n n ℂ) B m θ)
       hs
  exact (contDiffAt_dyadicDensityResponseBranch H B m hm θ hθ _
    (hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) B m hm θ hθ)
       hs).congr_of_eventuallyEq heq


end
end MatrixSpencer
