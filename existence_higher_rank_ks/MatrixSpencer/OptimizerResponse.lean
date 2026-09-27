import MatrixSpencer.DensityHessian
import MatrixSpencer.DensityFaithfulness
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap

/-!
# Response of the actual maximizing density

The trace-one chart and stationarity below refer to the attained global maximum.
All source-faithfulness assumptions are explicit local positive-definiteness facts.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance optimizerResponseCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance optimizerResponseNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance optimizerResponseFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
local instance optimizerResponseTangentGroup : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance optimizerResponseTangentSpace : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance optimizerResponseTangentFinite : FiniteDimensional ℝ (densityTangent (n := n)) := inferInstance
local instance optimizerResponseTangentComplete : CompleteSpace (densityTangent (n := n)) :=
  FiniteDimensional.complete ℝ _
local instance optimizerResponseDualGroup : NormedAddCommGroup (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
local instance optimizerResponseDualSpace : NormedSpace ℝ (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance

/-- Translation from the trace-zero tangent to the trace-one affine hyperplane. -/
def densityChart (S : selfAdjoint (Matrix n n ℂ)) (X : densityTangent (n := n)) :
    selfAdjoint (Matrix n n ℂ) := S + X

@[simp] theorem densityChart_zero (S : selfAdjoint (Matrix n n ℂ)) : densityChart S 0 = S := add_zero S

theorem hasStrictFDerivAt_densityChart (S : selfAdjoint (Matrix n n ℂ))
    (X : densityTangent (n := n)) :
    HasStrictFDerivAt (densityChart S) (densityTangent (n := n)).subtypeL X := by
  simpa only [zero_add] using
    (hasStrictFDerivAt_const (𝕜 := ℝ) S X).add (densityTangent (n := n)).subtypeL.hasStrictFDerivAt

theorem densityChart_trace (S : selfAdjoint (Matrix n n ℂ)) (X : densityTangent (n := n)) :
    realTrace (densityChart S X : Matrix n n ℂ) = realTrace (S : Matrix n n ℂ) := by
  change realTrace ((S : Matrix n n ℂ) + ((X : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) = _
  rw [realTrace_add, (mem_densityTangent_iff _).mp X.property, add_zero]

theorem eventually_densityChart_mem (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1) :
    ∀ᶠ X : densityTangent (n := n) in 𝓝 0, (densityChart S X : Matrix n n ℂ) ∈ densitySet := by
  have hc := (hasStrictFDerivAt_densityChart S 0).continuousAt
  have hp : ∀ᶠ X in 𝓝 (0 : densityTangent (n := n)),
      (densityChart S X : Matrix n n ℂ).PosDef :=
    hc.eventually (by simpa using eventually_posDef_of_posDef S hS)
  filter_upwards [hp] with X hX
  exact ⟨hX.posSemidef, (densityChart_trace S X).trans ht⟩

def densityTangentRestriction :
    (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) →L[ℝ] (densityTangent (n := n) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (densityTangent (n := n))
    (selfAdjoint (Matrix n n ℂ)) ℝ).flip (densityTangent (n := n)).subtypeL

/-- Stationarity of any actual attained faithful maximizer, proved on a feasible local chart. -/
theorem density_maximizer_stationary (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef)
    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S) :
    densityTangentRestriction (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S) = 0 := by
  have hlocal : IsLocalMax ((hermitianDensityObjective (H : Matrix n n ℂ) B θ) ∘ densityChart S) 0 := by
    filter_upwards [eventually_densityChart_mem S hS ht] with X hX
    simpa only [Function.comp_apply, densityChart_zero, hermitianDensityObjective] using
      hmax (densityChart S X) hX
  have hd := ((contDiffAt_hermitianDensityObjective (H : Matrix n n ℂ) B θ S hS hM).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  have hd' : HasFDerivAt (hermitianDensityObjective (H : Matrix n n ℂ) B θ)
      (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S) (densityChart S 0) := by simpa using hd
  have hc := hd'.comp 0 (hasStrictFDerivAt_densityChart S 0).hasFDerivAt
  exact hlocal.hasFDerivAt_eq_zero hc

/-- The canonical optimizer as a Hermitian matrix, without changing its definition. -/
def hermitianDensityOptimizer [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) : selfAdjoint (Matrix n n ℂ) :=
  ⟨densityOptimizer (H : Matrix n n ℂ) B θ, (densityOptimizer_mem (H : Matrix n n ℂ) B θ).1.isHermitian⟩

theorem hermitianDensityOptimizer_posDef [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    (hermitianDensityOptimizer H B θ : Matrix n n ℂ).PosDef :=
  densityOptimizer_posDef H B hθ

theorem hermitianDensityOptimizer_trace [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) :
    realTrace (hermitianDensityOptimizer H B θ : Matrix n n ℂ) = 1 :=
  (densityOptimizer_mem H B θ).2

theorem hermitianDensityOptimizer_source_posDef [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ)
    (hM : (krausChannel B (densityOptimizer H B θ)).PosDef) :
    (krausChannel B (hermitianDensityOptimizer H B θ : Matrix n n ℂ)).PosDef := hM

theorem densityOptimizer_stationary [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ)
    (hM : (krausChannel B (densityOptimizer (H : Matrix n n ℂ) B θ)).PosDef) :
    densityTangentRestriction
      (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)) = 0 :=
  density_maximizer_stationary H B θ _ (densityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
    (densityOptimizer_mem (H : Matrix n n ℂ) B θ).2 hM (densityOptimizer_isMaxOn (H : Matrix n n ℂ) B θ)

section ConcaveSupport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A derivative of a concave function supports every point of its convex domain. -/
theorem concaveOn_le_tangent {f : E → ℝ} {K : Set E} (hf : ConcaveOn ℝ K f)
    {S T : E} (hS : S ∈ K) (hT : T ∈ K) {L : E →L[ℝ] ℝ}
    (hd : HasFDerivAt f L S) : f T ≤ f S + L (T - S) := by
  let g : ℝ →ᵃ[ℝ] E := AffineMap.lineMap S T
  have hc : ConcaveOn ℝ (g ⁻¹' K) (f ∘ g) := hf.comp_affineMap g
  have hd' : HasFDerivAt f L (g 0) := by simpa [g] using hd
  have hg : HasDerivAt (f ∘ g) (L (T - S)) 0 :=
    hd'.comp_hasDerivAt 0 AffineMap.hasDerivAt_lineMap
  have h := hc.slope_le_of_hasDerivAt (x := 0) (y := 1)
    (by simpa [g] using hS) (by simpa [g] using hT) zero_lt_one hg
  simp only [slope_def_field, Function.comp_apply, g, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one] at h
  linarith
end ConcaveSupport

/-- A faithful stationary density is the global maximum, including comparison with singular densities. -/
theorem density_stationary_isMaxOn (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {θ : ℝ} (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef)
    (hstat : densityTangentRestriction
      (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S) = 0) :
    ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S := by
  intro T hT
  let T' : selfAdjoint (Matrix n n ℂ) := ⟨T, hT.1.isHermitian⟩
  have hc := (strictConcaveOn_densityObjective H B hθ).concaveOn.comp_linearMap
    (hermitianInclusion (n := n)).toLinearMap
  have hd := ((contDiffAt_hermitianDensityObjective (H : Matrix n n ℂ) B θ S hS hM).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  have hbound := concaveOn_le_tangent hc (S := S) (T := T') ⟨hS.posSemidef, ht⟩ hT hd
  have hzero : realTrace ((T' - S : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) = 0 := by
    change realTrace (T - (S : Matrix n n ℂ)) = 0
    rw [realTrace_sub, hT.2, ht, sub_self]
  let X : densityTangent (n := n) := ⟨T' - S, (mem_densityTangent_iff _).mpr hzero⟩
  have hz := DFunLike.congr_fun hstat X
  change fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S (T' - S) = 0 at hz
  rw [hz, add_zero] at hbound
  exact hbound

/-- Negative stationarity in the trace-one chart; its derivative is the constrained Hessian. -/
def densityGradientChart (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (X : densityTangent (n := n)) :
    densityTangent (n := n) →L[ℝ] ℝ :=
  -densityTangentRestriction (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) (densityChart S X))

def densityCenterFunctional : selfAdjoint (Matrix n n ℂ) →L[ℝ]
    (densityTangent (n := n) →L[ℝ] ℝ) :=
  densityTangentRestriction.comp (tracePairing.comp hermitianInclusion)

theorem density_stationarity_center_shift (H K : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    densityTangentRestriction (fderiv ℝ (hermitianDensityObjective (K : Matrix n n ℂ) B θ) S) =
      densityTangentRestriction (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S) +
      densityTangentRestriction (tracePairing (K - H)) := by
  rw [fderiv_hermitianDensityObjective_eq H B θ S hS hM,
    fderiv_hermitianDensityObjective_eq K B θ S hS hM]
  simp only [map_add, map_sub]
  abel

theorem hasStrictFDerivAt_densityGradientChart (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    HasStrictFDerivAt (densityGradientChart (H : Matrix n n ℂ) B θ S)
      (densityTangentHessianEquiv (H : Matrix n n ℂ) B θ hθ S hS hM).toContinuousLinearMap 0 := by
  have hd := hasStrictFDerivAt_fderiv_hermitianDensityObjective (H : Matrix n n ℂ) B θ S hS hM
  rw [← hd.hasFDerivAt.fderiv] at hd
  have hd' : HasStrictFDerivAt (fun A => fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) A)
      (fderiv ℝ (fun A => fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) A) S)
      (densityChart S 0) := by simpa using hd
  have hc := ((densityTangentRestriction (n := n)).hasStrictFDerivAt.comp 0
    (hd'.comp 0 (hasStrictFDerivAt_densityChart S 0))).neg
  convert hc using 1

theorem contDiffAt_densityGradientChart (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    ContDiffAt ℝ ∞ (densityGradientChart (H : Matrix n n ℂ) B θ S) 0 := by
  have hd : ContDiffAt ℝ ∞ (fun A => fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) A) S :=
    (contDiffAt_hermitianDensityObjective (H : Matrix n n ℂ) B θ S hS hM).fderiv_right (by simp)
  have hd' : ContDiffAt ℝ ∞ (fun A => fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) A)
      (densityChart S 0) := by simpa using hd
  exact ((densityTangentRestriction (n := n)).contDiff.contDiffAt.comp 0
    (hd'.comp 0 (contDiffAt_const.add (densityTangent (n := n)).subtypeL.contDiff.contDiffAt))).neg

/-- A stationary positive density is the canonical chosen optimizer, by proved uniqueness. -/
theorem density_stationary_eq_optimizer [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef)
    (hstat : densityTangentRestriction (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S) = 0) :
    hermitianDensityOptimizer (H : Matrix n n ℂ) B θ = S := by
  apply Subtype.ext
  exact (strictConcaveOn_densityObjective H B hθ).eq_of_isMaxOn
    (densityOptimizer_isMaxOn (H : Matrix n n ℂ) B θ) (density_stationary_isMaxOn H B hθ S hS ht hM hstat)
    (densityOptimizer_mem (H : Matrix n n ℂ) B θ) ⟨hS.posSemidef, ht⟩

def densityGradientLocalInverse (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    (densityTangent (n := n) →L[ℝ] ℝ) → densityTangent (n := n) := by
  let f := densityGradientChart (H : Matrix n n ℂ) B θ S
  let e := densityTangentHessianEquiv (H : Matrix n n ℂ) B θ hθ S hS hM
  have hf : HasStrictFDerivAt f e.toContinuousLinearMap 0 :=
    hasStrictFDerivAt_densityGradientChart (H : Matrix n n ℂ) B θ hθ S hS hM
  exact hf.localInverse f e 0

/-- The actual local inverse of the constrained-gradient map, applied to the center perturbation. -/
def densityResponseBranch (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef)
    (K : selfAdjoint (Matrix n n ℂ)) : selfAdjoint (Matrix n n ℂ) :=
  densityChart S (densityGradientLocalInverse (H : Matrix n n ℂ) B θ hθ S hS hM
    (densityCenterFunctional (K - H)))

def densityResponseDerivative (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  (densityTangent (n := n)).subtypeL.comp
    ((densityTangentHessianEquiv (H : Matrix n n ℂ) B θ hθ S hS hM).symm.toContinuousLinearMap.comp
      densityCenterFunctional)

theorem hasStrictFDerivAt_densityResponseBranch (H : selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef)
    (hstat : densityTangentRestriction (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S) = 0) :
    HasStrictFDerivAt (densityResponseBranch H B θ hθ S hS hM)
      (densityResponseDerivative (H : Matrix n n ℂ) B θ hθ S hS hM) H := by
  have hf := hasStrictFDerivAt_densityGradientChart (H : Matrix n n ℂ) B θ hθ S hS hM
  have hf0 : densityGradientChart (H : Matrix n n ℂ) B θ S 0 = 0 := by
    simp only [densityGradientChart, densityChart_zero, hstat, neg_zero]
  have hi := hf.to_localInverse
  rw [hf0] at hi
  have ht : HasStrictFDerivAt (fun K : selfAdjoint (Matrix n n ℂ) =>
      densityCenterFunctional (K - H)) densityCenterFunctional H := by
    simpa only [sub_zero, ContinuousLinearMap.comp_id] using
      (densityCenterFunctional (n := n)).hasStrictFDerivAt.comp H
        ((hasStrictFDerivAt_id H).sub (hasStrictFDerivAt_const (𝕜 := ℝ) H H))
  have hi' : HasStrictFDerivAt (hf.localInverse _ _ 0)
      (densityTangentHessianEquiv (H : Matrix n n ℂ) B θ hθ S hS hM).symm.toContinuousLinearMap
      (densityCenterFunctional (H - H)) := by simpa using hi
  have hbase : hf.localInverse _ _ 0 (densityCenterFunctional (H - H)) = 0 := by
    simpa only [sub_self, map_zero, hf0] using hf.localInverse_apply_image
  have hc : HasStrictFDerivAt (densityChart S) (densityTangent (n := n)).subtypeL
      (hf.localInverse _ _ 0 (densityCenterFunctional (H - H))) := by
    rw [hbase]
    exact hasStrictFDerivAt_densityChart S 0
  exact hc.comp H (hi'.comp H ht)

/-- The IFT branch agrees locally with the actual globally chosen density optimizer. -/
theorem eventually_densityOptimizer_eq_responseBranch [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef)
    (hstat : densityTangentRestriction (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S) = 0) :
    ∀ᶠ K : selfAdjoint (Matrix n n ℂ) in 𝓝 H,
      hermitianDensityOptimizer (K : Matrix n n ℂ) B θ = densityResponseBranch H B θ hθ S hS hM K := by
  have hf := hasStrictFDerivAt_densityGradientChart (H : Matrix n n ℂ) B θ hθ S hS hM
  have hf0 : densityGradientChart (H : Matrix n n ℂ) B θ S 0 = 0 := by
    simp only [densityGradientChart, densityChart_zero, hstat, neg_zero]
  let target := fun K : selfAdjoint (Matrix n n ℂ) => densityCenterFunctional (K - H)
  have htarget : Tendsto target (𝓝 H) (𝓝 (densityGradientChart (H : Matrix n n ℂ) B θ S 0)) := by
    rw [hf0]
    have hc := (densityCenterFunctional (n := n)).continuous.continuousAt.comp
      (continuousAt_id.sub continuousAt_const : ContinuousAt (fun K => K - H) H)
    simpa only [ContinuousAt, Function.comp_apply, id_eq, sub_self, map_zero, target] using hc
  let inv := hf.localInverse (densityGradientChart (H : Matrix n n ℂ) B θ S)
    (densityTangentHessianEquiv (H : Matrix n n ℂ) B θ hθ S hS hM) 0
  have hinv : Tendsto (fun K => inv (target K)) (𝓝 H) (𝓝 0) := hf.localInverse_tendsto.comp htarget
  have hchart : Tendsto (fun K => densityChart S (inv (target K))) (𝓝 H) (𝓝 S) := by
    have hc := (hasStrictFDerivAt_densityChart S 0).continuousAt.tendsto.comp hinv
    simpa only [densityChart_zero] using hc
  filter_upwards [hchart.eventually (eventually_posDef_of_posDef S hS),
    hchart.eventually (eventually_posDef_krausSource B S hM),
    htarget.eventually hf.eventually_right_inverse] with K hK hMK heq
  change hermitianDensityOptimizer (K : Matrix n n ℂ) B θ = densityChart S (inv (target K))
  apply density_stationary_eq_optimizer K B hθ _ hK ((densityChart_trace S _).trans ht) hMK
  rw [density_stationarity_center_shift H K B θ _ hK hMK]
  change densityTangentRestriction
      (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) (densityChart S (inv (target K)))) + target K = 0
  change -densityTangentRestriction
      (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) (densityChart S (inv (target K)))) = target K at heq
  have hz := congrArg Neg.neg heq
  simp only [neg_neg] at hz
  exact add_eq_zero_iff_eq_neg.mpr hz

/-- Actual optimizer response, with only source positive-definiteness as a local hypothesis. -/
theorem hasStrictFDerivAt_hermitianDensityOptimizer [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ)
    (hM : (krausChannel B (densityOptimizer (H : Matrix n n ℂ) B θ)).PosDef) :
    HasStrictFDerivAt (fun K : selfAdjoint (Matrix n n ℂ) => hermitianDensityOptimizer (K : Matrix n n ℂ) B θ)
      (densityResponseDerivative (H : Matrix n n ℂ) B θ hθ (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)
        (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
          (hermitianDensityOptimizer_source_posDef (H : Matrix n n ℂ) B θ hM)) H := by
  have hs := densityOptimizer_stationary (H : Matrix n n ℂ) B hθ hM
  have heq := eventually_densityOptimizer_eq_responseBranch H B θ hθ
    (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ) (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
    (hermitianDensityOptimizer_trace (H : Matrix n n ℂ) B θ)
    (hermitianDensityOptimizer_source_posDef (H : Matrix n n ℂ) B θ hM) hs
  exact (hasStrictFDerivAt_densityResponseBranch H B θ hθ _
    (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
          (hermitianDensityOptimizer_source_posDef (H : Matrix n n ℂ) B θ hM) hs).congr_of_eventuallyEq (heq.mono fun _ h => h.symm)

theorem contDiffAt_densityResponseBranch (H : selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef)
    (hstat : densityTangentRestriction (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S) = 0) :
    ContDiffAt ℝ ∞ (densityResponseBranch H B θ hθ S hS hM) H := by
  have hf := hasStrictFDerivAt_densityGradientChart (H : Matrix n n ℂ) B θ hθ S hS hM
  have hsmooth := contDiffAt_densityGradientChart (H : Matrix n n ℂ) B θ S hS hM
  have hi : ContDiffAt ℝ ∞ (hf.localInverse _ _ 0) (densityGradientChart (H : Matrix n n ℂ) B θ S 0) :=
    hsmooth.to_localInverse hf.hasFDerivAt (by simp)
  have hf0 : densityGradientChart (H : Matrix n n ℂ) B θ S 0 = 0 := by
    simp only [densityGradientChart, densityChart_zero, hstat, neg_zero]
  have hi' : ContDiffAt ℝ ∞ (hf.localInverse _ _ 0) (densityCenterFunctional (H - H)) := by
    simpa only [sub_self, map_zero, hf0] using hi
  exact contDiffAt_const.add ((densityTangent (n := n)).subtypeL.contDiff.contDiffAt.comp H
    (hi'.comp H ((densityCenterFunctional (n := n)).contDiff.contDiffAt.comp H
      (contDiffAt_id.sub contDiffAt_const))))

/-- Smoothness of the actual optimizer follows from the proved branch identification. -/
theorem contDiffAt_hermitianDensityOptimizer [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ)
    (hM : (krausChannel B (densityOptimizer (H : Matrix n n ℂ) B θ)).PosDef) :
    ContDiffAt ℝ ∞ (fun K : selfAdjoint (Matrix n n ℂ) => hermitianDensityOptimizer (K : Matrix n n ℂ) B θ) H := by
  have hs := densityOptimizer_stationary (H : Matrix n n ℂ) B hθ hM
  have heq := eventually_densityOptimizer_eq_responseBranch H B θ hθ
    (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ) (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
    (hermitianDensityOptimizer_trace (H : Matrix n n ℂ) B θ)
      (hermitianDensityOptimizer_source_posDef (H : Matrix n n ℂ) B θ hM) hs
  exact (contDiffAt_densityResponseBranch H B θ hθ _
    (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
      (hermitianDensityOptimizer_source_posDef (H : Matrix n n ℂ) B θ hM) hs).congr_of_eventuallyEq heq

/-- The actual potential, with its center restricted to the real Hermitian space. -/
def hermitianDensityPotential (B : ι → Matrix n n ℂ) (θ : ℝ)
    (H : selfAdjoint (Matrix n n ℂ)) : ℝ := densityPotential H B θ

theorem hermitianDensityPotential_eq_objective [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) (θ : ℝ) :
    hermitianDensityPotential B θ H =
      hermitianDensityObjective (H : Matrix n n ℂ) B θ (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ) := by
  change densityPotential (H : Matrix n n ℂ) B θ =
    densityObjective (H : Matrix n n ℂ) B θ (densityOptimizer (H : Matrix n n ℂ) B θ)
  exact densityPotential_eq_of_maximizer (H : Matrix n n ℂ) B θ
    (S := densityOptimizer (H : Matrix n n ℂ) B θ)
    (densityOptimizer_mem (H : Matrix n n ℂ) B θ)
    (densityOptimizer_isMaxOn (H : Matrix n n ℂ) B θ)

/-- Smoothness of the genuine supremum potential, through its actual unique maximizer. -/
theorem contDiffAt_hermitianDensityPotential [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ)
    (hM : (krausChannel B (densityOptimizer (H : Matrix n n ℂ) B θ)).PosDef) :
    ContDiffAt ℝ ∞ (hermitianDensityPotential B θ) H := by
  have hs := contDiffAt_hermitianDensityOptimizer H B hθ hM
  have hm := (hermitianInclusion (n := n)).contDiff.contDiffAt.comp H hs
  have hlinear := realTraceCLM.contDiff.contDiffAt.comp H
    ((hermitianInclusion (n := n)).contDiff.contDiffAt.mul hm)
  have hf := (contDiffAt_krausSourceFidelity B (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)
    (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
      (hermitianDensityOptimizer_source_posDef (H : Matrix n n ℂ) B θ hM)).comp H hs
  have ht := (contDiffAt_tsallisPotential θ (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)
    (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)).comp H hs
  apply ((hlinear.add hf).add ht).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun K => hermitianDensityPotential_eq_objective K B θ

/-- The envelope derivative is the actual optimizer, in the real trace pairing. -/
theorem hasFDerivAt_hermitianDensityPotential [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ)
    (hM : (krausChannel B (densityOptimizer (H : Matrix n n ℂ) B θ)).PosDef) :
    HasFDerivAt (hermitianDensityPotential B θ) (tracePairing (densityOptimizer (H : Matrix n n ℂ) B θ)) H := by
  have hd := ((contDiffAt_hermitianDensityPotential H B hθ hM).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  let L := tracePairing (densityOptimizer (H : Matrix n n ℂ) B θ)
  have hmin : IsLocalMin (fun K => hermitianDensityPotential B θ K - L K) H := by
    apply Filter.Eventually.of_forall
    intro K
    have h := densityPotential_supporting_plane (H : Matrix n n ℂ) (K : Matrix n n ℂ) B θ
      (S := densityOptimizer (H : Matrix n n ℂ) B θ)
      (densityOptimizer_mem (H : Matrix n n ℂ) B θ)
      (densityOptimizer_isMaxOn (H : Matrix n n ℂ) B θ)
    rw [realTrace_mul_comm] at h
    change densityPotential H B θ + L (K - H) ≤ densityPotential K B θ at h
    rw [map_sub] at h
    change densityPotential H B θ - L H ≤ densityPotential K B θ - L K
    linarith
  have hz := hmin.hasFDerivAt_eq_zero (hd.sub L.hasFDerivAt)
  rwa [sub_eq_zero.mp hz] at hd

theorem hasStrictFDerivAt_hermitianDensityPotential [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ)
    (hM : (krausChannel B (densityOptimizer (H : Matrix n n ℂ) B θ)).PosDef) :
    HasStrictFDerivAt (hermitianDensityPotential B θ) (tracePairing (densityOptimizer (H : Matrix n n ℂ) B θ)) H :=
  (contDiffAt_hermitianDensityPotential H B hθ hM).hasStrictFDerivAt'
    (hasFDerivAt_hermitianDensityPotential H B hθ hM) (by simp)

/-- Actual second derivative of the supremum potential is the constrained inverse-Hessian response. -/
theorem hasStrictFDerivAt_fderiv_hermitianDensityPotential [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ)
    (hM : (krausChannel B (densityOptimizer (H : Matrix n n ℂ) B θ)).PosDef) :
    HasStrictFDerivAt (fun K => fderiv ℝ (hermitianDensityPotential B θ) K)
      ((tracePairing.comp hermitianInclusion).comp
        (densityResponseDerivative (H : Matrix n n ℂ) B θ hθ (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)
          (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
      (hermitianDensityOptimizer_source_posDef (H : Matrix n n ℂ) B θ hM))) H := by
  have hs := hasStrictFDerivAt_hermitianDensityOptimizer H B hθ hM
  have hd := (tracePairing.comp (hermitianInclusion (n := n))).hasStrictFDerivAt.comp H hs
  have hevent := hs.continuousAt.eventually
    (eventually_posDef_krausSource B (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ) hM)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hevent] with K hK
  exact (hasFDerivAt_hermitianDensityPotential K B hθ hK).fderiv.symm

theorem fderiv_fderiv_hermitianDensityPotential_apply [Nonempty n]
    (H X Y : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ)
    (hM : (krausChannel B (densityOptimizer (H : Matrix n n ℂ) B θ)).PosDef) :
    fderiv ℝ (fun K => fderiv ℝ (hermitianDensityPotential B θ) K) H X Y =
      realTrace ((densityResponseDerivative (H : Matrix n n ℂ) B θ hθ (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)
        (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
      (hermitianDensityOptimizer_source_posDef (H : Matrix n n ℂ) B θ hM) X : Matrix n n ℂ) * (Y : Matrix n n ℂ)) := by
  rw [(hasStrictFDerivAt_fderiv_hermitianDensityPotential H B hθ hM).hasFDerivAt.fderiv]
  rfl

/-- The response stays in the trace-zero tangent. -/
theorem densityResponseDerivative_trace (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef)
    (X : selfAdjoint (Matrix n n ℂ)) :
    realTrace (densityResponseDerivative H B θ hθ S hS hM X : Matrix n n ℂ) = 0 :=
  (mem_densityTangent_iff _).mp
    ((densityTangentHessianEquiv H B θ hθ S hS hM).symm (densityCenterFunctional X)).property

/-- Positivity of the actual inverse-Hessian response in the trace pairing. -/
theorem densityResponseDerivative_quadratic_nonneg (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef)
    (X : selfAdjoint (Matrix n n ℂ)) :
    0 ≤ realTrace ((densityResponseDerivative H B θ hθ S hS hM X : Matrix n n ℂ) *
      (X : Matrix n n ℂ)) := by
  let U := (densityTangentHessianEquiv H B θ hθ S hS hM).symm (densityCenterFunctional X)
  have hrep : densityTangentNegativeHessian H B θ S U U = densityCenterFunctional X U := by
    change densityTangentHessianEquiv H B θ hθ S hS hM U U = _
    dsimp only [U]
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [realTrace_mul_comm]
  change 0 ≤ densityCenterFunctional X U
  by_cases hU : U = 0
  · rw [hU]
    exact le_of_eq ((densityCenterFunctional X).map_zero).symm
  · rw [← hrep]
    exact (densityTangentNegativeHessian_pos H B θ hθ S hS hM U hU).le

theorem fderiv_fderiv_hermitianDensityPotential_quadratic_nonneg [Nonempty n]
    (H X : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ)
    (hM : (krausChannel B (densityOptimizer (H : Matrix n n ℂ) B θ)).PosDef) :
    0 ≤ fderiv ℝ (fun K => fderiv ℝ (hermitianDensityPotential B θ) K) H X X := by
  rw [fderiv_fderiv_hermitianDensityPotential_apply H X X B hθ hM]
  exact densityResponseDerivative_quadratic_nonneg (H : Matrix n n ℂ) B θ hθ
    (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)
    (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
    (hermitianDensityOptimizer_source_posDef (H : Matrix n n ℂ) B θ hM) X

end
end MatrixSpencer
