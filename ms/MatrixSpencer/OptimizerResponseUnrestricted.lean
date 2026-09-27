import MatrixSpencer.OptimizerResponse
import MatrixSpencer.SingularDensityCalculus

/-!
# Actual optimizer response for arbitrary Kraus sources

Compression onto the concrete Kraus source support provides the local smooth
calculus. The final optimizer and supremum-potential theorems require only a
positive Tsallis scale; source matrices may be singular or zero.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance optimizerUnrestrictedCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance optimizerUnrestrictedNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance optimizerUnrestrictedFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
local instance optimizerUnrestrictedTangentGroup : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance optimizerUnrestrictedTangentSpace : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance optimizerUnrestrictedTangentFinite : FiniteDimensional ℝ (densityTangent (n := n)) := inferInstance
local instance optimizerUnrestrictedTangentComplete : CompleteSpace (densityTangent (n := n)) :=
  FiniteDimensional.complete ℝ _
local instance optimizerUnrestrictedDualGroup : NormedAddCommGroup (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
local instance optimizerUnrestrictedDualSpace : NormedSpace ℝ (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance

theorem density_maximizer_stationary_source_unrestricted (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)

    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S) :
    densityTangentRestriction (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S) = 0 := by
  have hlocal : IsLocalMax ((hermitianDensityObjective (H : Matrix n n ℂ) B θ) ∘ densityChart S) 0 := by
    filter_upwards [eventually_densityChart_mem S hS ht] with X hX
    simpa only [Function.comp_apply, densityChart_zero, hermitianDensityObjective] using
      hmax (densityChart S X) hX
  have hd := ((contDiffAt_hermitianDensityObjective_source_unrestricted (H : Matrix n n ℂ) B θ S hS).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  have hd' : HasFDerivAt (hermitianDensityObjective (H : Matrix n n ℂ) B θ)
      (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S) (densityChart S 0) := by simpa using hd
  have hc := hd'.comp 0 (hasStrictFDerivAt_densityChart S 0).hasFDerivAt
  exact hlocal.hasFDerivAt_eq_zero hc

theorem densityOptimizer_stationary_source_unrestricted [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    densityTangentRestriction
      (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)) = 0 :=
  density_maximizer_stationary_source_unrestricted H B θ _ (densityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
    (densityOptimizer_mem (H : Matrix n n ℂ) B θ).2 (densityOptimizer_isMaxOn (H : Matrix n n ℂ) B θ)

theorem density_stationary_isMaxOn_source_unrestricted (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {θ : ℝ} (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1)

    (hstat : densityTangentRestriction
      (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S) = 0) :
    ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S := by
  intro T hT
  let T' : selfAdjoint (Matrix n n ℂ) := ⟨T, hT.1.isHermitian⟩
  have hc := (strictConcaveOn_densityObjective H B hθ).concaveOn.comp_linearMap
    (hermitianInclusion (n := n)).toLinearMap
  have hd := ((contDiffAt_hermitianDensityObjective_source_unrestricted (H : Matrix n n ℂ) B θ S hS).differentiableAt
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

theorem density_stationarity_center_shift_source_unrestricted (H K : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    densityTangentRestriction (fderiv ℝ (hermitianDensityObjective (K : Matrix n n ℂ) B θ) S) =
      densityTangentRestriction (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S) +
      densityTangentRestriction (tracePairing (K - H)) := by
  rw [fderiv_hermitianDensityObjective_eq_source_unrestricted H B θ S hS,
    fderiv_hermitianDensityObjective_eq_source_unrestricted K B θ S hS ]
  simp only [map_add, map_sub]
  abel

theorem hasStrictFDerivAt_densityGradientChart_source_unrestricted (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (densityGradientChart (H : Matrix n n ℂ) B θ S)
      (densityTangentHessianEquiv_source_unrestricted (H : Matrix n n ℂ) B θ hθ S hS).toContinuousLinearMap 0 := by
  have hd := hasStrictFDerivAt_fderiv_hermitianDensityObjective_source_unrestricted (H : Matrix n n ℂ) B θ S hS
  rw [← hd.hasFDerivAt.fderiv] at hd
  have hd' : HasStrictFDerivAt (fun A => fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) A)
      (fderiv ℝ (fun A => fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) A) S)
      (densityChart S 0) := by simpa using hd
  have hc := ((densityTangentRestriction (n := n)).hasStrictFDerivAt.comp 0
    (hd'.comp 0 (hasStrictFDerivAt_densityChart S 0))).neg
  convert hc using 1

theorem contDiffAt_densityGradientChart_source_unrestricted (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (densityGradientChart (H : Matrix n n ℂ) B θ S) 0 := by
  have hd : ContDiffAt ℝ ∞ (fun A => fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) A) S :=
    (contDiffAt_hermitianDensityObjective_source_unrestricted (H : Matrix n n ℂ) B θ S hS).fderiv_right (by simp)
  have hd' : ContDiffAt ℝ ∞ (fun A => fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) A)
      (densityChart S 0) := by simpa using hd
  exact ((densityTangentRestriction (n := n)).contDiff.contDiffAt.comp 0
    (hd'.comp 0 (contDiffAt_const.add (densityTangent (n := n)).subtypeL.contDiff.contDiffAt))).neg

theorem density_stationary_eq_optimizer_source_unrestricted [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1)

    (hstat : densityTangentRestriction (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S) = 0) :
    hermitianDensityOptimizer (H : Matrix n n ℂ) B θ = S := by
  apply Subtype.ext
  exact (strictConcaveOn_densityObjective H B hθ).eq_of_isMaxOn
    (densityOptimizer_isMaxOn (H : Matrix n n ℂ) B θ) (density_stationary_isMaxOn_source_unrestricted H B hθ S hS ht hstat)
    (densityOptimizer_mem (H : Matrix n n ℂ) B θ) ⟨hS.posSemidef, ht⟩

def densityGradientLocalInverse_source_unrestricted (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    (densityTangent (n := n) →L[ℝ] ℝ) → densityTangent (n := n) := by
  let f := densityGradientChart (H : Matrix n n ℂ) B θ S
  let e := densityTangentHessianEquiv_source_unrestricted (H : Matrix n n ℂ) B θ hθ S hS
  have hf : HasStrictFDerivAt f e.toContinuousLinearMap 0 :=
    hasStrictFDerivAt_densityGradientChart_source_unrestricted (H : Matrix n n ℂ) B θ hθ S hS
  exact hf.localInverse f e 0

def densityResponseBranch_source_unrestricted (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef)
    (K : selfAdjoint (Matrix n n ℂ)) : selfAdjoint (Matrix n n ℂ) :=
  densityChart S (densityGradientLocalInverse_source_unrestricted (H : Matrix n n ℂ) B θ hθ S hS
    (densityCenterFunctional (K - H)))

def densityResponseDerivative_source_unrestricted (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  (densityTangent (n := n)).subtypeL.comp
    ((densityTangentHessianEquiv_source_unrestricted (H : Matrix n n ℂ) B θ hθ S hS).symm.toContinuousLinearMap.comp
      densityCenterFunctional)

theorem hasStrictFDerivAt_densityResponseBranch_source_unrestricted (H : selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef)
    (hstat : densityTangentRestriction (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S) = 0) :
    HasStrictFDerivAt (densityResponseBranch_source_unrestricted H B θ hθ S hS)
      (densityResponseDerivative_source_unrestricted (H : Matrix n n ℂ) B θ hθ S hS) H := by
  have hf := hasStrictFDerivAt_densityGradientChart_source_unrestricted (H : Matrix n n ℂ) B θ hθ S hS
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
      (densityTangentHessianEquiv_source_unrestricted (H : Matrix n n ℂ) B θ hθ S hS).symm.toContinuousLinearMap
      (densityCenterFunctional (H - H)) := by simpa using hi
  have hbase : hf.localInverse _ _ 0 (densityCenterFunctional (H - H)) = 0 := by
    simpa only [sub_self, map_zero, hf0] using hf.localInverse_apply_image
  have hc : HasStrictFDerivAt (densityChart S) (densityTangent (n := n)).subtypeL
      (hf.localInverse _ _ 0 (densityCenterFunctional (H - H))) := by
    rw [hbase]
    exact hasStrictFDerivAt_densityChart S 0
  exact hc.comp H (hi'.comp H ht)

theorem eventually_densityOptimizer_eq_responseBranch_source_unrestricted [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)

    (hstat : densityTangentRestriction (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S) = 0) :
    ∀ᶠ K : selfAdjoint (Matrix n n ℂ) in 𝓝 H,
      hermitianDensityOptimizer (K : Matrix n n ℂ) B θ = densityResponseBranch_source_unrestricted H B θ hθ S hS K := by
  have hf := hasStrictFDerivAt_densityGradientChart_source_unrestricted (H : Matrix n n ℂ) B θ hθ S hS
  have hf0 : densityGradientChart (H : Matrix n n ℂ) B θ S 0 = 0 := by
    simp only [densityGradientChart, densityChart_zero, hstat, neg_zero]
  let target := fun K : selfAdjoint (Matrix n n ℂ) => densityCenterFunctional (K - H)
  have htarget : Tendsto target (𝓝 H) (𝓝 (densityGradientChart (H : Matrix n n ℂ) B θ S 0)) := by
    rw [hf0]
    have hc := (densityCenterFunctional (n := n)).continuous.continuousAt.comp
      (continuousAt_id.sub continuousAt_const : ContinuousAt (fun K => K - H) H)
    simpa only [ContinuousAt, Function.comp_apply, id_eq, sub_self, map_zero, target] using hc
  let inv := hf.localInverse (densityGradientChart (H : Matrix n n ℂ) B θ S)
    (densityTangentHessianEquiv_source_unrestricted (H : Matrix n n ℂ) B θ hθ S hS) 0
  have hinv : Tendsto (fun K => inv (target K)) (𝓝 H) (𝓝 0) := hf.localInverse_tendsto.comp htarget
  have hchart : Tendsto (fun K => densityChart S (inv (target K))) (𝓝 H) (𝓝 S) := by
    have hc := (hasStrictFDerivAt_densityChart S 0).continuousAt.tendsto.comp hinv
    simpa only [densityChart_zero] using hc
  filter_upwards [hchart.eventually (eventually_posDef_of_posDef S hS),
    htarget.eventually hf.eventually_right_inverse] with K hK heq
  change hermitianDensityOptimizer (K : Matrix n n ℂ) B θ = densityChart S (inv (target K))
  apply density_stationary_eq_optimizer_source_unrestricted K B hθ _ hK ((densityChart_trace S _).trans ht)
  rw [density_stationarity_center_shift_source_unrestricted H K B θ _ hK ]
  change densityTangentRestriction
      (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) (densityChart S (inv (target K)))) + target K = 0
  change -densityTangentRestriction
      (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) (densityChart S (inv (target K)))) = target K at heq
  have hz := congrArg Neg.neg heq
  simp only [neg_neg] at hz
  exact add_eq_zero_iff_eq_neg.mpr hz

/-- The actual optimizer derivative is the inverse constrained Hessian, for arbitrary sources. -/
theorem hasStrictFDerivAt_hermitianDensityOptimizer_source_unrestricted [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    HasStrictFDerivAt (fun K : selfAdjoint (Matrix n n ℂ) => hermitianDensityOptimizer (K : Matrix n n ℂ) B θ)
      (densityResponseDerivative_source_unrestricted (H : Matrix n n ℂ) B θ hθ (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)
        (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
) H := by
  have hs := densityOptimizer_stationary_source_unrestricted (H : Matrix n n ℂ) B hθ
  have heq := eventually_densityOptimizer_eq_responseBranch_source_unrestricted H B θ hθ
    (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ) (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
    (hermitianDensityOptimizer_trace (H : Matrix n n ℂ) B θ)
     hs
  exact (hasStrictFDerivAt_densityResponseBranch_source_unrestricted H B θ hθ _
    (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
           hs).congr_of_eventuallyEq (heq.mono fun _ h => h.symm)

theorem contDiffAt_densityResponseBranch_source_unrestricted (H : selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef)
    (hstat : densityTangentRestriction (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) B θ) S) = 0) :
    ContDiffAt ℝ ∞ (densityResponseBranch_source_unrestricted H B θ hθ S hS) H := by
  have hf := hasStrictFDerivAt_densityGradientChart_source_unrestricted (H : Matrix n n ℂ) B θ hθ S hS
  have hsmooth := contDiffAt_densityGradientChart_source_unrestricted (H : Matrix n n ℂ) B θ S hS
  have hi : ContDiffAt ℝ ∞ (hf.localInverse _ _ 0) (densityGradientChart (H : Matrix n n ℂ) B θ S 0) :=
    hsmooth.to_localInverse hf.hasFDerivAt (by simp)
  have hf0 : densityGradientChart (H : Matrix n n ℂ) B θ S 0 = 0 := by
    simp only [densityGradientChart, densityChart_zero, hstat, neg_zero]
  have hi' : ContDiffAt ℝ ∞ (hf.localInverse _ _ 0) (densityCenterFunctional (H - H)) := by
    simpa only [sub_self, map_zero, hf0] using hi
  exact contDiffAt_const.add ((densityTangent (n := n)).subtypeL.contDiff.contDiffAt.comp H
    (hi'.comp H ((densityCenterFunctional (n := n)).contDiff.contDiffAt.comp H
      (contDiffAt_id.sub contDiffAt_const))))

/-- The actual optimizer is smooth at every Hermitian center, including singular-source cases. -/
theorem contDiffAt_hermitianDensityOptimizer_source_unrestricted [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    ContDiffAt ℝ ∞ (fun K : selfAdjoint (Matrix n n ℂ) => hermitianDensityOptimizer (K : Matrix n n ℂ) B θ) H := by
  have hs := densityOptimizer_stationary_source_unrestricted (H : Matrix n n ℂ) B hθ
  have heq := eventually_densityOptimizer_eq_responseBranch_source_unrestricted H B θ hθ
    (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ) (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
    (hermitianDensityOptimizer_trace (H : Matrix n n ℂ) B θ)
       hs
  exact (contDiffAt_densityResponseBranch_source_unrestricted H B θ hθ _
    (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
       hs).congr_of_eventuallyEq heq

theorem contDiffAt_hermitianDensityPotential_source_unrestricted [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    ContDiffAt ℝ ∞ (hermitianDensityPotential B θ) H := by
  have hs := contDiffAt_hermitianDensityOptimizer_source_unrestricted H B hθ
  have hm := (hermitianInclusion (n := n)).contDiff.contDiffAt.comp H hs
  have hlinear := realTraceCLM.contDiff.contDiffAt.comp H
    ((hermitianInclusion (n := n)).contDiff.contDiffAt.mul hm)
  have hf := (contDiffAt_krausSourceFidelity_source_unrestricted B (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)
    (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
).comp H hs
  have ht := (contDiffAt_tsallisPotential θ (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)
    (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)).comp H hs
  apply ((hlinear.add hf).add ht).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun K => hermitianDensityPotential_eq_objective K B θ

/-- The genuine supremum potential has the actual optimizer as its trace gradient. -/
theorem hasFDerivAt_hermitianDensityPotential_source_unrestricted [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    HasFDerivAt (hermitianDensityPotential B θ) (tracePairing (densityOptimizer (H : Matrix n n ℂ) B θ)) H := by
  have hd := ((contDiffAt_hermitianDensityPotential_source_unrestricted H B hθ).differentiableAt
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

theorem hasStrictFDerivAt_hermitianDensityPotential_source_unrestricted [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    HasStrictFDerivAt (hermitianDensityPotential B θ) (tracePairing (densityOptimizer (H : Matrix n n ℂ) B θ)) H :=
  (contDiffAt_hermitianDensityPotential_source_unrestricted H B hθ).hasStrictFDerivAt'
    (hasFDerivAt_hermitianDensityPotential_source_unrestricted H B hθ) (by simp)

theorem hasStrictFDerivAt_fderiv_hermitianDensityPotential_source_unrestricted [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    HasStrictFDerivAt (fun K => fderiv ℝ (hermitianDensityPotential B θ) K)
      ((tracePairing.comp hermitianInclusion).comp
        (densityResponseDerivative_source_unrestricted (H : Matrix n n ℂ) B θ hθ (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)
          (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
)) H := by
  have hs := hasStrictFDerivAt_hermitianDensityOptimizer_source_unrestricted H B hθ
  have hd := (tracePairing.comp (hermitianInclusion (n := n))).hasStrictFDerivAt.comp H hs
  apply hd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun K =>
    (hasFDerivAt_hermitianDensityPotential_source_unrestricted K B hθ).fderiv.symm

/-- The actual potential Hessian is the trace pairing with the proved optimizer response. -/
theorem fderiv_fderiv_hermitianDensityPotential_apply_source_unrestricted [Nonempty n]
    (H X Y : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    fderiv ℝ (fun K => fderiv ℝ (hermitianDensityPotential B θ) K) H X Y =
      realTrace ((densityResponseDerivative_source_unrestricted (H : Matrix n n ℂ) B θ hθ (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)
        (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
       X : Matrix n n ℂ) * (Y : Matrix n n ℂ)) := by
  rw [(hasStrictFDerivAt_fderiv_hermitianDensityPotential_source_unrestricted H B hθ).hasFDerivAt.fderiv]
  rfl

theorem densityResponseDerivative_trace_source_unrestricted (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef)
    (X : selfAdjoint (Matrix n n ℂ)) :
    realTrace (densityResponseDerivative_source_unrestricted H B θ hθ S hS X : Matrix n n ℂ) = 0 :=
  (mem_densityTangent_iff _).mp
    ((densityTangentHessianEquiv_source_unrestricted H B θ hθ S hS).symm (densityCenterFunctional X)).property

theorem densityResponseDerivative_quadratic_nonneg_source_unrestricted (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef)
    (X : selfAdjoint (Matrix n n ℂ)) :
    0 ≤ realTrace ((densityResponseDerivative_source_unrestricted H B θ hθ S hS X : Matrix n n ℂ) *
      (X : Matrix n n ℂ)) := by
  let U := (densityTangentHessianEquiv_source_unrestricted H B θ hθ S hS).symm (densityCenterFunctional X)
  have hrep : densityTangentNegativeHessian H B θ S U U = densityCenterFunctional X U := by
    change densityTangentHessianEquiv_source_unrestricted H B θ hθ S hS U U = _
    dsimp only [U]
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [realTrace_mul_comm]
  change 0 ≤ densityCenterFunctional X U
  by_cases hU : U = 0
  · rw [hU]
    exact le_of_eq ((densityCenterFunctional X).map_zero).symm
  · rw [← hrep]
    exact (densityTangentNegativeHessian_pos_source_unrestricted H B θ hθ S hS U hU).le

theorem fderiv_fderiv_hermitianDensityPotential_quadratic_nonneg_source_unrestricted [Nonempty n]
    (H X : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    0 ≤ fderiv ℝ (fun K => fderiv ℝ (hermitianDensityPotential B θ) K) H X X := by
  rw [fderiv_fderiv_hermitianDensityPotential_apply_source_unrestricted H X X B hθ ]
  exact densityResponseDerivative_quadratic_nonneg_source_unrestricted (H : Matrix n n ℂ) B θ hθ
    (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)
    (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
     X

/-- Global smoothness of the actual optimizer in its Hermitian center. -/
theorem contDiff_hermitianDensityOptimizer_source_unrestricted [Nonempty n]
    (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    ContDiff ℝ ∞ (fun H : selfAdjoint (Matrix n n ℂ) =>
      hermitianDensityOptimizer (H : Matrix n n ℂ) B θ) :=
  contDiff_iff_contDiffAt.mpr fun H => contDiffAt_hermitianDensityOptimizer_source_unrestricted H B hθ

/-- Global smoothness of the actual supremum potential, with no source-rank restriction. -/
theorem contDiff_hermitianDensityPotential_source_unrestricted [Nonempty n]
    (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    ContDiff ℝ ∞ (hermitianDensityPotential B θ) :=
  contDiff_iff_contDiffAt.mpr fun H => contDiffAt_hermitianDensityPotential_source_unrestricted H B hθ

end
end MatrixSpencer
