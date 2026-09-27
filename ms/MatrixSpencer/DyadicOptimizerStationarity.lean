import MatrixSpencer.DyadicDensityOptimizer

/-! Actual stationarity and the invertible trace-constrained gradient chart. -/
open Matrix Filter Topology
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
namespace MatrixSpencer
noncomputable section
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance dyadicStationarityCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicStationaritySpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicStationarityTangentGroup : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance dyadicStationarityTangentSpace : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance dyadicStationarityDualGroup : NormedAddCommGroup (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
local instance dyadicStationarityDualSpace : NormedSpace ℝ (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance

theorem dyadicDensity_maximizer_stationary (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, dyadicDensityObjective H B m θ T ≤ dyadicDensityObjective H B m θ S) :
    densityTangentRestriction (fderiv ℝ (hermitianDyadicDensityObjective H B m θ) S) = 0 := by
  have hlocal : IsLocalMax ((hermitianDyadicDensityObjective H B m θ) ∘ densityChart S) 0 := by
    filter_upwards [eventually_densityChart_mem S hS ht] with X hX
    simpa only [Function.comp_apply, densityChart_zero, hermitianDyadicDensityObjective] using
      hmax (densityChart S X) hX
  have hd := ((contDiffAt_hermitianDyadicDensityObjective H B m θ S hS).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  have hd' : HasFDerivAt (hermitianDyadicDensityObjective H B m θ)
      (fderiv ℝ (hermitianDyadicDensityObjective H B m θ) S) (densityChart S 0) := by simpa using hd
  exact hlocal.hasFDerivAt_eq_zero (hd'.comp 0 (hasStrictFDerivAt_densityChart S 0).hasFDerivAt)

theorem dyadicDensityOptimizer_stationary [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    densityTangentRestriction (fderiv ℝ (hermitianDyadicDensityObjective H B m θ)
      (hermitianDyadicDensityOptimizer H B m θ)) = 0 :=
  dyadicDensity_maximizer_stationary H B m θ _ (dyadicDensityOptimizer_posDef H B m hm θ hθ)
    (dyadicDensityOptimizer_mem H B m θ).2 (dyadicDensityOptimizer_isMaxOn H B m θ)

theorem dyadicDensity_stationary_isMaxOn (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hstat : densityTangentRestriction (fderiv ℝ (hermitianDyadicDensityObjective H B m θ) S) = 0) :
    ∀ T ∈ densitySet, dyadicDensityObjective H B m θ T ≤ dyadicDensityObjective H B m θ S := by
  intro T hT
  let T' : selfAdjoint (Matrix n n ℂ) := ⟨T, hT.1.isHermitian⟩
  have hc := (concaveOn_dyadicDensityObjective H B m hm θ hθ).comp_linearMap
    (hermitianInclusion (n := n)).toLinearMap
  have hd := ((contDiffAt_hermitianDyadicDensityObjective H B m θ S hS).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  have hbound := concaveOn_le_tangent hc (S := S) (T := T') ⟨hS.posSemidef, ht⟩ hT hd
  have hztrace : realTrace ((T' - S : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) = 0 := by
    change realTrace (T - (S : Matrix n n ℂ)) = 0
    rw [realTrace_sub, hT.2, ht, sub_self]
  let X : densityTangent (n := n) := ⟨T' - S, (mem_densityTangent_iff _).mpr hztrace⟩
  have hz := DFunLike.congr_fun hstat X
  change fderiv ℝ (hermitianDyadicDensityObjective H B m θ) S (T' - S) = 0 at hz
  rw [hz, add_zero] at hbound
  exact hbound

theorem dyadicDensity_stationary_eq_optimizer [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hstat : densityTangentRestriction (fderiv ℝ (hermitianDyadicDensityObjective H B m θ) S) = 0) :
    hermitianDyadicDensityOptimizer H B m θ = S := by
  apply Subtype.ext
  exact dyadicDensity_maximizers_eq H B m hm θ hθ
    (dyadicDensityOptimizer_mem H B m θ) ⟨hS.posSemidef, ht⟩
    (dyadicDensityOptimizer_isMaxOn H B m θ)
    (dyadicDensity_stationary_isMaxOn H B m hm θ hθ S hS ht hstat)

theorem dyadicDensity_stationarity_center_shift (H K : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    densityTangentRestriction (fderiv ℝ (hermitianDyadicDensityObjective K B m θ) S) =
      densityTangentRestriction (fderiv ℝ (hermitianDyadicDensityObjective H B m θ) S) +
        densityTangentRestriction (tracePairing (K - H)) := by
  rw [fderiv_hermitianDyadicDensityObjective_eq H B m θ S hS,
    fderiv_hermitianDyadicDensityObjective_eq K B m θ S hS]
  simp only [map_add, map_sub]
  abel

def dyadicDensityGradientChart (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) (X : densityTangent (n := n)) :
    densityTangent (n := n) →L[ℝ] ℝ :=
  -densityTangentRestriction (fderiv ℝ (hermitianDyadicDensityObjective H B m θ) (densityChart S X))

theorem hasStrictFDerivAt_dyadicDensityGradientChart (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (dyadicDensityGradientChart H B m θ S)
      (dyadicDensityTangentHessianEquiv H B m hm θ hθ S hS).toContinuousLinearMap 0 := by
  have hd := hasStrictFDerivAt_fderiv_hermitianDyadicDensityObjective H B m hm θ S hS
  rw [← hd.hasFDerivAt.fderiv] at hd
  have hd' : HasStrictFDerivAt (fun A => fderiv ℝ (hermitianDyadicDensityObjective H B m θ) A)
      (fderiv ℝ (fun A => fderiv ℝ (hermitianDyadicDensityObjective H B m θ) A) S)
      (densityChart S 0) := by simpa using hd
  have hc := ((densityTangentRestriction (n := n)).hasStrictFDerivAt.comp 0
    (hd'.comp 0 (hasStrictFDerivAt_densityChart S 0))).neg
  convert hc using 1

theorem contDiffAt_dyadicDensityGradientChart (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (dyadicDensityGradientChart H B m θ S) 0 := by
  have hd : ContDiffAt ℝ ∞ (fun A => fderiv ℝ (hermitianDyadicDensityObjective H B m θ) A) S :=
    (contDiffAt_hermitianDyadicDensityObjective H B m θ S hS).fderiv_right (by simp)
  have hd' : ContDiffAt ℝ ∞ (fun A => fderiv ℝ (hermitianDyadicDensityObjective H B m θ) A)
      (densityChart S 0) := by simpa using hd
  exact ((densityTangentRestriction (n := n)).contDiff.contDiffAt.comp 0
    (hd'.comp 0 (contDiffAt_const.add (densityTangent (n := n)).subtypeL.contDiff.contDiffAt))).neg

end
end MatrixSpencer
