import MatrixSpencer.RectangularRidgeCalculus

/-! The actual trace-constrained stationarity equation for the mixed objective,
and its invertible gradient chart. -/
open Matrix Filter Topology
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeCalculus
open RectangularRidgePotential
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance ridgeStationarityLocal1 : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeStationarityLocal2 : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeStationarityLocal3 : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance ridgeStationarityLocal4 : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance ridgeStationarityLocal5 : NormedAddCommGroup (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
local instance ridgeStationarityLocal6 : NormedSpace ℝ (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
set_option maxHeartbeats 1200000

theorem hermitianOptimizer_posDef [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) :
    (hermitianOptimizer H B m θ κ : Matrix n n ℂ).PosDef :=
  optimizer_posDef H B hm hθ hκ.le

theorem hermitianOptimizer_trace [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) : realTrace (hermitianOptimizer H B m θ κ : Matrix n n ℂ) = 1 :=
  (optimizer_mem H B m θ κ).2

theorem hermitianOptimizer_stationary [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) :
    densityTangentRestriction (fderiv ℝ (hermitianObjective H B m θ κ)
      (hermitianOptimizer H B m θ κ)) = 0 :=
  optimizer_stationary H B m hm θ κ hθ hκ.le

theorem concaveOn_objective (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 ≤ κ) :
    ConcaveOn ℝ densitySet (objective H B m θ κ) := by
  refine ⟨densitySet_convex, ?_⟩
  intro S hS T hT a b ha hb hab
  have hd := (concaveOn_dyadicDensityObjective H B m hm θ hθ).2 hS hT ha hb hab
  have hr := mul_le_mul_of_nonneg_left (trace_sqrt_concave hS.1 hT.1 ha hb hab)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hκ)
  simp only [objective, smul_eq_mul] at *
  nlinarith

theorem stationary_isMaxOn (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 ≤ κ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (htr : realTrace (S : Matrix n n ℂ) = 1)
    (hstat : densityTangentRestriction (fderiv ℝ (hermitianObjective H B m θ κ) S) = 0) :
    ∀ T ∈ densitySet, objective H B m θ κ T ≤ objective H B m θ κ S := by
  intro T hT
  let T' : selfAdjoint (Matrix n n ℂ) := ⟨T, hT.1.isHermitian⟩
  have hc := (concaveOn_objective H B m hm θ κ hθ hκ).comp_linearMap
    (hermitianInclusion (n := n)).toLinearMap
  have hd := ((contDiffAt_hermitianObjective H B m θ κ S hS).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  have hbound := concaveOn_le_tangent hc (S := S) (T := T') ⟨hS.posSemidef, htr⟩ hT hd
  have hztrace : realTrace ((T' - S : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) = 0 := by
    change realTrace (T - (S : Matrix n n ℂ)) = 0
    rw [realTrace_sub, hT.2, htr, sub_self]
  let X : densityTangent (n := n) := ⟨T' - S, (mem_densityTangent_iff _).mpr hztrace⟩
  have hz := DFunLike.congr_fun hstat X
  change fderiv ℝ (hermitianObjective H B m θ κ) S (T' - S) = 0 at hz
  rw [hz, add_zero] at hbound
  exact hbound

theorem stationary_eq_optimizer [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 ≤ κ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (htr : realTrace (S : Matrix n n ℂ) = 1)
    (hstat : densityTangentRestriction (fderiv ℝ (hermitianObjective H B m θ κ) S) = 0) :
    hermitianOptimizer H B m θ κ = S := by
  apply Subtype.ext
  exact maximizers_eq H B hm hθ hκ (optimizer_mem H B m θ κ) ⟨hS.posSemidef, htr⟩
    (optimizer_max H B m θ κ) (stationary_isMaxOn H B m hm θ κ hθ hκ S hS htr hstat)

theorem stationarity_center_shift (H K : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    densityTangentRestriction (fderiv ℝ (hermitianObjective K B m θ κ) S) =
      densityTangentRestriction (fderiv ℝ (hermitianObjective H B m θ κ) S) +
        densityTangentRestriction (tracePairing (K - H)) := by
  rw [fderiv_eq_add K B m θ κ S hS, fderiv_eq_add H B m θ κ S hS]
  simp only [map_add]
  rw [dyadicDensity_stationarity_center_shift H K B m θ S hS]
  abel

def gradientChart (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) (X : densityTangent (n := n)) :
    densityTangent (n := n) →L[ℝ] ℝ :=
  -densityTangentRestriction (fderiv ℝ (hermitianObjective H B m θ κ) (densityChart S X))

theorem hasStrictFDerivAt_gradientChart (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (gradientChart H B m θ κ S)
      (tangentHessianEquiv H B m hm θ κ hθ hκ S hS).toContinuousLinearMap 0 := by
  have hdf : ContDiffAt ℝ ∞ (fun T => fderiv ℝ (hermitianObjective H B m θ κ) T) S :=
    (contDiffAt_hermitianObjective H B m θ κ S hS).fderiv_right (by simp)
  have hd := hdf.hasStrictFDerivAt (by simp)
  have hd' : HasStrictFDerivAt (fun T => fderiv ℝ (hermitianObjective H B m θ κ) T)
      (fderiv ℝ (fun T => fderiv ℝ (hermitianObjective H B m θ κ) T) S)
      (densityChart S 0) := by simpa using hd
  have hc := ((densityTangentRestriction (n := n)).hasStrictFDerivAt.comp 0
    (hd'.comp 0 (hasStrictFDerivAt_densityChart S 0))).neg
  convert hc using 1

theorem contDiffAt_gradientChart (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) : ContDiffAt ℝ ∞ (gradientChart H B m θ κ S) 0 := by
  have hd : ContDiffAt ℝ ∞ (fun T => fderiv ℝ (hermitianObjective H B m θ κ) T) S :=
    (contDiffAt_hermitianObjective H B m θ κ S hS).fderiv_right (by simp)
  have hd' : ContDiffAt ℝ ∞ (fun T => fderiv ℝ (hermitianObjective H B m θ κ) T)
      (densityChart S 0) := by simpa using hd
  exact ((densityTangentRestriction (n := n)).contDiff.contDiffAt.comp 0
    (hd'.comp 0 (contDiffAt_const.add (densityTangent (n := n)).subtypeL.contDiff.contDiffAt))).neg

end MatrixSpencer.RectangularRidgeCalculus
