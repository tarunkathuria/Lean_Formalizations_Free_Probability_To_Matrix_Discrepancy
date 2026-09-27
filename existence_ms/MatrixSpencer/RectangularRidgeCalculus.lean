import MatrixSpencer.RectangularRidgePotential
import MatrixSpencer.RectangularRidgeResponse

/-! Actual calculus for the mixed rectangular objective. The square-root
ridge contributes nonnegative negative curvature, so the dyadic response
comparison remains valid at the mixed optimizer itself. -/
open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeCalculus
open RectangularRidgePotential
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance ridgeCalculusLocal1 : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeCalculusLocal2 : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeCalculusLocal3 : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
local instance ridgeCalculusLocal4 : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance ridgeCalculusLocal5 : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance ridgeCalculusLocal6 : FiniteDimensional ℝ (densityTangent (n := n)) := inferInstance
set_option maxHeartbeats 1200000

def hermitianObjective (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) : ℝ :=
  hermitianDyadicDensityObjective H B m θ S + tsallisPotential κ S

theorem objective_eq (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) :
    hermitianObjective H B m θ κ S = objective H B m θ κ S := rfl

theorem contDiffAt_hermitianObjective (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (hermitianObjective H B m θ κ) S :=
  (contDiffAt_hermitianDyadicDensityObjective H B m θ S hS).add
    (contDiffAt_tsallisPotential κ S hS)

theorem hasFDerivAt_hermitianObjective (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    HasFDerivAt (hermitianObjective H B m θ κ)
      (tracePairing H + fderiv ℝ (krausSourceFidelity B) S +
        θ • tracePairing (inverseDyadicRoot m S) + κ • tracePairing (inverseSqrt S)) S :=
  (hasFDerivAt_hermitianDyadicDensityObjective H B m hm θ S hS).add
    (hasStrictFDerivAt_tsallisPotential κ S hS).hasFDerivAt

theorem fderiv_hermitianObjective_eq (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (hermitianObjective H B m θ κ) S =
      tracePairing H + fderiv ℝ (krausSourceFidelity B) S +
        θ • tracePairing (inverseDyadicRoot m S) + κ • tracePairing (inverseSqrt S) :=
  (hasFDerivAt_hermitianObjective H B m hm θ κ S hS).fderiv

theorem fderiv_eq_add (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (hermitianObjective H B m θ κ) S =
      fderiv ℝ (hermitianDyadicDensityObjective H B m θ) S +
        fderiv ℝ (tsallisPotential κ) S := by
  exact (((contDiffAt_hermitianDyadicDensityObjective H B m θ S hS).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt.add
      ((contDiffAt_tsallisPotential κ S hS).differentiableAt
        (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt).fderiv

theorem fderiv_fderiv_eq_add (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (fun T => fderiv ℝ (hermitianObjective H B m θ κ) T) S =
      fderiv ℝ (fun T => fderiv ℝ (hermitianDyadicDensityObjective H B m θ) T) S +
        fderiv ℝ (fun T => fderiv ℝ (tsallisPotential κ) T) S := by
  have hd := hasStrictFDerivAt_fderiv_hermitianDyadicDensityObjective H B m hm θ S hS
  rw [← hd.hasFDerivAt.fderiv] at hd
  have hr := hasStrictFDerivAt_fderiv_tsallisPotential κ S hS
  rw [← hr.hasFDerivAt.fderiv] at hr
  apply HasFDerivAt.fderiv
  apply (hd.add hr).hasFDerivAt.congr_of_eventuallyEq
  filter_upwards [eventually_posDef_of_posDef S hS] with T hT
  exact fderiv_eq_add H B m θ κ T hT

def negativeHessian (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) :=
  -fderiv ℝ (fun T => fderiv ℝ (hermitianObjective H B m θ κ) T) S

theorem negativeHessian_ge_dyadic (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    dyadicDensityNegativeHessian H B m θ S X X ≤ negativeHessian H B m θ κ S X X := by
  have hp := negativeTsallisBilinear_nonneg κ hκ S hS X
  rw [negativeTsallisBilinear_apply] at hp
  unfold negativeHessian
  rw [fderiv_fderiv_eq_add H B m hm θ κ S hS]
  change _ ≤ -(fderiv ℝ (fun T => fderiv ℝ (hermitianDyadicDensityObjective H B m θ) T) S X X +
    fderiv ℝ (fun T => fderiv ℝ (tsallisPotential κ) T) S X X)
  rw [fderiv_fderiv_tsallisPotential_apply κ hκ.ne' S X X hS]
  change -fderiv ℝ (fun T => fderiv ℝ (hermitianDyadicDensityObjective H B m θ) T) S X X ≤ _
  linarith

theorem negativeHessian_pos (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) (hX : X ≠ 0) :
    0 < negativeHessian H B m θ κ S X X :=
  (negativeDyadicDensityHessian_quadratic_pos H B m hm θ hθ S X hS hX).trans_le
    (negativeHessian_ge_dyadic H B m hm θ hκ S X hS)

def tangentNegativeHessian (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) :
    densityTangent (n := n) →L[ℝ] (densityTangent (n := n) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (densityTangent (n := n))
      (selfAdjoint (Matrix n n ℂ)) ℝ).flip (densityTangent (n := n)).subtypeL).comp
    ((negativeHessian H B m θ κ S).comp (densityTangent (n := n)).subtypeL)

def tangentHessianEquiv (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    RectangularRidgeResponse.TangentInverse n :=
  positiveBilinearEquiv (tangentNegativeHessian H B m θ κ S)
    (fun X hX => negativeHessian_pos H B m hm hθ hκ S X hS (fun hz => hX (Subtype.ext hz)))

theorem tangentHessianEquiv_ge_dyadic (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (X : densityTangent (n := n)) :
    dyadicDensityNegativeHessian H B m θ S X X ≤
      tangentHessianEquiv H B m hm θ κ hθ hκ S hS X X :=
  negativeHessian_ge_dyadic H B m hm θ hκ S X hS

theorem maximizer_stationary (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (htr : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, objective H B m θ κ T ≤ objective H B m θ κ S) :
    densityTangentRestriction (fderiv ℝ (hermitianObjective H B m θ κ) S) = 0 := by
  have hl : IsLocalMax ((hermitianObjective H B m θ κ) ∘ densityChart S) 0 := by
    filter_upwards [eventually_densityChart_mem S hS htr] with X hX
    simpa only [Function.comp_apply, densityChart_zero, objective_eq] using hmax (densityChart S X) hX
  have hd := ((contDiffAt_hermitianObjective H B m θ κ S hS).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  have hd' : HasFDerivAt (hermitianObjective H B m θ κ)
      (fderiv ℝ (hermitianObjective H B m θ κ) S) (densityChart S 0) := by simpa using hd
  exact hl.hasFDerivAt_eq_zero (hd'.comp 0 (hasStrictFDerivAt_densityChart S 0).hasFDerivAt)

def hermitianOptimizer [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) : selfAdjoint (Matrix n n ℂ) :=
  ⟨optimizer H B m θ κ, (optimizer_mem H B m θ κ).1.isHermitian⟩

theorem optimizer_stationary [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 ≤ κ) :
    densityTangentRestriction (fderiv ℝ (hermitianObjective H B m θ κ)
      (hermitianOptimizer H B m θ κ)) = 0 :=
  maximizer_stationary H B m θ κ _ (optimizer_posDef H B hm hθ hκ)
    (optimizer_mem H B m θ κ).2 (optimizer_max H B m θ κ)

end MatrixSpencer.RectangularRidgeCalculus
