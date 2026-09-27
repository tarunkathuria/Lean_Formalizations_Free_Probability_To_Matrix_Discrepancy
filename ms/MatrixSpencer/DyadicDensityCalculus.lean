import MatrixSpencer.SingularDensityCalculus
import MatrixSpencer.DyadicTsallisConcavity
import MatrixSpencer.RegularizedOwnerPotential
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Actual density calculus for dyadic Tsallis regularization

The physical density is positive definite, while its concrete Kraus source
may be singular. Source fidelity is the unchanged actual function, whose
fixed-support smoothness was already proved in `SingularDensityCalculus`.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

namespace MatrixSpencer
noncomputable section

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

local instance dyadicDensityCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicDensitySpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicDensityFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

def dyadicDensityObjective (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ : ℝ) (S : Matrix n n ℂ) : ℝ :=
  realTrace (H * S) + 2 * fidelity S (krausChannel B S) + dyadicTsallisRegularizer m θ S

def hermitianDyadicDensityObjective (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) : ℝ :=
  dyadicDensityObjective H B m θ (S : Matrix n n ℂ)

theorem hermitianDyadicDensityObjective_eq (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) :
    hermitianDyadicDensityObjective H B m θ S =
      tracePairing H S + krausSourceFidelity B S + dyadicTsallisPotential m θ S := rfl

theorem regularizedOwnerObjective_eq_dyadicDensityObjective [DecidableEq ι]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (θ : ℝ) (S : Matrix n n ℂ) :
    regularizedOwnerObjective H A C (dyadicTsallisRegularizer m θ) S =
      dyadicDensityObjective H (covarianceKraus A C) m θ S := by
  unfold regularizedOwnerObjective dyadicDensityObjective
  rw [covarianceSource_eq_kraus A hA hC]

/-- Actual smoothness has no faithful-source premise. -/
theorem contDiffAt_hermitianDyadicDensityObjective (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (hermitianDyadicDensityObjective H B m θ) S :=
  (((tracePairing H).contDiff.contDiffAt).add
    (contDiffAt_krausSourceFidelity_source_unrestricted B S hS)).add
      (contDiffAt_dyadicTsallisPotential m θ S hS)

theorem fderiv_hermitianDyadicDensityObjective_eq (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (hermitianDyadicDensityObjective H B m θ) S = tracePairing H +
      fderiv ℝ (krausSourceFidelity B) S + fderiv ℝ (dyadicTsallisPotential m θ (n := n)) S := by
  have hf := ((contDiffAt_krausSourceFidelity_source_unrestricted B S hS).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  have ht := ((contDiffAt_dyadicTsallisPotential m θ S hS).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  exact (((tracePairing H).hasFDerivAt.add hf).add ht).fderiv

theorem hasFDerivAt_hermitianDyadicDensityObjective (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    HasFDerivAt (hermitianDyadicDensityObjective H B m θ)
      (tracePairing H + fderiv ℝ (krausSourceFidelity B) S +
        θ • tracePairing (inverseDyadicRoot m S)) S := by
  have hf := ((contDiffAt_krausSourceFidelity_source_unrestricted B S hS).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  exact (((tracePairing H).hasFDerivAt.add hf).add
    (hasStrictFDerivAt_dyadicTsallisPotential m hm θ S hS).hasFDerivAt)

/-- Differentiating the actual gradient gives exactly the sum of the two actual curvatures. -/
theorem hasStrictFDerivAt_fderiv_hermitianDyadicDensityObjective (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (fun X => fderiv ℝ (hermitianDyadicDensityObjective H B m θ) X)
      (fderiv ℝ (fun X => fderiv ℝ (krausSourceFidelity B) X) S +
        fderiv ℝ (fun X => fderiv ℝ (dyadicTsallisPotential m θ (n := n)) X) S) S := by
  have hf := hasStrictFDerivAt_fderiv_krausSourceFidelity_source_unrestricted B S hS
  rw [← hf.hasFDerivAt.fderiv] at hf
  have ht := hasStrictFDerivAt_fderiv_dyadicTsallisPotential m hm θ S hS
  rw [← ht.hasFDerivAt.fderiv] at ht
  have hc := ((hasStrictFDerivAt_const (𝕜 := ℝ) (tracePairing H) S).add hf).add ht
  simp only [zero_add] at hc
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_posDef_of_posDef S hS] with X hX
  exact (fderiv_hermitianDyadicDensityObjective_eq H B m θ X hX).symm

theorem fderiv_fderiv_hermitianDyadicDensityObjective_apply (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ)
    (S X Y : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (fun A => fderiv ℝ (hermitianDyadicDensityObjective H B m θ) A) S X Y =
      fderiv ℝ (fun A => fderiv ℝ (krausSourceFidelity B) A) S X Y +
        fderiv ℝ (fun A => fderiv ℝ (dyadicTsallisPotential m θ (n := n)) A) S X Y := by
  rw [(hasStrictFDerivAt_fderiv_hermitianDyadicDensityObjective H B m hm θ S hS).hasFDerivAt.fderiv]
  rfl

def dyadicDensityNegativeHessian (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) :=
  -fderiv ℝ (fun X => fderiv ℝ (hermitianDyadicDensityObjective H B m θ) X) S

theorem dyadicDensityNegativeHessian_symmetric (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (X Y : selfAdjoint (Matrix n n ℂ)) :
    dyadicDensityNegativeHessian H B m θ S X Y = dyadicDensityNegativeHessian H B m θ S Y X := by
  have h := (contDiffAt_hermitianDyadicDensityObjective H B m θ S hS).isSymmSndFDerivAt
    (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)
  exact congrArg Neg.neg (h X Y)

theorem negativeDyadicDensityHessian_quadratic_pos (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) (hX : X ≠ 0) :
    0 < dyadicDensityNegativeHessian H B m θ S X X := by
  have hf := fderiv_fderiv_krausSourceFidelity_quadratic_nonpos_source_unrestricted B S X hS
  have ht := fderiv_fderiv_dyadicTsallisPotential_quadratic_neg m hm θ hθ S X hS hX
  change 0 < -fderiv ℝ (fun A => fderiv ℝ (hermitianDyadicDensityObjective H B m θ) A) S X X
  rw [fderiv_fderiv_hermitianDyadicDensityObjective_apply H B m hm θ S X X hS]
  linarith

theorem dyadicDensityNegativeHessian_nonneg (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    0 ≤ dyadicDensityNegativeHessian H B m θ S X X := by
  by_cases hX : X = 0
  · subst X; simp
  · exact (negativeDyadicDensityHessian_quadratic_pos H B m hm θ hθ S X hS hX).le

/-- The full actual negative Hessian is an isomorphism to the real Hermitian dual. -/
def dyadicDensityHessianEquiv (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    selfAdjoint (Matrix n n ℂ) ≃L[ℝ] (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) :=
  positiveBilinearEquiv (dyadicDensityNegativeHessian H B m θ S)
    (fun X hX => negativeDyadicDensityHessian_quadratic_pos H B m hm θ hθ S X hS hX)

@[simp] theorem dyadicDensityHessianEquiv_apply (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    dyadicDensityHessianEquiv H B m hm θ hθ S hS X = dyadicDensityNegativeHessian H B m θ S X := rfl

local instance dyadicDensityTangentNormedGroup : NormedAddCommGroup (densityTangent (n := n)) :=
  inferInstance
local instance dyadicDensityTangentSpace : NormedSpace ℝ (densityTangent (n := n)) :=
  inferInstance
local instance dyadicDensityTangentFiniteDimensional : FiniteDimensional ℝ (densityTangent (n := n)) :=
  inferInstance

def dyadicDensityTangentNegativeHessian (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) :
    densityTangent (n := n) →L[ℝ] (densityTangent (n := n) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (densityTangent (n := n))
      (selfAdjoint (Matrix n n ℂ)) ℝ).flip (densityTangent (n := n)).subtypeL).comp
    ((dyadicDensityNegativeHessian H B m θ S).comp (densityTangent (n := n)).subtypeL)

@[simp] theorem dyadicDensityTangentNegativeHessian_apply (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (X Y : densityTangent (n := n)) :
    dyadicDensityTangentNegativeHessian H B m θ S X Y =
      dyadicDensityNegativeHessian H B m θ S X Y := rfl

theorem dyadicDensityTangentNegativeHessian_pos (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (X : densityTangent (n := n)) (hX : X ≠ 0) :
    0 < dyadicDensityTangentNegativeHessian H B m θ S X X := by
  have hX' : (X : selfAdjoint (Matrix n n ℂ)) ≠ 0 := fun h => hX (Subtype.ext h)
  exact negativeDyadicDensityHessian_quadratic_pos H B m hm θ hθ S X hS hX'

/-- The actual trace-zero negative Hessian is invertible even when the Kraus source is singular. -/
def dyadicDensityTangentHessianEquiv (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    densityTangent (n := n) ≃L[ℝ] (densityTangent (n := n) →L[ℝ] ℝ) :=
  positiveBilinearEquiv (dyadicDensityTangentNegativeHessian H B m θ S)
    (dyadicDensityTangentNegativeHessian_pos H B m hm θ hθ S hS)

@[simp] theorem dyadicDensityTangentHessianEquiv_apply (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (X : densityTangent (n := n)) :
    dyadicDensityTangentHessianEquiv H B m hm θ hθ S hS X =
      dyadicDensityTangentNegativeHessian H B m θ S X := rfl

end
end MatrixSpencer
