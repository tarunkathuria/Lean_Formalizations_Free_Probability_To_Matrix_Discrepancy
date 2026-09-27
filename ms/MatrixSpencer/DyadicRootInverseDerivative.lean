import MatrixSpencer.DyadicRootDerivative

/-! The inverse of the actual root derivative equals the noncommutative
derivative of the natural power. This identifies the finite polynomial
kernel needed by the general-order regularizer. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology
namespace MatrixSpencer
noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance dyadicRootInverseCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicRootInverseSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

theorem matrixPowerDerivative_dyadicRoot_comp (m : ℕ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    (matrixPowerDerivative (2 ^ m) (dyadicRoot m (S : Matrix n n ℂ))).comp
      (hermitianInclusion.comp (hermitianDyadicRootDerivative m S hS :
        selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ))) = hermitianInclusion := by
  have hr : HasStrictFDerivAt (fun T : selfAdjoint (Matrix n n ℂ) =>
      dyadicRoot m (T : Matrix n n ℂ)) (hermitianInclusion.comp
        (hermitianDyadicRootDerivative m S hS : selfAdjoint (Matrix n n ℂ) →L[ℝ]
          selfAdjoint (Matrix n n ℂ))) S := by
    simpa only [hermitianInclusion_apply, hermitianDyadicRoot_coe, Function.comp_def] using
      (hermitianInclusion (n := n)).hasStrictFDerivAt.comp S
        (hasStrictFDerivAt_hermitianDyadicRoot m S hS)
  have hp := (hasStrictFDerivAt_matrixPower (2 ^ m) (dyadicRoot m (S : Matrix n n ℂ))).comp S hr
  have he : (fun T : selfAdjoint (Matrix n n ℂ) => dyadicRoot m (T : Matrix n n ℂ) ^ (2 ^ m))
      =ᶠ[𝓝 S] hermitianInclusion := by
    filter_upwards [eventually_posDef_of_posDef S hS] with T hT
    exact dyadicRoot_pow m hT.posSemidef
  exact (hp.congr_of_eventuallyEq he).hasFDerivAt.unique
    (hermitianInclusion (n := n)).hasFDerivAt

theorem matrixPowerDerivative_dyadicRoot_apply (m : ℕ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    matrixPowerDerivative (2 ^ m) (dyadicRoot m (S : Matrix n n ℂ))
      (hermitianDyadicRootDerivative m S hS X : Matrix n n ℂ) = (X : Matrix n n ℂ) := by
  exact DFunLike.congr_fun (matrixPowerDerivative_dyadicRoot_comp m S hS) X

/-- The actual inverse root derivative, not an assumed spectral formula. -/
theorem hermitianDyadicRootDerivative_symm_apply (m : ℕ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    ((hermitianDyadicRootDerivative m S hS).symm X : Matrix n n ℂ) =
      matrixPowerDerivative (2 ^ m) (dyadicRoot m (S : Matrix n n ℂ)) (X : Matrix n n ℂ) := by
  have h := matrixPowerDerivative_dyadicRoot_apply m S
    ((hermitianDyadicRootDerivative m S hS).symm X) hS
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem hermitianDyadicRootDerivative_symm_sum (m : ℕ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    ((hermitianDyadicRootDerivative m S hS).symm X : Matrix n n ℂ) =
      ∑ i ∈ Finset.range (2 ^ m),
        dyadicRoot m (S : Matrix n n ℂ) ^ (2 ^ m - 1 - i) * (X : Matrix n n ℂ) *
          dyadicRoot m (S : Matrix n n ℂ) ^ i := by
  rw [hermitianDyadicRootDerivative_symm_apply, matrixPowerDerivative_apply]

end
end MatrixSpencer
