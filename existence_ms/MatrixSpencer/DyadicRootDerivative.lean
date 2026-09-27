import MatrixSpencer.DyadicRoot
import MatrixSpencer.TsallisHessian
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! The actual dyadic-root derivative is an invertible composition of the
proved Sylvester inverses. This supplies the calculus for dyadic Tsallis orders. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology
namespace MatrixSpencer
noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance dyadicRootDerivativeCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicRootDerivativeSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def hermitianDyadicRootDerivative : (m : ℕ) → (S : selfAdjoint (Matrix n n ℂ)) →
    (S : Matrix n n ℂ).PosDef →
    selfAdjoint (Matrix n n ℂ) ≃L[ℝ] selfAdjoint (Matrix n n ℂ)
  | 0, _, _ => ContinuousLinearEquiv.refl ℝ _
  | m + 1, S, hS => (hermitianDyadicRootDerivative m S hS).trans
      (hermitianSylvester (hermitianSqrt (hermitianDyadicRoot m S))
        (hermitianDyadicRoot_posDef m S hS).posDef_sqrt).symm

theorem hasStrictFDerivAt_hermitianDyadicRoot (m : ℕ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (hermitianDyadicRoot m)
      (hermitianDyadicRootDerivative m S hS : selfAdjoint (Matrix n n ℂ) →L[ℝ]
        selfAdjoint (Matrix n n ℂ)) S := by
  induction m with
  | zero => exact hasStrictFDerivAt_id S
  | succ m ih =>
    exact (hasStrictFDerivAt_hermitianSqrt _ (hermitianDyadicRoot_posDef m S hS)).comp S ih

theorem fderiv_hermitianDyadicRoot (m : ℕ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (hermitianDyadicRoot m) S =
      (hermitianDyadicRootDerivative m S hS : selfAdjoint (Matrix n n ℂ) →L[ℝ]
        selfAdjoint (Matrix n n ℂ)) :=
  (hasStrictFDerivAt_hermitianDyadicRoot m S hS).hasFDerivAt.fderiv

def inverseDyadicRoot (m : ℕ) (S : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ :=
  (dyadicRoot m (S : Matrix n n ℂ))⁻¹

theorem hasStrictFDerivAt_inverseDyadicRoot (m : ℕ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (inverseDyadicRoot m)
      ((-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (inverseDyadicRoot m S)
        (inverseDyadicRoot m S)).comp (hermitianInclusion.comp
          (hermitianDyadicRootDerivative m S hS : selfAdjoint (Matrix n n ℂ) →L[ℝ]
            selfAdjoint (Matrix n n ℂ)))) S := by
  have hroot : HasStrictFDerivAt (fun T : selfAdjoint (Matrix n n ℂ) =>
      dyadicRoot m (T : Matrix n n ℂ)) (hermitianInclusion.comp
        (hermitianDyadicRootDerivative m S hS : selfAdjoint (Matrix n n ℂ) →L[ℝ]
          selfAdjoint (Matrix n n ℂ))) S := by
    simpa only [hermitianInclusion_apply, hermitianDyadicRoot_coe, Function.comp_def] using
      (hermitianInclusion (n := n)).hasStrictFDerivAt.comp S
        (hasStrictFDerivAt_hermitianDyadicRoot m S hS)
  exact (hasStrictFDerivAt_matrixInverse (dyadicRoot m (S : Matrix n n ℂ))
    (dyadicRoot_posDef m hS).isUnit).comp S hroot

/-- The natural-power map has its actual noncommutative matrix derivative. -/
def matrixPowerDerivative (p : ℕ) (Q : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  ∑ i ∈ Finset.range p,
    ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (Q ^ (p - 1 - i)) (Q ^ i)

theorem matrixPowerDerivative_apply (p : ℕ) (Q X : Matrix n n ℂ) :
    matrixPowerDerivative p Q X = ∑ i ∈ Finset.range p, Q ^ (p - 1 - i) * X * Q ^ i := by
  simp [matrixPowerDerivative, ContinuousLinearMap.mulLeftRight_apply]

theorem hasStrictFDerivAt_matrixPower (p : ℕ) (Q : Matrix n n ℂ) :
    HasStrictFDerivAt (fun X : Matrix n n ℂ => X ^ p) (matrixPowerDerivative p Q) Q := by
  convert (hasStrictFDerivAt_pow' (𝕜 := ℝ) p (x := Q)) using 1

end
end MatrixSpencer
