import MatrixSpencer.DyadicRootInverseDerivative
import MatrixSpencer.MatrixPowerTrace

/-! Actual dyadic Tsallis regularizer, its gradient, and its invertible
negative Hessian. The derivative operators are derived from the function. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology
namespace MatrixSpencer
noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance dyadicTsallisCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicTsallisSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicTsallisFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

/-- For p=2^m this is θp/(p−1) Tr(S^(1−1/p)). -/
def dyadicTsallisRegularizer (m : ℕ) (θ : ℝ) (S : Matrix n n ℂ) : ℝ :=
  (θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)) * realTrace (dyadicRoot m S ^ (2 ^ m - 1))

def dyadicTsallisPotential (m : ℕ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) : ℝ :=
  dyadicTsallisRegularizer m θ (S : Matrix n n ℂ)

theorem dyadicTsallisPotential_one (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) :
    dyadicTsallisPotential 1 θ S = tsallisPotential θ S := by
  simp [dyadicTsallisPotential, dyadicTsallisRegularizer, dyadicRoot, tsallisPotential, traceSqrt]
  left
  ring

theorem hasStrictFDerivAt_dyadicTsallisPotential (m : ℕ) (hm : 1 ≤ m) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (dyadicTsallisPotential m θ)
      (θ • tracePairing (inverseDyadicRoot m S)) S := by
  have hp : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ (1 : ℕ) := by norm_num
         _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
  have hr : HasStrictFDerivAt (fun T : selfAdjoint (Matrix n n ℂ) =>
      dyadicRoot m (T : Matrix n n ℂ)) (hermitianInclusion.comp
        (hermitianDyadicRootDerivative m S hS : selfAdjoint (Matrix n n ℂ) →L[ℝ]
          selfAdjoint (Matrix n n ℂ))) S := by
    simpa only [hermitianInclusion_apply, hermitianDyadicRoot_coe, Function.comp_def] using
      (hermitianInclusion (n := n)).hasStrictFDerivAt.comp S
        (hasStrictFDerivAt_hermitianDyadicRoot m S hS)
  have ht := ((realTraceCLM (n := n)).hasStrictFDerivAt.comp
    (dyadicRoot m (S : Matrix n n ℂ))
    (hasStrictFDerivAt_matrixPower (2 ^ m - 1) (dyadicRoot m (S : Matrix n n ℂ)))).comp S hr
  have h := ht.const_mul (θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1))
  convert h using 1
  ext X
  change θ * realTrace ((dyadicRoot m (S : Matrix n n ℂ))⁻¹ * (X : Matrix n n ℂ)) =
    (θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)) *
      realTrace (matrixPowerDerivative (2 ^ m - 1) (dyadicRoot m (S : Matrix n n ℂ))
        (hermitianDyadicRootDerivative m S hS X : Matrix n n ℂ))
  have he := normalized_pred_power_trace_eq hp (dyadicRoot m (S : Matrix n n ℂ))
    (hermitianDyadicRootDerivative m S hS X : Matrix n n ℂ) (dyadicRoot_posDef m hS).isUnit
  rw [matrixPowerDerivative_dyadicRoot_apply] at he
  simp only [Nat.cast_pow, Nat.cast_ofNat] at he
  rw [show θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1) =
    θ * ((2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)) by ring, mul_assoc, he]

theorem fderiv_dyadicTsallisPotential_eq (m : ℕ) (hm : 1 ≤ m) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (dyadicTsallisPotential m θ) S = θ • tracePairing (inverseDyadicRoot m S) :=
  (hasStrictFDerivAt_dyadicTsallisPotential m hm θ S hS).hasFDerivAt.fderiv

def inverseDyadicRootDerivative (m : ℕ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) : selfAdjoint (Matrix n n ℂ) →L[ℝ] Matrix n n ℂ :=
  (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (inverseDyadicRoot m S)
    (inverseDyadicRoot m S)).comp (hermitianInclusion.comp
      (hermitianDyadicRootDerivative m S hS : selfAdjoint (Matrix n n ℂ) →L[ℝ]
        selfAdjoint (Matrix n n ℂ)))

theorem inverseDyadicRootDerivative_apply (m : ℕ) (S X : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    inverseDyadicRootDerivative m S hS X =
      -(inverseDyadicRoot m S * (hermitianDyadicRootDerivative m S hS X : Matrix n n ℂ) *
        inverseDyadicRoot m S) := rfl

theorem hasStrictFDerivAt_fderiv_dyadicTsallisPotential (m : ℕ) (hm : 1 ≤ m) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (fun T => fderiv ℝ (dyadicTsallisPotential m θ) T)
      ((θ • tracePairing).comp (inverseDyadicRootDerivative m S hS)) S := by
  have ht := ((θ • tracePairing (n := n)) : Matrix n n ℂ →L[ℝ]
    (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ)).hasStrictFDerivAt (x := inverseDyadicRoot m S)
  have hc := ht.comp S (hasStrictFDerivAt_inverseDyadicRoot m S hS)
  apply hc.congr_of_eventuallyEq
  exact (eventually_posDef_of_posDef S hS).mono fun T hT =>
    (fderiv_dyadicTsallisPotential_eq m hm θ T hT).symm

def negativeDyadicTsallisHessianEquiv (m : ℕ) (θ : ℝ) (hθ : θ ≠ 0)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    selfAdjoint (Matrix n n ℂ) ≃L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  (((hermitianDyadicRootDerivative m S hS).toLinearEquiv.trans
    (hermitianCongruenceEquiv (dyadicRoot m (S : Matrix n n ℂ))
      (dyadicRoot_posDef m hS)).symm).trans
        (LinearEquiv.smulOfNeZero ℝ (selfAdjoint (Matrix n n ℂ)) θ hθ)).toContinuousLinearEquiv

theorem negativeDyadicTsallisHessianEquiv_apply (m : ℕ) (θ : ℝ) (hθ : θ ≠ 0)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    (negativeDyadicTsallisHessianEquiv m θ hθ S hS X : Matrix n n ℂ) =
      θ • (inverseDyadicRoot m S * (hermitianDyadicRootDerivative m S hS X : Matrix n n ℂ) *
        inverseDyadicRoot m S) := rfl

theorem negativeDyadicTsallisHessianEquiv_symm_apply (m : ℕ) (θ : ℝ) (hθ : θ ≠ 0)
    (S B : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    ((negativeDyadicTsallisHessianEquiv m θ hθ S hS).symm B : Matrix n n ℂ) =
      θ⁻¹ • matrixPowerDerivative (2 ^ m) (dyadicRoot m (S : Matrix n n ℂ))
        (dyadicRoot m (S : Matrix n n ℂ) * B * dyadicRoot m (S : Matrix n n ℂ)) := by
  change ((hermitianDyadicRootDerivative m S hS).symm
    ((hermitianCongruenceEquiv (dyadicRoot m (S : Matrix n n ℂ)) (dyadicRoot_posDef m hS))
      (θ⁻¹ • B)) : Matrix n n ℂ) = _
  rw [hermitianDyadicRootDerivative_symm_apply]
  change matrixPowerDerivative (2 ^ m) (dyadicRoot m (S : Matrix n n ℂ))
    (dyadicRoot m (S : Matrix n n ℂ) * (θ⁻¹ • (B : Matrix n n ℂ)) *
      dyadicRoot m (S : Matrix n n ℂ)) = _
  rw [Matrix.mul_smul, Matrix.smul_mul, map_smul]

theorem fderiv_fderiv_dyadicTsallisPotential_apply (m : ℕ) (hm : 1 ≤ m) (θ : ℝ)
    (hθ : θ ≠ 0) (S X Y : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (fun T => fderiv ℝ (dyadicTsallisPotential m θ) T) S X Y =
      -realTrace ((negativeDyadicTsallisHessianEquiv m θ hθ S hS X : Matrix n n ℂ) *
        (Y : Matrix n n ℂ)) := by
  rw [(hasStrictFDerivAt_fderiv_dyadicTsallisPotential m hm θ S hS).hasFDerivAt.fderiv]
  change θ * realTrace (inverseDyadicRootDerivative m S hS X * (Y : Matrix n n ℂ)) = _
  rw [inverseDyadicRootDerivative_apply, negativeDyadicTsallisHessianEquiv_apply,
    Matrix.neg_mul, realTrace_neg, Matrix.smul_mul, realTrace_smul]
  ring

theorem contDiffAt_dyadicTsallisPotential (m : ℕ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (dyadicTsallisPotential m θ) S := by
  have hr := (hermitianInclusion (n := n)).contDiff.contDiffAt.comp S
    (contDiffAt_hermitianDyadicRoot m S hS)
  have ht := (realTraceCLM (n := n)).contDiff.contDiffAt.comp S (hr.pow (2 ^ m - 1))
  simpa only [dyadicTsallisPotential, dyadicTsallisRegularizer, Function.comp_def,
    realTraceCLM_apply, hermitianInclusion_apply, hermitianDyadicRoot_coe] using
      contDiffAt_const.mul ht

end
end MatrixSpencer
