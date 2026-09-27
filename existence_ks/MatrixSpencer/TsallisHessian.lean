import MatrixSpencer.SqrtDerivative
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Trace square-root calculus

This file computes derivatives of the actual trace square root on the real
Hermitian space. Every inverse is justified by positive definiteness.
-/

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

namespace MatrixSpencer

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance tsallisHessianCStarAlgebra : CStarAlgebra (Matrix n n ℂ) := {}

local instance tsallisHessianNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

local instance tsallisHessianFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

/-- The real trace as a continuous real-linear functional. -/
def realTraceCLM : Matrix n n ℂ →L[ℝ] ℝ :=
  ({ toFun := realTrace
     map_add' := realTrace_add
     map_smul' := realTrace_smul } : Matrix n n ℂ →ₗ[ℝ] ℝ).toContinuousLinearMap

omit [DecidableEq n] in
@[simp] theorem realTraceCLM_apply (A : Matrix n n ℂ) : realTraceCLM A = realTrace A := rfl

/-- Pairing a physical matrix with a Hermitian direction. -/
def tracePairing : Matrix n n ℂ →L[ℝ] (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) :=
  ({ toFun := fun A => realTraceCLM.comp
       (((LinearMap.mulLeft ℝ A).toContinuousLinearMap).comp hermitianInclusion)
     map_add' := by
       intro A B
       apply ContinuousLinearMap.ext
       intro X
       change realTrace ((A + B) * (X : Matrix n n ℂ)) = _
       simp only [Matrix.add_mul, realTrace_add]
       rfl
     map_smul' := by
       intro r A
       apply ContinuousLinearMap.ext
       intro X
       change realTrace ((r • A) * (X : Matrix n n ℂ)) = _
       simp only [Matrix.smul_mul, realTrace_smul]
       rfl } : Matrix n n ℂ →ₗ[ℝ]
       (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ)).toContinuousLinearMap

@[simp] theorem tracePairing_apply (A : Matrix n n ℂ)
    (X : selfAdjoint (Matrix n n ℂ)) :
    tracePairing A X = realTrace (A * (X : Matrix n n ℂ)) := rfl

/-- Tracing the Sylvester solution eliminates the divided-difference denominator. -/
theorem realTrace_sylvester_inverse (Q B : Matrix n n ℂ) (hQ : Q.PosDef) :
    realTrace ((sylvesterEquiv Q hQ).symm B) = (1 / 2 : ℝ) * realTrace (Q⁻¹ * B) := by
  let X := (sylvesterEquiv Q hQ).symm B
  have hdet := Q.isUnit_iff_isUnit_det.mp hQ.isUnit
  have hi : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hdet
  have hir : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hdet
  have h := congrArg (fun Z => realTrace (Q⁻¹ * Z)) (sylvester_inverse_solve Q hQ B)
  change realTrace (Q⁻¹ * (Q * X + X * Q)) = realTrace (Q⁻¹ * B) at h
  have h₁ : Q⁻¹ * (Q * X) = X := by rw [← Matrix.mul_assoc, hi, Matrix.one_mul]
  have h₂ : realTrace (Q⁻¹ * (X * Q)) = realTrace X := by
    rw [← Matrix.mul_assoc, realTrace_mul_cycle, hir, Matrix.one_mul]
  rw [Matrix.mul_add, realTrace_add, h₁, h₂] at h
  change realTrace X = _
  linarith

/-- The unscaled trace square root. -/
def traceSqrt (S : selfAdjoint (Matrix n n ℂ)) : ℝ :=
  realTrace (CFC.sqrt (S : Matrix n n ℂ))

theorem hasStrictFDerivAt_traceSqrt (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt traceSqrt
      ((1 / 2 : ℝ) • tracePairing (CFC.sqrt (S : Matrix n n ℂ))⁻¹) S := by
  have hi := (hermitianInclusion (n := n)).hasStrictFDerivAt.comp S
    (hasStrictFDerivAt_hermitianSqrt S hS)
  have ht := (realTraceCLM (n := n)).hasStrictFDerivAt.comp S hi
  have heq : (1 / 2 : ℝ) • tracePairing (CFC.sqrt (S : Matrix n n ℂ))⁻¹ =
      realTraceCLM.comp (hermitianInclusion.comp
        ((hermitianSylvester (hermitianSqrt S) hS.posDef_sqrt).symm :
          selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ))) := by
    apply ContinuousLinearMap.ext
    intro X
    change (1 / 2 : ℝ) * realTrace ((CFC.sqrt (S : Matrix n n ℂ))⁻¹ *
      (X : Matrix n n ℂ)) =
      realTrace ((sylvesterEquiv (CFC.sqrt (S : Matrix n n ℂ)) hS.posDef_sqrt).symm X)
    exact (realTrace_sylvester_inverse _ _ hS.posDef_sqrt).symm
  rw [heq]
  exact ht

theorem fderiv_traceSqrt_apply (S X : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ traceSqrt S X =
      (1 / 2 : ℝ) * realTrace ((CFC.sqrt (S : Matrix n n ℂ))⁻¹ *
        (X : Matrix n n ℂ)) := by
  rw [(hasStrictFDerivAt_traceSqrt S hS).hasFDerivAt.fderiv]
  rfl

theorem eventually_posDef_of_posDef (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    ∀ᶠ X : selfAdjoint (Matrix n n ℂ) in 𝓝 S, (X : Matrix n n ℂ).PosDef := by
  have hu : ∀ᶠ X : selfAdjoint (Matrix n n ℂ) in 𝓝 S,
      IsUnit (X : Matrix n n ℂ) :=
    (hermitianInclusion (n := n)).continuous.continuousAt
      (Units.isOpen.mem_nhds hS.isUnit)
  filter_upwards [eventually_nonneg_of_posDef S hS, hu] with X hX huX
  exact hX.posSemidef.posDef_iff_isUnit.mpr huX

/-- Matrix inversion has the usual noncommutative strict derivative at every invertible matrix. -/
theorem hasStrictFDerivAt_matrixInverse (Q : Matrix n n ℂ) (hQ : IsUnit Q) :
    HasStrictFDerivAt (𝕜 := ℝ) (fun A : Matrix n n ℂ => A⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) Q⁻¹ Q⁻¹) Q := by
  rcases hQ with ⟨u, rfl⟩
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit] using
    (hasStrictFDerivAt_ringInverse (𝕜 := ℝ) u)

def inverseSqrt (S : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ :=
  (CFC.sqrt (S : Matrix n n ℂ))⁻¹

/-- The actual inverse-square-root derivative, as a map to physical matrices. -/
def inverseSqrtDerivative (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] Matrix n n ℂ :=
  (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (inverseSqrt S) (inverseSqrt S)).comp
    (hermitianInclusion.comp
      ((hermitianSylvester (hermitianSqrt S) hS.posDef_sqrt).symm :
        selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ)))

theorem hasStrictFDerivAt_inverseSqrt (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt inverseSqrt (inverseSqrtDerivative S hS) S :=
  (hasStrictFDerivAt_matrixInverse _ hS.posDef_sqrt.isUnit).comp S
    ((hermitianInclusion (n := n)).hasStrictFDerivAt.comp S
      (hasStrictFDerivAt_hermitianSqrt S hS))

theorem inverseSqrtDerivative_apply (S X : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    inverseSqrtDerivative S hS X =
      -(inverseSqrt S * (fderiv ℝ hermitianSqrt S X : Matrix n n ℂ) * inverseSqrt S) := by
  rw [fderiv_hermitianSqrt_eq S hS]
  rfl

/-- The concave p=2 Tsallis term used in the matrix proof. -/
def tsallisPotential (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) : ℝ :=
  (2 * θ) * traceSqrt S

theorem hasStrictFDerivAt_tsallisPotential (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (tsallisPotential θ) (θ • tracePairing (inverseSqrt S)) S := by
  have h := (hasStrictFDerivAt_traceSqrt S hS).const_mul (2 * θ)
  convert h using 1
  ext X
  change θ * realTrace (inverseSqrt S * (X : Matrix n n ℂ)) =
    (2 * θ) * ((1 / 2 : ℝ) * realTrace (inverseSqrt S * (X : Matrix n n ℂ)))
  ring

theorem fderiv_tsallisPotential_eq (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (tsallisPotential θ) S = θ • tracePairing (inverseSqrt S) :=
  (hasStrictFDerivAt_tsallisPotential θ S hS).hasFDerivAt.fderiv

/-- The second derivative is obtained by differentiating the proved first derivative on
the open positive-definite cone. -/
theorem hasStrictFDerivAt_fderiv_tsallisPotential (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (fun A => fderiv ℝ (tsallisPotential θ) A)
      ((θ • tracePairing).comp (inverseSqrtDerivative S hS)) S := by
  have ht := ((θ • tracePairing (n := n)) :
    Matrix n n ℂ →L[ℝ] (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ)).hasStrictFDerivAt
      (x := inverseSqrt S)
  have hc := ht.comp S (hasStrictFDerivAt_inverseSqrt S hS)
  apply hc.congr_of_eventuallyEq
  exact (eventually_posDef_of_posDef S hS).mono fun X hX =>
    (fderiv_tsallisPotential_eq θ X hX).symm

/-- Positive congruence is an actual real-linear equivalence on the Hermitian space. -/
def hermitianCongruenceEquiv (Q : Matrix n n ℂ) (hQ : Q.PosDef) :
    selfAdjoint (Matrix n n ℂ) ≃ₗ[ℝ] selfAdjoint (Matrix n n ℂ) where
  toFun X := ⟨Q * X * Q, by
    change (Q * (X : Matrix n n ℂ) * Q)ᴴ = _
    simp only [Matrix.conjTranspose_mul, hQ.isHermitian.eq,
      show (X : Matrix n n ℂ)ᴴ = X from X.property, Matrix.mul_assoc]⟩
  invFun X := ⟨Q⁻¹ * X * Q⁻¹, by
    change (Q⁻¹ * (X : Matrix n n ℂ) * Q⁻¹)ᴴ = _
    simp only [Matrix.conjTranspose_mul, hQ.inv.isHermitian.eq,
      show (X : Matrix n n ℂ)ᴴ = X from X.property, Matrix.mul_assoc]⟩
  left_inv X := by
    apply Subtype.ext
    change Q⁻¹ * (Q * (X : Matrix n n ℂ) * Q) * Q⁻¹ = X
    have hi := Matrix.nonsing_inv_mul Q (Q.isUnit_iff_isUnit_det.mp hQ.isUnit)
    have hir := Matrix.mul_nonsing_inv Q (Q.isUnit_iff_isUnit_det.mp hQ.isUnit)
    calc
      _ = (Q⁻¹ * Q) * (X : Matrix n n ℂ) * (Q * Q⁻¹) := by
        simp only [Matrix.mul_assoc]
      _ = X := by rw [hi, hir, Matrix.one_mul, Matrix.mul_one]
  right_inv X := by
    apply Subtype.ext
    change Q * (Q⁻¹ * (X : Matrix n n ℂ) * Q⁻¹) * Q = X
    have hi := Matrix.nonsing_inv_mul Q (Q.isUnit_iff_isUnit_det.mp hQ.isUnit)
    have hir := Matrix.mul_nonsing_inv Q (Q.isUnit_iff_isUnit_det.mp hQ.isUnit)
    calc
      _ = (Q * Q⁻¹) * (X : Matrix n n ℂ) * (Q⁻¹ * Q) := by
        simp only [Matrix.mul_assoc]
      _ = X := by rw [hi, hir, Matrix.one_mul, Matrix.mul_one]
  map_add' X Y := by
    apply Subtype.ext
    change Q * ((X : Matrix n n ℂ) + Y) * Q = _
    simp only [Matrix.mul_add, Matrix.add_mul]
    rfl
  map_smul' r X := by
    apply Subtype.ext
    change Q * (r • (X : Matrix n n ℂ)) * Q = _
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rfl

/-- The negative Hessian represented through the real trace pairing. Invertibility is
proved by composing Sylvester, congruence, and nonzero scalar equivalences. -/
def negativeTsallisHessianEquiv (θ : ℝ) (hθ : θ ≠ 0)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    selfAdjoint (Matrix n n ℂ) ≃L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  (((sylvesterHermitianEquiv (CFC.sqrt (S : Matrix n n ℂ)) hS.posDef_sqrt).symm.trans
      (hermitianCongruenceEquiv (CFC.sqrt (S : Matrix n n ℂ)) hS.posDef_sqrt).symm).trans
      (LinearEquiv.smulOfNeZero ℝ (selfAdjoint (Matrix n n ℂ)) θ hθ)).toContinuousLinearEquiv

theorem negativeTsallisHessianEquiv_apply (θ : ℝ) (hθ : θ ≠ 0)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    (negativeTsallisHessianEquiv θ hθ S hS X : Matrix n n ℂ) =
      θ • (inverseSqrt S * (fderiv ℝ hermitianSqrt S X : Matrix n n ℂ) * inverseSqrt S) := by
  rw [fderiv_hermitianSqrt_eq S hS]
  rfl

/-- The inverse negative Hessian has the polynomial square-root formula from the proof. -/
theorem negativeTsallisHessianEquiv_symm_apply (θ : ℝ) (hθ : θ ≠ 0)
    (S B : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    ((negativeTsallisHessianEquiv θ hθ S hS).symm B : Matrix n n ℂ) =
      θ⁻¹ • ((S : Matrix n n ℂ) * B * CFC.sqrt (S : Matrix n n ℂ) +
        CFC.sqrt (S : Matrix n n ℂ) * B * (S : Matrix n n ℂ)) := by
  change CFC.sqrt (S : Matrix n n ℂ) *
      (CFC.sqrt (S : Matrix n n ℂ) * (θ⁻¹ • (B : Matrix n n ℂ)) *
        CFC.sqrt (S : Matrix n n ℂ)) +
      (CFC.sqrt (S : Matrix n n ℂ) * (θ⁻¹ • (B : Matrix n n ℂ)) *
        CFC.sqrt (S : Matrix n n ℂ)) * CFC.sqrt (S : Matrix n n ℂ) = _
  simp only [Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
  congr 1
  have hs := CFC.sqrt_mul_sqrt_self (S : Matrix n n ℂ) hS.posSemidef.nonneg
  calc
    _ = (CFC.sqrt (S : Matrix n n ℂ) * CFC.sqrt (S : Matrix n n ℂ)) * B *
          CFC.sqrt (S : Matrix n n ℂ) +
        CFC.sqrt (S : Matrix n n ℂ) * B *
          (CFC.sqrt (S : Matrix n n ℂ) * CFC.sqrt (S : Matrix n n ℂ)) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hs]

/-- This is the actual second derivative of the scalar potential, represented by the
negative of the invertible Hermitian Hessian operator. -/
theorem fderiv_fderiv_tsallisPotential_apply (θ : ℝ) (hθ : θ ≠ 0)
    (S X Y : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (fun A => fderiv ℝ (tsallisPotential θ) A) S X Y =
      -realTrace ((negativeTsallisHessianEquiv θ hθ S hS X : Matrix n n ℂ) *
        (Y : Matrix n n ℂ)) := by
  rw [(hasStrictFDerivAt_fderiv_tsallisPotential θ S hS).hasFDerivAt.fderiv]
  change θ * realTrace (inverseSqrtDerivative S hS X * (Y : Matrix n n ℂ)) = _
  rw [inverseSqrtDerivative_apply, negativeTsallisHessianEquiv_apply,
    Matrix.neg_mul, realTrace_neg, Matrix.smul_mul, realTrace_smul]
  ring

theorem realTrace_sylvester_conjugate (Q U : Matrix n n ℂ) (hQ : IsUnit Q) :
    realTrace ((Q * U + U * Q) * (Q⁻¹ * U * Q⁻¹)) =
      2 * realTrace (U * Q⁻¹ * U) := by
  have hi := Matrix.nonsing_inv_mul Q (Q.isUnit_iff_isUnit_det.mp hQ)
  have hir := Matrix.mul_nonsing_inv Q (Q.isUnit_iff_isUnit_det.mp hQ)
  have h₁ : realTrace (Q * U * (Q⁻¹ * U * Q⁻¹)) = realTrace (U * Q⁻¹ * U) := by
    calc
      _ = realTrace (Q * (U * Q⁻¹ * U * Q⁻¹)) := by simp only [Matrix.mul_assoc]
      _ = realTrace ((U * Q⁻¹ * U * Q⁻¹) * Q) := realTrace_mul_comm _ _
      _ = realTrace (U * Q⁻¹ * U) := by rw [Matrix.mul_assoc _ Q⁻¹ Q, hi, Matrix.mul_one]
  have h₂ : realTrace (U * Q * (Q⁻¹ * U * Q⁻¹)) = realTrace (U * Q⁻¹ * U) := by
    calc
      _ = realTrace (U * (Q * Q⁻¹) * U * Q⁻¹) := by simp only [Matrix.mul_assoc]
      _ = realTrace (U * U * Q⁻¹) := by rw [hir, Matrix.mul_one]
      _ = realTrace (U * Q⁻¹ * U) := by
        rw [Matrix.mul_assoc, realTrace_mul_comm U (U * Q⁻¹)]
  rw [Matrix.add_mul, realTrace_add, h₁, h₂]
  ring

/-- Strict positive definiteness of the negative Tsallis Hessian in the real trace pairing. -/
theorem negativeTsallisHessian_quadratic_pos (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hX : X ≠ 0) :
    0 < realTrace ((X : Matrix n n ℂ) *
      (negativeTsallisHessianEquiv θ hθ.ne' S hS X : Matrix n n ℂ)) := by
  let Q := CFC.sqrt (S : Matrix n n ℂ)
  let U := (sylvesterEquiv Q hS.posDef_sqrt).symm (X : Matrix n n ℂ)
  have hU : U.IsHermitian := sylvester_inverse_isHermitian Q hS.posDef_sqrt X.property
  have hUX : Q * U + U * Q = (X : Matrix n n ℂ) :=
    sylvester_inverse_solve Q hS.posDef_sqrt X
  have hUne : U ≠ 0 := by
    intro h
    apply hX
    apply Subtype.ext
    change (X : Matrix n n ℂ) = 0
    simpa only [h, Matrix.mul_zero, Matrix.zero_mul, add_zero] using hUX.symm
  have hp := realTrace_weighted_square_pos hS.posDef_sqrt.inv hUne
  rw [hU.eq] at hp
  rw [negativeTsallisHessianEquiv_apply, fderiv_hermitianSqrt_eq S hS,
    Matrix.mul_smul, realTrace_smul]
  change 0 < θ * realTrace ((X : Matrix n n ℂ) * (Q⁻¹ * U * Q⁻¹))
  rw [← hUX, realTrace_sylvester_conjugate Q U hS.posDef_sqrt.isUnit]
  exact mul_pos hθ (mul_pos (by norm_num) hp)

theorem contDiffAt_tsallisPotential (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) : ContDiffAt ℝ ∞ (tsallisPotential θ) S := by
  have h := (realTraceCLM (n := n)).contDiff.contDiffAt.comp S
    ((hermitianInclusion (n := n)).contDiff.contDiffAt.comp S
      (contDiffAt_hermitianSqrt S hS))
  exact contDiffAt_const.mul h

end

end MatrixSpencer
