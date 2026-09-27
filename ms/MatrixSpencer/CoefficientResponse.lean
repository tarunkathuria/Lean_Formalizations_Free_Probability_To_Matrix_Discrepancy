import MatrixSpencer.ObservedResponse
import MatrixSpencer.OwnerPotential

/-!
# Coefficient covariance and the actual response trace

The coefficient response matrix uses half the actual center Hessian.
Its covariance trace equals the response in the square-root factored
Kraus directions, including singular coefficient covariances.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer

set_option maxHeartbeats 800000

section Bilinear

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def coefficientMix (A : ι → E) (R : Matrix ι κ ℝ) (a : κ) : E :=
  ∑ i, R i a • A i

def responseGram (β : E →L[ℝ] (E →L[ℝ] ℝ)) (A : ι → E) : Matrix ι ι ℝ :=
  fun i j => β (A i) (A j)

theorem responseGram_mix (β : E →L[ℝ] (E →L[ℝ] ℝ)) (A : ι → E) (R : Matrix ι κ ℝ) :
    responseGram β (coefficientMix A R) = Rᵀ * responseGram β A * R := by
  ext a b
  simp only [responseGram, coefficientMix, map_sum, map_smul,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem responseGram_factor_trace (β : E →L[ℝ] (E →L[ℝ] ℝ))
    (A : ι → E) (R : Matrix ι κ ℝ) :
    realTrace ((R * Rᵀ) * responseGram β A) =
      ∑ a, β (coefficientMix A R a) (coefficientMix A R a) := by
  have ht : realTrace ((R * Rᵀ) * responseGram β A) =
      realTrace (Rᵀ * responseGram β A * R) :=
    congrArg RCLike.re ((Matrix.trace_mul_cycle R Rᵀ (responseGram β A)).trans
      (Matrix.trace_mul_cycle (responseGram β A) R Rᵀ))
  rw [ht, ← responseGram_mix]
  rfl

end Bilinear

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

local instance coefficientResponseCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance coefficientResponseNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance coefficientResponseFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

theorem covarianceKraus_isHermitian (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (a : ι) :
    (covarianceKraus A C a).IsHermitian := mixedKraus_isHermitian A (CFC.sqrt C) hA a

def ownerPotentialAsCenter (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (θ : ℝ)
    (H : selfAdjoint (Matrix n n ℂ)) : ℝ := ownerPotential H A C θ

def ownerCenterHessian (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (θ : ℝ)
    (H : selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) :=
  fderiv ℝ (fun K => fderiv ℝ (ownerPotentialAsCenter A C θ) K) H

/-- The original coefficient matrix of half the actual optimized center Hessian. -/
def ownerCoefficientResponse (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ)) : Matrix ι ι ℝ :=
  (2 : ℝ)⁻¹ • responseGram (ownerCenterHessian A C θ H) (hermitianMatrixFamily A hA)

theorem coefficientMix_hermitian_coe (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (R : Matrix ι ι ℝ) (a : ι) :
    ((coefficientMix (hermitianMatrixFamily A hA) R a : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) =
      mixedKraus A R a := by
  change (selfAdjoint (Matrix n n ℂ)).subtype
    (∑ i, R i a • hermitianMatrixFamily A hA i) = ∑ i, R i a • A i
  rw [map_sum]
  rfl

theorem ownerPotentialAsCenter_eq (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ : ℝ) :
    ownerPotentialAsCenter A C θ = hermitianDensityPotential (covarianceKraus A C) θ := by
  funext H
  change ownerPotential (H : Matrix n n ℂ) A C θ = densityPotential (H : Matrix n n ℂ) (covarianceKraus A C) θ
  exact ownerPotential_eq_densityPotential (H : Matrix n n ℂ) A hA hC θ

/-- The coefficient response trace is exactly the observed response after factoring C. -/
theorem ownerCoefficientResponse_trace_eq (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ)) :
    realTrace (C * ownerCoefficientResponse A hA C θ H) =
      krausObservedResponse H (covarianceKraus A C) (fun a => covarianceKraus_isHermitian A hA C a) θ := by
  have hs : CFC.sqrt C * (CFC.sqrt C)ᵀ = C := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, (CFC.sqrt_nonneg C).posSemidef.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self C hC.nonneg]
  rw [ownerCoefficientResponse, Matrix.mul_smul, realTrace_smul, ← hs,
    responseGram_factor_trace]
  rw [hs]
  unfold krausObservedResponse
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  have hm : coefficientMix (hermitianMatrixFamily A hA) (CFC.sqrt C) a =
      hermitianMatrixFamily (covarianceKraus A C)
        (fun a => covarianceKraus_isHermitian A hA C a) a := by
    apply Subtype.ext
    exact coefficientMix_hermitian_coe A hA (CFC.sqrt C) a
  rw [hm]
  simp only [ownerCenterHessian, ownerPotentialAsCenter_eq A hA hC θ]

end MatrixSpencer
