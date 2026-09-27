import MatrixSpencer.Sylvester
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Differentiating the positive matrix square root

All derivatives in this file use the real vector space of Hermitian matrices.
The norm is the matrix operator norm. The derivative inverse is constructed from
the proved Sylvester bijection.
-/

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

namespace MatrixSpencer

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance sqrtDerivativeCStarAlgebra : CStarAlgebra (Matrix n n ℂ) := {}

local instance sqrtDerivativeFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

/-- The inclusion of the real Hermitian space into all matrices. -/
noncomputable def hermitianInclusion :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] Matrix n n ℂ :=
  (selfAdjoint.submodule ℝ (Matrix n n ℂ)).subtypeL

/-- Real-linear projection onto Hermitian matrices. -/
noncomputable def hermitianProjection :
    Matrix n n ℂ →L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  (selfAdjointPart ℝ).toContinuousLinearMap

@[simp] theorem hermitianInclusion_apply (X : selfAdjoint (Matrix n n ℂ)) :
    hermitianInclusion X = (X : Matrix n n ℂ) := rfl

@[simp] theorem hermitianProjection_apply (X : Matrix n n ℂ) :
    hermitianProjection X = selfAdjointPart ℝ X := rfl

/-- Squaring, with its natural real Hermitian domain and range. -/
noncomputable def hermitianSquare (X : selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix n n ℂ) :=
  hermitianProjection ((X : Matrix n n ℂ) * X)

@[simp] theorem hermitianSquare_coe (X : selfAdjoint (Matrix n n ℂ)) :
    (hermitianSquare X : Matrix n n ℂ) = (X : Matrix n n ℂ) * X := by
  apply IsSelfAdjoint.coe_selfAdjointPart_apply
  change ((X : Matrix n n ℂ) * (X : Matrix n n ℂ))ᴴ = _
  rw [Matrix.conjTranspose_mul, show (X : Matrix n n ℂ)ᴴ = X from X.property]

/-- The actual positive square root, including its existing total definition away from the cone. -/
noncomputable def hermitianSqrt (X : selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix n n ℂ) :=
  ⟨CFC.sqrt (X : Matrix n n ℂ), (CFC.sqrt_nonneg _).isSelfAdjoint⟩

@[simp] theorem hermitianSqrt_coe (X : selfAdjoint (Matrix n n ℂ)) :
    (hermitianSqrt X : Matrix n n ℂ) = CFC.sqrt (X : Matrix n n ℂ) := rfl

/-- The Sylvester isomorphism equipped with the operator-norm topology. -/
noncomputable def hermitianSylvester (Q : selfAdjoint (Matrix n n ℂ))
    (hQ : (Q : Matrix n n ℂ).PosDef) :
    selfAdjoint (Matrix n n ℂ) ≃L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  (sylvesterHermitianEquiv Q hQ).toContinuousLinearEquiv

@[simp] theorem hermitianSylvester_apply (Q : selfAdjoint (Matrix n n ℂ))
    (hQ : (Q : Matrix n n ℂ).PosDef) (X : selfAdjoint (Matrix n n ℂ)) :
    (hermitianSylvester Q hQ X : Matrix n n ℂ) =
      (Q : Matrix n n ℂ) * X + (X : Matrix n n ℂ) * Q := rfl

@[simp] theorem hermitianSylvester_symm_apply (Q : selfAdjoint (Matrix n n ℂ))
    (hQ : (Q : Matrix n n ℂ).PosDef) (X : selfAdjoint (Matrix n n ℂ)) :
    ((hermitianSylvester Q hQ).symm X : Matrix n n ℂ) =
      (sylvesterEquiv Q hQ).symm X := rfl

theorem hasStrictFDerivAt_hermitianSquare (Q : selfAdjoint (Matrix n n ℂ))
    (hQ : (Q : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (𝕜 := ℝ) hermitianSquare
      (hermitianSylvester Q hQ : selfAdjoint (Matrix n n ℂ) →L[ℝ]
        selfAdjoint (Matrix n n ℂ)) Q := by
  have hi := (hermitianInclusion (n := n)).hasStrictFDerivAt (x := Q)
  have hm := hi.fun_mul' hi
  have hp := (hermitianProjection (n := n)).hasStrictFDerivAt.comp Q hm
  have heq : (hermitianSylvester Q hQ : selfAdjoint (Matrix n n ℂ) →L[ℝ]
      selfAdjoint (Matrix n n ℂ)) =
      hermitianProjection.comp
        (hermitianInclusion Q • hermitianInclusion +
          MulOpposite.op (hermitianInclusion Q) • hermitianInclusion) := by
    apply ContinuousLinearMap.ext
    intro X
    apply Subtype.ext
    change (Q : Matrix n n ℂ) * (X : Matrix n n ℂ) + (X : Matrix n n ℂ) * Q =
      ((selfAdjointPart ℝ ((Q : Matrix n n ℂ) * X + (X : Matrix n n ℂ) * Q)) :
        Matrix n n ℂ)
    symm
    apply IsSelfAdjoint.coe_selfAdjointPart_apply
    change ((Q : Matrix n n ℂ) * (X : Matrix n n ℂ) +
      (X : Matrix n n ℂ) * (Q : Matrix n n ℂ))ᴴ = _
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      show (Q : Matrix n n ℂ)ᴴ = Q from Q.property,
      show (X : Matrix n n ℂ)ᴴ = X from X.property]
    exact add_comm _ _
  rw [heq]
  exact hp

/-- Positive definite matrices have a Hermitian neighborhood of nonnegative matrices.
This uses a strictly positive spectral lower bound and the C-star norm order bound. -/
theorem eventually_nonneg_of_posDef (Q : selfAdjoint (Matrix n n ℂ))
    (hQ : (Q : Matrix n n ℂ).PosDef) :
    ∀ᶠ X : selfAdjoint (Matrix n n ℂ) in 𝓝 Q, 0 ≤ (X : Matrix n n ℂ) := by
  rcases subsingleton_or_nontrivial (Matrix n n ℂ) with h | h
  · letI := h
    exact Filter.Eventually.of_forall fun X => by
      rw [Subsingleton.elim (X : Matrix n n ℂ) 0]
  · letI := h
    have hstrict : IsStrictlyPositive (Q : Matrix n n ℂ) :=
      IsStrictlyPositive.iff_of_unital.mpr ⟨hQ.posSemidef.nonneg, hQ.isUnit⟩
    obtain ⟨r, hr, hrQ⟩ := (CFC.exists_pos_algebraMap_le_iff Q.property).mpr
      ((StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (Q : Matrix n n ℂ)).mp hstrict)
    refine Metric.eventually_nhds_iff.mpr ⟨r, hr, ?_⟩
    intro X hX
    have hdist : ‖(X : Matrix n n ℂ) - (Q : Matrix n n ℂ)‖ < r := by
      simpa only [dist_eq_norm] using hX
    have hlow := (IsSelfAdjoint.sub X.property Q.property).neg_algebraMap_norm_le_self
    have hmap : algebraMap ℝ (Matrix n n ℂ) ‖(X : Matrix n n ℂ) - Q‖ ≤
        algebraMap ℝ (Matrix n n ℂ) r := by
      simp only [Algebra.algebraMap_eq_smul_one]
      exact smul_le_smul_of_nonneg_right hdist.le zero_le_one
    calc
      0 = algebraMap ℝ (Matrix n n ℂ) r - algebraMap ℝ (Matrix n n ℂ) r :=
        (sub_self _).symm
      _ ≤ algebraMap ℝ (Matrix n n ℂ) r -
          algebraMap ℝ (Matrix n n ℂ) ‖(X : Matrix n n ℂ) - Q‖ :=
        sub_le_sub_left hmap _
      _ ≤ (Q : Matrix n n ℂ) + ((X : Matrix n n ℂ) - Q) :=
        add_le_add hrQ hlow
      _ = X := by abel

theorem hermitianSqrt_square_of_nonneg (Q : selfAdjoint (Matrix n n ℂ))
    (hQ : 0 ≤ (Q : Matrix n n ℂ)) : hermitianSqrt (hermitianSquare Q) = Q := by
  apply Subtype.ext
  simp only [hermitianSqrt_coe, hermitianSquare_coe]
  exact CFC.sqrt_mul_self _ hQ

theorem hermitianSquare_sqrt_of_nonneg (S : selfAdjoint (Matrix n n ℂ))
    (hS : 0 ≤ (S : Matrix n n ℂ)) : hermitianSquare (hermitianSqrt S) = S := by
  apply Subtype.ext
  simp only [hermitianSquare_coe, hermitianSqrt_coe]
  exact CFC.sqrt_mul_sqrt_self _ hS

/-- The square root is the local inverse of squaring near every positive definite root. -/
theorem hasStrictFDerivAt_hermitianSqrt_of_square (Q : selfAdjoint (Matrix n n ℂ))
    (hQ : (Q : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (𝕜 := ℝ) hermitianSqrt
      ((hermitianSylvester Q hQ).symm : selfAdjoint (Matrix n n ℂ) →L[ℝ]
        selfAdjoint (Matrix n n ℂ)) (hermitianSquare Q) := by
  apply (hasStrictFDerivAt_hermitianSquare Q hQ).to_local_left_inverse
  exact (eventually_nonneg_of_posDef Q hQ).mono fun X hX =>
    hermitianSqrt_square_of_nonneg X hX

/-- At a positive definite matrix, the strict derivative of the actual square root is the
inverse of `X ↦ sqrt(S) X + X sqrt(S)` on the real Hermitian space. -/
theorem hasStrictFDerivAt_hermitianSqrt (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (𝕜 := ℝ) hermitianSqrt
      ((hermitianSylvester (hermitianSqrt S) hS.posDef_sqrt).symm :
        selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ)) S := by
  have h := hasStrictFDerivAt_hermitianSqrt_of_square (hermitianSqrt S) hS.posDef_sqrt
  rwa [hermitianSquare_sqrt_of_nonneg S hS.posSemidef.nonneg] at h

theorem hasFDerivAt_hermitianSqrt (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    HasFDerivAt (𝕜 := ℝ) hermitianSqrt
      ((hermitianSylvester (hermitianSqrt S) hS.posDef_sqrt).symm :
        selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ)) S :=
  (hasStrictFDerivAt_hermitianSqrt S hS).hasFDerivAt

theorem fderiv_hermitianSqrt_eq (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ hermitianSqrt S =
      ((hermitianSylvester (hermitianSqrt S) hS.posDef_sqrt).symm :
        selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ)) :=
  (hasFDerivAt_hermitianSqrt S hS).fderiv

/-- The computed derivative solves the physical Sylvester equation in every Hermitian direction. -/
theorem fderiv_hermitianSqrt_solve (S H : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    CFC.sqrt (S : Matrix n n ℂ) * (fderiv ℝ hermitianSqrt S H : Matrix n n ℂ) +
        (fderiv ℝ hermitianSqrt S H : Matrix n n ℂ) * CFC.sqrt (S : Matrix n n ℂ) = H := by
  rw [fderiv_hermitianSqrt_eq S hS]
  exact sylvester_inverse_solve (CFC.sqrt (S : Matrix n n ℂ)) hS.posDef_sqrt H

/-- Squaring on the Hermitian space is smooth of every finite order. -/
theorem contDiff_hermitianSquare :
    ContDiff ℝ ∞ (hermitianSquare (n := n)) :=
  (hermitianProjection (n := n)).contDiff.comp
    ((hermitianInclusion (n := n)).contDiff.mul (hermitianInclusion (n := n)).contDiff)

/-- The inverse function theorem also supplies all higher derivatives of the actual square root. -/
theorem contDiffAt_hermitianSqrt_of_square (Q : selfAdjoint (Matrix n n ℂ))
    (hQ : (Q : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ hermitianSqrt (hermitianSquare Q) := by
  have hf := (contDiff_hermitianSquare (n := n)).contDiffAt (x := Q)
  have hf' := (hasStrictFDerivAt_hermitianSquare Q hQ).hasFDerivAt
  have hn : (1 : WithTop ℕ∞) ≤ ∞ := by simp
  have ht := hf.to_localInverse hf' hn
  have heq := (hf.hasStrictFDerivAt' hf' hn).localInverse_unique
    ((eventually_nonneg_of_posDef Q hQ).mono fun X hX =>
      hermitianSqrt_square_of_nonneg X hX)
  exact ht.congr_of_eventuallyEq heq

theorem contDiffAt_hermitianSqrt (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) : ContDiffAt ℝ ∞ hermitianSqrt S := by
  have h := contDiffAt_hermitianSqrt_of_square (hermitianSqrt S) hS.posDef_sqrt
  rwa [hermitianSquare_sqrt_of_nonneg S hS.posSemidef.nonneg] at h

end

end MatrixSpencer
