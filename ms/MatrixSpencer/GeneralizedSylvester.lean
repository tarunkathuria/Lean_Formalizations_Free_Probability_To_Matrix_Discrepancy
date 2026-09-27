import MatrixSpencer.TransportDerivative

/-!
# The generalized transport Sylvester inverse

Congruence by `sqrt M` changes `U ↦ T M U + U M T` into the positive Sylvester
operator with coefficient `sqrt M T sqrt M`.
-/

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

namespace MatrixSpencer

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance generalizedSylvesterCStarAlgebra : CStarAlgebra (Matrix n n ℂ) := {}
local instance generalizedSylvesterNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstance
local instance generalizedSylvesterFiniteDimensional :
    FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

def transportSylvesterCore (M T : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt M * T * CFC.sqrt M

theorem transportSylvesterCore_posDef (M T : Matrix n n ℂ)
    (hM : M.PosDef) (hT : T.PosDef) : (transportSylvesterCore M T).PosDef := by
  have hi : Function.Injective (CFC.sqrt M).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hM.posDef_sqrt.isUnit
  simpa only [transportSylvesterCore, hM.posDef_sqrt.isHermitian.eq] using
    hT.conjTranspose_mul_mul_same hi

/-- The actual continuous generalized Sylvester equivalence on the full Hermitian space. -/
def transportSylvesterEquiv (M T : Matrix n n ℂ) (hM : M.PosDef) (hT : T.PosDef) :
    selfAdjoint (Matrix n n ℂ) ≃L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  (((hermitianCongruenceEquiv (CFC.sqrt M) hM.posDef_sqrt).trans
      (sylvesterHermitianEquiv (transportSylvesterCore M T)
        (transportSylvesterCore_posDef M T hM hT))).trans
      (hermitianCongruenceEquiv (CFC.sqrt M) hM.posDef_sqrt).symm).toContinuousLinearEquiv

theorem transportSylvesterEquiv_apply (M T : Matrix n n ℂ)
    (hM : M.PosDef) (hT : T.PosDef) (X : selfAdjoint (Matrix n n ℂ)) :
    (transportSylvesterEquiv M T hM hT X : Matrix n n ℂ) =
      T * M * (X : Matrix n n ℂ) + (X : Matrix n n ℂ) * M * T := by
  let Q := CFC.sqrt M
  have hi := Matrix.nonsing_inv_mul Q (Q.isUnit_iff_isUnit_det.mp hM.posDef_sqrt.isUnit)
  have hir := Matrix.mul_nonsing_inv Q (Q.isUnit_iff_isUnit_det.mp hM.posDef_sqrt.isUnit)
  have hsq : Q * Q = M := CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg
  change Q⁻¹ * ((Q * T * Q) * (Q * (X : Matrix n n ℂ) * Q) +
    (Q * (X : Matrix n n ℂ) * Q) * (Q * T * Q)) * Q⁻¹ = _
  calc
    _ = (Q⁻¹ * Q) * T * (Q * Q) * (X : Matrix n n ℂ) * (Q * Q⁻¹) +
        (Q⁻¹ * Q) * (X : Matrix n n ℂ) * (Q * Q) * T * (Q * Q⁻¹) := by noncomm_ring
    _ = _ := by rw [hi, hir, hsq]; simp only [Matrix.one_mul, Matrix.mul_one]

theorem transportSylvesterEquiv_symm_solve (M T : Matrix n n ℂ)
    (hM : M.PosDef) (hT : T.PosDef) (B : selfAdjoint (Matrix n n ℂ)) :
    T * M * ((transportSylvesterEquiv M T hM hT).symm B : Matrix n n ℂ) +
      ((transportSylvesterEquiv M T hM hT).symm B : Matrix n n ℂ) * M * T = B := by
  rw [← transportSylvesterEquiv_apply M T hM hT]
  exact congrArg (fun X : selfAdjoint (Matrix n n ℂ) => (X : Matrix n n ℂ))
    ((transportSylvesterEquiv M T hM hT).apply_symm_apply B)

theorem transportSylvesterEquiv_symm_apply (M T : Matrix n n ℂ)
    (hM : M.PosDef) (hT : T.PosDef) (B : selfAdjoint (Matrix n n ℂ)) :
    ((transportSylvesterEquiv M T hM hT).symm B : Matrix n n ℂ) =
      (CFC.sqrt M)⁻¹ *
        (sylvesterEquiv (transportSylvesterCore M T)
          (transportSylvesterCore_posDef M T hM hT)).symm
          (CFC.sqrt M * (B : Matrix n n ℂ) * CFC.sqrt M) * (CFC.sqrt M)⁻¹ := rfl

theorem jointTransportOptimizer_isHermitian
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) :
    (jointTransportOptimizer P).IsHermitian := by
  have hq := (CFC.sqrt_nonneg (P.1 : Matrix n n ℂ)).posSemidef.isHermitian
  have hc : (fidelityCore (P.1 : Matrix n n ℂ) (P.2 : Matrix n n ℂ)).IsHermitian :=
    (CFC.sqrt_nonneg _).posSemidef.isHermitian
  change (CFC.sqrt (P.1 : Matrix n n ℂ) *
    (fidelityCore (P.1 : Matrix n n ℂ) (P.2 : Matrix n n ℂ))⁻¹ *
    CFC.sqrt (P.1 : Matrix n n ℂ))ᴴ = _
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
    hq.eq, hc.eq]
  simp only [jointTransportOptimizer, transportOptimizer, Matrix.mul_assoc]

/-- The optimizer with its natural Hermitian range. -/
def jointHermitianTransport
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix n n ℂ) :=
  ⟨jointTransportOptimizer P, jointTransportOptimizer_isHermitian P⟩

theorem contDiffAt_jointHermitianTransport (S M : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ jointHermitianTransport (S, M) := by
  have heq : jointHermitianTransport = hermitianProjection (n := n) ∘ jointTransportOptimizer := by
    funext P
    apply Subtype.ext
    exact (IsSelfAdjoint.coe_selfAdjointPart_apply ℝ
      (jointTransportOptimizer_isHermitian P)).symm
  rw [heq]
  exact (hermitianProjection (n := n)).contDiff.contDiffAt.comp (S, M)
    (contDiffAt_jointTransportOptimizer S M hS hM)

theorem fderiv_jointHermitianTransport_coe (S M δS δM : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef) :
    (fderiv ℝ jointHermitianTransport (S, M) (δS, δM) : Matrix n n ℂ) =
      fderiv ℝ jointTransportOptimizer (S, M) (δS, δM) := by
  have h := (hermitianInclusion (n := n)).hasFDerivAt.comp (S, M)
    (((contDiffAt_jointHermitianTransport S M hS hM).differentiableAt
      (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt)
  exact congrArg (fun L => L (δS, δM)) h.fderiv.symm

def transportResidual (T : Matrix n n ℂ) (hT : T.IsHermitian)
    (X Y : selfAdjoint (Matrix n n ℂ)) : selfAdjoint (Matrix n n ℂ) :=
  ⟨(X : Matrix n n ℂ) - T * (Y : Matrix n n ℂ) * T, by
    change ((X : Matrix n n ℂ) - T * (Y : Matrix n n ℂ) * T)ᴴ = _
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hT.eq,
      show (X : Matrix n n ℂ)ᴴ = X from X.property,
      show (Y : Matrix n n ℂ)ᴴ = Y from Y.property, Matrix.mul_assoc]⟩

/-- The actual transport derivative equals the proved generalized Sylvester inverse
applied to the actual joint residual. -/
theorem fderiv_jointHermitianTransport_eq (S M δS δM : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef) :
    fderiv ℝ jointHermitianTransport (S, M) (δS, δM) =
      (transportSylvesterEquiv (M : Matrix n n ℂ)
        (transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ)) hM
        (transportOptimizer_posDef hS hM)).symm
        (transportResidual _ (transportOptimizer_posDef hS hM).isHermitian δS δM) := by
  apply (transportSylvesterEquiv (M : Matrix n n ℂ)
    (transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ)) hM
    (transportOptimizer_posDef hS hM)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [transportSylvesterEquiv_apply, fderiv_jointHermitianTransport_coe S M δS δM hS hM]
  have h := fderiv_jointTransportOptimizer_solve S M δS δM hS hM
  change _ = (δS : Matrix n n ℂ) -
    transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ) * (δM : Matrix n n ℂ) *
      transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ)
  exact (add_comm _ _).trans h

end

end MatrixSpencer
