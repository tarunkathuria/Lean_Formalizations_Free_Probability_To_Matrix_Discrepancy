import MatrixSpencer.TsallisHessian
import MatrixSpencer.TransportVariational
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The joint fidelity derivative

Smoothness comes from the actual positive square-root formula. The exact derivative
then follows from Fermat's theorem applied to the attained transport upper bound.
-/

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

namespace MatrixSpencer

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance fidelityDerivativeCStarAlgebra : CStarAlgebra (Matrix n n ℂ) := {}

local instance fidelityDerivativeNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

local instance fidelityDerivativeFiniteDimensional : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

/-- The Hermitian matrix inside the fidelity square root. -/
def jointFidelitySandwich
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix n n ℂ) :=
  hermitianProjection ((hermitianSqrt P.1 : Matrix n n ℂ) * P.2 * hermitianSqrt P.1)

theorem jointFidelitySandwich_coe
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) :
    (jointFidelitySandwich P : Matrix n n ℂ) =
      CFC.sqrt (P.1 : Matrix n n ℂ) * (P.2 : Matrix n n ℂ) *
        CFC.sqrt (P.1 : Matrix n n ℂ) := by
  apply IsSelfAdjoint.coe_selfAdjointPart_apply
  change (CFC.sqrt (P.1 : Matrix n n ℂ) * (P.2 : Matrix n n ℂ) *
    CFC.sqrt (P.1 : Matrix n n ℂ))ᴴ = _
  simp only [Matrix.conjTranspose_mul,
    (CFC.sqrt_nonneg (P.1 : Matrix n n ℂ)).posSemidef.isHermitian.eq,
    show (P.2 : Matrix n n ℂ)ᴴ = P.2 from P.2.property, Matrix.mul_assoc]
  rfl

theorem jointFidelitySandwich_posDef (S M : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef) :
    (jointFidelitySandwich (S, M) : Matrix n n ℂ).PosDef := by
  rw [jointFidelitySandwich_coe]
  have hi : Function.Injective (CFC.sqrt (S : Matrix n n ℂ)).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hS.posDef_sqrt.isUnit
  simpa only [hS.posDef_sqrt.isHermitian.eq] using hM.conjTranspose_mul_mul_same hi

theorem contDiffAt_jointFidelitySandwich (S M : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ jointFidelitySandwich (S, M) := by
  have hs := (hermitianInclusion (n := n)).contDiff.contDiffAt.comp (S, M)
    ((contDiffAt_hermitianSqrt S hS).comp (S, M) contDiffAt_fst)
  have hm : ContDiffAt ℝ ∞
      (fun P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ) =>
        (P.2 : Matrix n n ℂ)) (S, M) :=
    (hermitianInclusion (n := n)).contDiff.contDiffAt.comp (S, M) contDiffAt_snd
  exact (hermitianProjection (n := n)).contDiff.contDiffAt.comp (S, M) ((hs.mul hm).mul hs)

def doubleFidelity (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) : ℝ :=
  2 * fidelity (P.1 : Matrix n n ℂ) (P.2 : Matrix n n ℂ)

theorem doubleFidelity_eq_traceSqrt
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) :
    doubleFidelity P = 2 * traceSqrt (jointFidelitySandwich P) := by
  simp only [doubleFidelity, fidelity, fidelityCore, traceSqrt, jointFidelitySandwich_coe]

theorem contDiffAt_doubleFidelity (S M : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ doubleFidelity (S, M) := by
  have ht := (realTraceCLM (n := n)).contDiff.contDiffAt.comp (jointFidelitySandwich (S, M))
    ((hermitianInclusion (n := n)).contDiff.contDiffAt.comp (jointFidelitySandwich (S, M))
      (contDiffAt_hermitianSqrt _ (jointFidelitySandwich_posDef S M hS hM)))
  have hc := (contDiffAt_const (c := (2 : ℝ))).mul
    (ht.comp (S, M) (contDiffAt_jointFidelitySandwich S M hS))
  rw [show doubleFidelity = fun P : selfAdjoint (Matrix n n ℂ) ×
      selfAdjoint (Matrix n n ℂ) => 2 * traceSqrt (jointFidelitySandwich P) from
    funext doubleFidelity_eq_traceSqrt]
  exact hc

/-- The affine transport cost, as a functional of the two Hermitian inputs. -/
def jointTransportFunctional (T : Matrix n n ℂ) :
    (selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) →L[ℝ] ℝ :=
  (tracePairing T⁻¹).comp (ContinuousLinearMap.fst ℝ _ _) +
    (tracePairing T).comp (ContinuousLinearMap.snd ℝ _ _)

@[simp] theorem jointTransportFunctional_apply (T : Matrix n n ℂ)
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) :
    jointTransportFunctional T P =
      realTrace (T⁻¹ * (P.1 : Matrix n n ℂ)) + realTrace (T * (P.2 : Matrix n n ℂ)) := rfl

theorem jointTransportFunctional_eq_cost (T : Matrix n n ℂ)
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) :
    jointTransportFunctional T P = transportCost P.1 P.2 T := by
  rw [jointTransportFunctional_apply, transportCost,
    realTrace_mul_comm T⁻¹ (P.1 : Matrix n n ℂ), realTrace_mul_comm T (P.2 : Matrix n n ℂ)]

/-- The attained transport majorant gives the joint fidelity derivative by Fermat's theorem. -/
theorem hasFDerivAt_doubleFidelity (S M : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef) :
    HasFDerivAt doubleFidelity
      (jointTransportFunctional (transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ)))
      (S, M) := by
  let T := transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ)
  let L := jointTransportFunctional T
  have hT : T.PosDef := transportOptimizer_posDef hS hM
  have hfd := ((contDiffAt_doubleFidelity S M hS hM).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  have hmin : IsLocalMin (fun P => L P - doubleFidelity P) (S, M) := by
    have hs : ∀ᶠ P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)
        in 𝓝 (S, M), (P.1 : Matrix n n ℂ).PosDef :=
      (continuous_fst.continuousAt (x := (S, M))).eventually
        (eventually_posDef_of_posDef S hS)
    have hm : ∀ᶠ P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)
        in 𝓝 (S, M), (P.2 : Matrix n n ℂ).PosDef :=
      (continuous_snd.continuousAt (x := (S, M))).eventually
        (eventually_posDef_of_posDef M hM)
    have h0 : L (S, M) = doubleFidelity (S, M) := by
      change jointTransportFunctional T (S, M) =
        2 * fidelity (S : Matrix n n ℂ) (M : Matrix n n ℂ)
      rw [jointTransportFunctional_eq_cost,
        transportCost_at_transport hT (transportOptimizer_solve hS hM),
        trace_transportOptimizer_eq_fidelity hS hM]
    filter_upwards [hs, hm] with P hP₁ hP₂
    change L (S, M) - doubleFidelity (S, M) ≤ L P - doubleFidelity P
    rw [h0, sub_self]
    apply sub_nonneg.mpr
    obtain ⟨_, _, _, hbound⟩ := fidelity_variational_posDef hP₁ hP₂
    exact (jointTransportFunctional_eq_cost T P).symm ▸ hbound T hT
  have hz := hmin.hasFDerivAt_eq_zero (L.hasFDerivAt.sub hfd)
  rwa [← sub_eq_zero.mp hz] at hfd

theorem hasStrictFDerivAt_doubleFidelity (S M : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt doubleFidelity
      (jointTransportFunctional (transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ)))
      (S, M) :=
  (contDiffAt_doubleFidelity S M hS hM).hasStrictFDerivAt'
    (hasFDerivAt_doubleFidelity S M hS hM) (by simp)

/-- In a joint direction `(δS,δM)`, the derivative is exactly
`Tr(T⁻¹ δS) + Tr(T δM)` for the explicitly constructed transport matrix. -/
theorem fderiv_doubleFidelity_apply (S M δS δM : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef) :
    fderiv ℝ doubleFidelity (S, M) (δS, δM) =
      realTrace ((transportOptimizer (S : Matrix n n ℂ) M)⁻¹ * (δS : Matrix n n ℂ)) +
        realTrace (transportOptimizer (S : Matrix n n ℂ) M * (δM : Matrix n n ℂ)) := by
  rw [(hasFDerivAt_doubleFidelity S M hS hM).fderiv]
  rfl

end

end MatrixSpencer
