import MatrixSpencer.FidelityDerivative

/-!
# Differentiating the constructed transport optimizer

The explicit optimizer is smooth on positive definite input pairs. Differentiating
its proved transport equation gives the Sylvester equation for its actual derivative.
-/

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

namespace MatrixSpencer

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance transportDerivativeCStarAlgebra : CStarAlgebra (Matrix n n ℂ) := {}
local instance transportDerivativeNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstance
local instance transportDerivativeFiniteDimensional :
    FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

theorem contDiffAt_matrixInverse (Q : Matrix n n ℂ) (hQ : IsUnit Q) :
    ContDiffAt ℝ ∞ (fun A : Matrix n n ℂ => A⁻¹) Q := by
  rcases hQ with ⟨u, rfl⟩
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using (contDiffAt_ringInverse ℝ u)

def jointFidelityCore
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix n n ℂ) := hermitianSqrt (jointFidelitySandwich P)

theorem jointFidelityCore_coe
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) :
    (jointFidelityCore P : Matrix n n ℂ) =
      fidelityCore (P.1 : Matrix n n ℂ) (P.2 : Matrix n n ℂ) := by
  simp only [jointFidelityCore, hermitianSqrt_coe, jointFidelitySandwich_coe, fidelityCore]

theorem contDiffAt_jointFidelityCore (S M : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ jointFidelityCore (S, M) :=
  (contDiffAt_hermitianSqrt _ (jointFidelitySandwich_posDef S M hS hM)).comp (S, M)
    (contDiffAt_jointFidelitySandwich S M hS)

def jointTransportOptimizer
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ :=
  transportOptimizer (P.1 : Matrix n n ℂ) (P.2 : Matrix n n ℂ)

theorem contDiffAt_jointTransportOptimizer (S M : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ jointTransportOptimizer (S, M) := by
  have hs := (hermitianInclusion (n := n)).contDiff.contDiffAt.comp (S, M)
    ((contDiffAt_hermitianSqrt S hS).comp (S, M) contDiffAt_fst)
  have hc := (hermitianInclusion (n := n)).contDiff.contDiffAt.comp (S, M)
    (contDiffAt_jointFidelityCore S M hS hM)
  have hp : (jointFidelityCore (S, M) : Matrix n n ℂ).PosDef := by
    rw [jointFidelityCore_coe]
    exact fidelityCore_posDef hS hM
  have hi := (contDiffAt_matrixInverse _ hp.isUnit).comp (S, M) hc
  have ht := (hs.mul hi).mul hs
  have heq : jointTransportOptimizer =
      fun P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ) =>
        (hermitianSqrt P.1 : Matrix n n ℂ) * (jointFidelityCore P : Matrix n n ℂ)⁻¹ *
          (hermitianSqrt P.1 : Matrix n n ℂ) := by
    funext P
    simp only [jointTransportOptimizer, transportOptimizer, jointFidelityCore_coe,
      hermitianSqrt_coe]
  rw [heq]
  exact ht

/-- The actual derivative of the explicit transport optimizer solves the differentiated
transport equation, with no assumed derivative or inverse. -/
theorem fderiv_jointTransportOptimizer_solve (S M δS δM : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef) :
    let T := transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ)
    let U := fderiv ℝ jointTransportOptimizer (S, M) (δS, δM)
    U * (M : Matrix n n ℂ) * T + T * (M : Matrix n n ℂ) * U =
      (δS : Matrix n n ℂ) - T * (δM : Matrix n n ℂ) * T := by
  let T := transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ)
  let U := fderiv ℝ jointTransportOptimizer (S, M) (δS, δM)
  have ht := ((contDiffAt_jointTransportOptimizer S M hS hM).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  let F : (selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) →L[ℝ]
      Matrix n n ℂ := hermitianInclusion.comp (ContinuousLinearMap.fst ℝ _ _)
  let G : (selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) →L[ℝ]
      Matrix n n ℂ := hermitianInclusion.comp (ContinuousLinearMap.snd ℝ _ _)
  have hg := G.hasFDerivAt (x := (S, M))
  have hall := (ht.fun_mul' hg).fun_mul' ht
  have heq : (fun P => F P) =ᶠ[𝓝 (S, M)]
      (fun P => jointTransportOptimizer P * G P * jointTransportOptimizer P) := by
    have hs := (continuous_fst.continuousAt (x := (S, M))).eventually
      (eventually_posDef_of_posDef S hS)
    have hm := (continuous_snd.continuousAt (x := (S, M))).eventually
      (eventually_posDef_of_posDef M hM)
    filter_upwards [hs, hm] with P hP₁ hP₂
    exact (transportOptimizer_solve hP₁ hP₂).symm
  have he := (hall.congr_of_eventuallyEq heq).fderiv
  rw [F.hasFDerivAt.fderiv] at he
  have happ := congrArg (fun L => L (δS, δM)) he
  change (δS : Matrix n n ℂ) = T * (M : Matrix n n ℂ) * U +
    (T * (δM : Matrix n n ℂ) + U * (M : Matrix n n ℂ)) * T at happ
  change U * (M : Matrix n n ℂ) * T + T * (M : Matrix n n ℂ) * U =
    (δS : Matrix n n ℂ) - T * (δM : Matrix n n ℂ) * T
  rw [happ]
  noncomm_ring

end

end MatrixSpencer
