import MatrixSpencer.GeneralizedSylvester

/-!
# The actual joint fidelity Hessian

The gradient is differentiated through the smooth constructed transport matrix.
The differentiated transport equation then gives the exact quadratic form.
-/

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

namespace MatrixSpencer

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance fidelityHessianCStarAlgebra : CStarAlgebra (Matrix n n ℂ) := {}
local instance fidelityHessianNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstance
local instance fidelityHessianFiniteDimensional :
    FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

def jointTraceFunctional :
    (Matrix n n ℂ × Matrix n n ℂ) →L[ℝ]
      ((selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) →L[ℝ] ℝ) :=
  ({ toFun := fun A => (tracePairing A.1).comp (ContinuousLinearMap.fst ℝ _ _) +
       (tracePairing A.2).comp (ContinuousLinearMap.snd ℝ _ _)
     map_add' := by
       intro A B
       apply ContinuousLinearMap.ext
       intro X
       change realTrace ((A.1 + B.1) * (X.1 : Matrix n n ℂ)) +
         realTrace ((A.2 + B.2) * (X.2 : Matrix n n ℂ)) = _
       simp only [Matrix.add_mul, realTrace_add]
       change _ = (realTrace (A.1 * (X.1 : Matrix n n ℂ)) +
         realTrace (A.2 * (X.2 : Matrix n n ℂ))) +
         (realTrace (B.1 * (X.1 : Matrix n n ℂ)) + realTrace (B.2 * (X.2 : Matrix n n ℂ)))
       ring
     map_smul' := by
       intro r A
       apply ContinuousLinearMap.ext
       intro X
       change realTrace ((r • A.1) * (X.1 : Matrix n n ℂ)) +
         realTrace ((r • A.2) * (X.2 : Matrix n n ℂ)) = _
       simp only [Matrix.smul_mul, realTrace_smul]
       change _ = r * (realTrace (A.1 * (X.1 : Matrix n n ℂ)) +
         realTrace (A.2 * (X.2 : Matrix n n ℂ)))
       ring } : (Matrix n n ℂ × Matrix n n ℂ) →ₗ[ℝ]
       ((selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) →L[ℝ] ℝ)).toContinuousLinearMap

def transportFunctionalDerivative (T : Matrix n n ℂ) :
    Matrix n n ℂ →L[ℝ]
      ((selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) →L[ℝ] ℝ) :=
  jointTraceFunctional.comp
    ((-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) T⁻¹ T⁻¹).prod
      (ContinuousLinearMap.id ℝ (Matrix n n ℂ)))

theorem hasStrictFDerivAt_jointTransportFunctional (T : Matrix n n ℂ) (hT : IsUnit T) :
    HasStrictFDerivAt (jointTransportFunctional (n := n)) (transportFunctionalDerivative T) T := by
  have hfunc : jointTransportFunctional (n := n) =
      fun A : Matrix n n ℂ => jointTraceFunctional (A⁻¹, A) := by
    funext A
    rfl
  rw [hfunc]
  have hp : HasStrictFDerivAt (fun A : Matrix n n ℂ => (A⁻¹, A))
      ((-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) T⁻¹ T⁻¹).prod
        (ContinuousLinearMap.id ℝ (Matrix n n ℂ))) T :=
    (hasStrictFDerivAt_matrixInverse T hT).prodMk (hasStrictFDerivAt_id T)
  exact (jointTraceFunctional (n := n)).hasStrictFDerivAt.comp T hp

/-- The actual gradient of doubled fidelity is strictly differentiable on positive-definite pairs. -/
theorem hasStrictFDerivAt_fderiv_doubleFidelity (S M : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (fun P => fderiv ℝ (doubleFidelity (n := n)) P)
      ((transportFunctionalDerivative
        (transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ))).comp
        (fderiv ℝ jointTransportOptimizer (S, M))) (S, M) := by
  have ht := (contDiffAt_jointTransportOptimizer S M hS hM).hasStrictFDerivAt (by simp)
  have hg := (hasStrictFDerivAt_jointTransportFunctional _
    (transportOptimizer_posDef hS hM).isUnit).comp (S, M) ht
  apply hg.congr_of_eventuallyEq
  have hs := (continuous_fst.continuousAt (x := (S, M))).eventually
    (eventually_posDef_of_posDef S hS)
  have hm := (continuous_snd.continuousAt (x := (S, M))).eventually
    (eventually_posDef_of_posDef M hM)
  filter_upwards [hs, hm] with P hP₁ hP₂
  exact (hasFDerivAt_doubleFidelity P.1 P.2 hP₁ hP₂).fderiv.symm

theorem fderiv_fderiv_doubleFidelity_apply
    (S M X Y X' Y' : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef) :
    let T := transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ)
    let U := fderiv ℝ jointTransportOptimizer (S, M) (X, Y)
    fderiv ℝ (fun P => fderiv ℝ (doubleFidelity (n := n)) P) (S, M) (X, Y) (X', Y') =
      -realTrace (T⁻¹ * U * T⁻¹ * (X' : Matrix n n ℂ)) +
        realTrace (U * (Y' : Matrix n n ℂ)) := by
  rw [(hasStrictFDerivAt_fderiv_doubleFidelity S M hS hM).hasFDerivAt.fderiv]
  change realTrace ((-((transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ))⁻¹ *
      fderiv ℝ jointTransportOptimizer (S, M) (X, Y) *
      (transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ))⁻¹)) *
        (X' : Matrix n n ℂ)) + _ = _
  simp only [Matrix.neg_mul, realTrace_neg]
  rfl

theorem fidelityHessian_transport_identity (M T U X Y : Matrix n n ℂ)
    (hT : IsUnit T) (hres : U * M * T + T * M * U = X - T * Y * T) :
    -realTrace (T⁻¹ * U * T⁻¹ * X) + realTrace (U * Y) =
      -2 * realTrace (T⁻¹ * U * M * U) := by
  have hi := Matrix.nonsing_inv_mul T (T.isUnit_iff_isUnit_det.mp hT)
  have hir := Matrix.mul_nonsing_inv T (T.isUnit_iff_isUnit_det.mp hT)
  have hx : X = U * M * T + T * M * U + T * Y * T := by
    rw [hres]
    abel
  have h₁ : realTrace (T⁻¹ * U * T⁻¹ * (U * M * T)) =
      realTrace (T⁻¹ * U * M * U) := by
    calc
      _ = realTrace ((T⁻¹ * U * T⁻¹ * U * M) * T) := by simp only [Matrix.mul_assoc]
      _ = realTrace (T * (T⁻¹ * U * T⁻¹ * U * M)) := realTrace_mul_comm _ _
      _ = realTrace (U * T⁻¹ * U * M) := by
        calc
          _ = realTrace ((T * T⁻¹) * U * T⁻¹ * U * M) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hir, Matrix.one_mul]
      _ = realTrace (T⁻¹ * U * M * U) := by
        simpa only [Matrix.mul_assoc] using realTrace_mul_comm U (T⁻¹ * U * M)
  have h₂ : realTrace (T⁻¹ * U * T⁻¹ * (T * M * U)) =
      realTrace (T⁻¹ * U * M * U) := by
    congr 1
    calc
      _ = T⁻¹ * U * (T⁻¹ * T) * M * U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hi, Matrix.mul_one]
  have h₃ : realTrace (T⁻¹ * U * T⁻¹ * (T * Y * T)) = realTrace (U * Y) := by
    calc
      _ = realTrace (T⁻¹ * U * (T⁻¹ * T) * Y * T) := by simp only [Matrix.mul_assoc]
      _ = realTrace (T⁻¹ * U * Y * T) := by rw [hi, Matrix.mul_one]
      _ = realTrace (T * (T⁻¹ * U * Y)) := realTrace_mul_comm _ _
      _ = realTrace (U * Y) := by
        calc
          _ = realTrace ((T * T⁻¹) * U * Y) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hir, Matrix.one_mul]
  rw [hx, Matrix.mul_add, Matrix.mul_add, realTrace_add, realTrace_add, h₁, h₂, h₃]
  ring

/-- The exact joint Hessian quadratic form of doubled fidelity. -/
theorem fderiv_fderiv_doubleFidelity_quadratic
    (S M X Y : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef) :
    let T := transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ)
    let U := fderiv ℝ jointTransportOptimizer (S, M) (X, Y)
    fderiv ℝ (fun P => fderiv ℝ (doubleFidelity (n := n)) P) (S, M) (X, Y) (X, Y) =
      -2 * realTrace (T⁻¹ * U * (M : Matrix n n ℂ) * U) := by
  rw [fderiv_fderiv_doubleFidelity_apply S M X Y X Y hS hM]
  exact fidelityHessian_transport_identity _ _ _ _ _
    (transportOptimizer_posDef hS hM).isUnit
    (fderiv_jointTransportOptimizer_solve S M X Y hS hM)

theorem fderiv_fderiv_doubleFidelity_quadratic_nonpos
    (S M X Y : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef) :
    fderiv ℝ (fun P => fderiv ℝ (doubleFidelity (n := n)) P)
      (S, M) (X, Y) (X, Y) ≤ 0 := by
  let T := transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ)
  let U := fderiv ℝ jointTransportOptimizer (S, M) (X, Y)
  have hU : U.IsHermitian := by
    change (fderiv ℝ jointTransportOptimizer (S, M) (X, Y)).IsHermitian
    rw [← fderiv_jointHermitianTransport_coe S M X Y hS hM]
    exact (fderiv ℝ jointHermitianTransport (S, M) (X, Y)).property
  have hUMU : (U * (M : Matrix n n ℂ) * U).PosSemidef := by
    simpa only [hU.eq] using hM.posSemidef.conjTranspose_mul_mul_same U
  have hn := realTrace_mul_nonneg (transportOptimizer_posDef hS hM).inv.posSemidef hUMU
  rw [fderiv_fderiv_doubleFidelity_quadratic S M X Y hS hM]
  change -2 * realTrace (T⁻¹ * U * (M : Matrix n n ℂ) * U) ≤ 0
  have hn' : 0 ≤ realTrace (T⁻¹ * U * (M : Matrix n n ℂ) * U) := by
    simpa only [Matrix.mul_assoc] using hn
  linarith

end

end MatrixSpencer
