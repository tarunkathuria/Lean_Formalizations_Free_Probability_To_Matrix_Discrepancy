import MatrixSpencer.RectangularRidgePotentialResponse
import MatrixSpencer.RectangularRidgeCoercivity

/-! Uniform center-only curvature of the actual mixed optimum. This permits
supporting tangent evaluations by finite value differences, without obtaining
an exact primal optimizer from the convex solver. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeCenterCurvature
open RectangularRidgeCalculus
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance ridgeCenterCurvatureCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeCenterCurvatureRealSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeCenterCurvatureTangentGroup : NormedAddCommGroup (densityTangent (n:=n)) := inferInstance
local instance ridgeCenterCurvatureTangentSpace : NormedSpace ℝ (densityTangent (n:=n)) := inferInstance
local instance ridgeCenterCurvatureDualGroup : NormedAddCommGroup (densityTangent (n:=n) →L[ℝ] ℝ) := inferInstance
local instance ridgeCenterCurvatureDualSpace : NormedSpace ℝ (densityTangent (n:=n) →L[ℝ] ℝ) := inferInstance

theorem response_frobenius_le (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1≤m) {θ κ : ℝ} (hθ : 0<θ) (hκ : 0<κ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (htr : realTrace (S : Matrix n n ℂ)=1) (X : selfAdjoint (Matrix n n ℂ)) :
    let U := responseDerivative H B m hm θ κ hθ hκ S hS X
    Real.sqrt (realTrace ((U : Matrix n n ℂ)*(U : Matrix n n ℂ))) ≤
      (2/κ)*Real.sqrt (realTrace ((X : Matrix n n ℂ)*(X : Matrix n n ℂ))) := by
  let U := (tangentHessianEquiv H B m hm θ κ hθ hκ S hS).symm (densityCenterFunctional X)
  have hrep : negativeHessian H B m θ κ S U U = densityCenterFunctional X U := by
    change tangentHessianEquiv H B m hm θ κ hθ hκ S hS U U = _
    dsimp only [U]
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hl := negativeHessian_coercive H B m hm hθ hκ S U hS htr
  rw [hrep] at hl
  change κ/2*realTrace ((((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))*
    (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))) ≤
      realTrace ((X : Matrix n n ℂ)*(((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))) at hl
  have hc := (le_abs_self _).trans (KSOptimizerInverseBound.trace_pairing_le_frobenius X U)
  have hUtr : 0≤realTrace ((((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))*
      (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))) := by
    have he : (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))ᴴ=U :=
      (U : selfAdjoint (Matrix n n ℂ)).property
    simpa only [he] using realTrace_conjTranspose_mul_self_nonneg
      (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))
  let u := Real.sqrt (realTrace ((((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))*
      (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))))
  let x := Real.sqrt (realTrace ((X : Matrix n n ℂ)*(X : Matrix n n ℂ)))
  have hs : u^2 = _ := Real.sq_sqrt hUtr
  have hineq : κ/2*u^2≤x*u := by nlinarith
  change u≤(2/κ)*x
  by_cases hu : u=0
  · rw [hu]
    positivity
  · have hup : 0<u := (Real.sqrt_nonneg _).lt_of_ne' hu
    have hux : u≤(2*x)/κ := (le_div_iff₀ hκ).mpr (by nlinarith)
    exact hux.trans_eq (by ring)

theorem potential_hessian_abs_le [Nonempty n] (H X : selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1≤m) {θ κ R : ℝ}
    (hθ : 0<θ) (hκ : 0<κ) (hR : 0≤R)
    (hX : Real.sqrt (realTrace ((X : Matrix n n ℂ)*(X : Matrix n n ℂ)))≤R) :
    |fderiv ℝ (fderiv ℝ (hermitianPotential B m θ κ)) H X X|≤(2/κ)*R^2 := by
  rw [fderiv_fderiv_hermitianPotential_apply H X X B m hm θ κ hθ hκ]
  let S := hermitianOptimizer (H : Matrix n n ℂ) B m θ κ
  let hp := hermitianOptimizer_posDef (H : Matrix n n ℂ) B m hm θ κ hθ hκ
  let U := responseDerivative (H : Matrix n n ℂ) B m hm θ κ hθ hκ S hp X
  have hu := response_frobenius_le (H : Matrix n n ℂ) B m hm hθ hκ S hp
    (hermitianOptimizer_trace (H : Matrix n n ℂ) B m θ κ) X
  have hh := KSOptimizerInverseBound.trace_pairing_le_frobenius U X
  apply hh.trans
  have ht := mul_le_mul_of_nonneg_right hu
    (Real.sqrt_nonneg (realTrace ((X : Matrix n n ℂ)*(X : Matrix n n ℂ))))
  have hx : (Real.sqrt (realTrace ((X : Matrix n n ℂ)*(X : Matrix n n ℂ))))^2≤R^2 := by
    nlinarith [Real.sqrt_nonneg (realTrace ((X : Matrix n n ℂ)*(X : Matrix n n ℂ)))]
  have hs := mul_le_mul_of_nonneg_left hx (by positivity : (0:ℝ)≤2/κ)
  nlinarith

end MatrixSpencer.RectangularRidgeCenterCurvature
