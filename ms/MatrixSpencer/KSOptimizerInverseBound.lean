import MatrixSpencer.KSObjectiveUpper
import MatrixSpencer.OptimizerResponseUnrestricted

/-!
# Quantitative inverse bounds for the actual density optimizer

The actual constrained negative Hessian has inverse norm at most `2/θ`.
The first estimate uses the inherited physical operator norm and its Banach
dual; separate trace-square estimates give the genuine Frobenius response
bound, including for the derivative of the canonical optimizer. Sources
may be singular, and the optimizer endpoint supplies its own density
faithfulness and trace hypotheses.

These bounds supply the inverse factor in differentiated stationarity.
They do not establish a fourth-derivative bound for the outer optimized
potential: explicit mixed coefficient derivatives and higher envelope
identities are separate remaining analytic obligations.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSOptimizerInverseBound
set_option maxHeartbeats 800000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_le_inverse_coercivity (A : E ≃L[ℝ] (E →L[ℝ] ℝ))
    {g : ℝ} (hg : 0 < g) (hA : ∀ x, g * ‖x‖ ^ 2 ≤ A x x) (x : E) :
    ‖x‖ ≤ g⁻¹ * ‖A x‖ := by
  have hb : A x x ≤ ‖A x‖ * ‖x‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using (A x).le_opNorm x)
  have hl := hA x
  by_cases hx : ‖x‖ = 0
  · rw [hx]
    positivity
  · have hxpos : 0 < ‖x‖ := (norm_nonneg x).lt_of_ne' hx
    have hc : g * ‖x‖ ≤ ‖A x‖ := by nlinarith
    calc ‖x‖ = g⁻¹ * (g * ‖x‖) := by rw [← mul_assoc, inv_mul_cancel₀ hg.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hg.le)

/-- The actual inverse is quantitatively bounded from a proved coercivity
inequality, with the genuine Banach dual norm on the input. -/
theorem inverse_norm_le_of_coercivity (A : E ≃L[ℝ] (E →L[ℝ] ℝ))
    {g : ℝ} (hg : 0 < g) (hA : ∀ x, g * ‖x‖ ^ 2 ≤ A x x) :
    ‖A.symm.toContinuousLinearMap‖ ≤ g⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hg.le)
  intro f
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    norm_le_inverse_coercivity A hg hA (A.symm f)

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance : NormedAddCommGroup (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance

/-- Coercivity of the actual constrained Hessian in the inherited physical
operator norm, obtained from the stronger Frobenius lower bound. -/
theorem tangent_hessian_coercive (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (htr : realTrace (S : Matrix n n ℂ) = 1)
    (X : densityTangent (n := n)) :
    θ / 2 * ‖X‖ ^ 2 ≤ densityTangentHessianEquiv_source_unrestricted H B θ hθ S hS X X := by
  have hl := KSObjectiveCurvature.densityNegativeHessian_ge_of_density H B θ hθ S X hS htr
  have hn := KSObjectiveUpper.norm_sq_le_trace_square (show
    ((X : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ).IsHermitian from
      (X : selfAdjoint (Matrix n n ℂ)).property)
  exact (mul_le_mul_of_nonneg_left hn (div_nonneg hθ.le (by norm_num))).trans hl

/-- The actual inverse tangent Hessian has norm at most `2/θ`. The source may
be singular; no density spectral gap is required for this inverse estimate. -/
theorem tangent_hessian_inverse_norm_le (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (htr : realTrace (S : Matrix n n ℂ) = 1) :
    ‖(densityTangentHessianEquiv_source_unrestricted H B θ hθ S hS).symm.toContinuousLinearMap‖ ≤ 2 / θ := by
  have hh := inverse_norm_le_of_coercivity (E := densityTangent (n := n))
    (densityTangentHessianEquiv_source_unrestricted H B θ hθ S hS)
    (div_pos hθ (by norm_num)) (tangent_hessian_coercive H B θ hθ S hS htr)
  simpa only [inv_div] using hh

/-- At the canonical optimizer the density hypotheses are discharged. -/
theorem optimizer_hessian_inverse_norm_le [Nonempty n]
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    ‖(densityTangentHessianEquiv_source_unrestricted H B θ hθ
      (hermitianDensityOptimizer H B θ) (hermitianDensityOptimizer_posDef H B hθ)).symm.toContinuousLinearMap‖ ≤
      2 / θ :=
  tangent_hessian_inverse_norm_le H B θ hθ _ (hermitianDensityOptimizer_posDef H B hθ)
    (hermitianDensityOptimizer_trace H B θ)

/-- The explicit trace-square expression is the true Frobenius norm in the
full real Hilbert chart, not the matrix operator norm. -/
theorem sqrt_trace_square_eq_coordinate_norm (X : selfAdjoint (Matrix n n ℂ)) :
    Real.sqrt (realTrace ((X : Matrix n n ℂ) * (X : Matrix n n ℂ))) =
      ‖(KSFullHermitianChart.chartEquiv n).symm X‖ := by
  have he : KSFullHermitianChart.chart n ((KSFullHermitianChart.chartEquiv n).symm X) = X :=
    (KSFullHermitianChart.chartEquiv n).apply_symm_apply X
  have ht := KSFullHermitianChart.chart_trace_square n ((KSFullHermitianChart.chartEquiv n).symm X)
  rw [he] at ht
  rw [ht, Real.sqrt_sq (norm_nonneg _)]

theorem trace_pairing_le_frobenius (X Y : selfAdjoint (Matrix n n ℂ)) :
    |realTrace ((X : Matrix n n ℂ) * (Y : Matrix n n ℂ))| ≤
      Real.sqrt (realTrace ((X : Matrix n n ℂ) * (X : Matrix n n ℂ))) *
        Real.sqrt (realTrace ((Y : Matrix n n ℂ) * (Y : Matrix n n ℂ))) := by
  let x := (KSFullHermitianChart.chartEquiv n).symm X
  let y := (KSFullHermitianChart.chartEquiv n).symm Y
  have hx : KSFullHermitianChart.chart n x = X := (KSFullHermitianChart.chartEquiv n).apply_symm_apply X
  have hy : KSFullHermitianChart.chart n y = Y := (KSFullHermitianChart.chartEquiv n).apply_symm_apply Y
  have hp := KSFullHermitianChart.chart_trace_pairing n x y
  rw [hx, hy] at hp
  rw [hp, sqrt_trace_square_eq_coordinate_norm, sqrt_trace_square_eq_coordinate_norm]
  exact (by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) x y)

/-- An arbitrary mixed forcing can use the same actual inverse estimate
once its Frobenius dual bound is established. The bound on that forcing is
explicit here and is not asserted for the coefficient derivatives. -/
theorem tangent_response_frobenius_le_of_forcing
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (htr : realTrace (S : Matrix n n ℂ) = 1)
    (φ : densityTangent (n := n) →L[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hforce : ∀ X : densityTangent (n := n), |φ X| ≤ C * Real.sqrt
      (realTrace ((((X : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) *
        (((X : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))))) :
    let U := (densityTangentHessianEquiv_source_unrestricted H B θ hθ S hS).symm φ
    Real.sqrt (realTrace ((((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) *
      (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)))) ≤ (2 / θ) * C := by
  let U := (densityTangentHessianEquiv_source_unrestricted H B θ hθ S hS).symm φ
  let u := Real.sqrt (realTrace ((((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) *
      (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))))
  have hrep : densityTangentNegativeHessian H B θ S U U = φ U := by
    change densityTangentHessianEquiv_source_unrestricted H B θ hθ S hS U U = _
    dsimp only [U]
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hl := KSObjectiveCurvature.densityNegativeHessian_ge_of_density H B θ hθ S U hS htr
  change θ / 2 * realTrace ((((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) *
      (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))) ≤ densityTangentNegativeHessian H B θ S U U at hl
  rw [hrep] at hl
  have hf := (le_abs_self (φ U)).trans (hforce U)
  have htrU : 0 ≤ realTrace ((((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) *
      (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))) := by
    have he : (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))ᴴ = U :=
      (U : selfAdjoint (Matrix n n ℂ)).property
    simpa only [he] using realTrace_conjTranspose_mul_self_nonneg
      (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))
  have hs : u ^ 2 = _ := Real.sq_sqrt htrU
  change u ≤ (2 / θ) * C
  by_cases hu : u = 0
  · rw [hu]
    positivity
  · have hup : 0 < u := (Real.sqrt_nonneg _).lt_of_ne' hu
    have hh : θ * u ≤ 2 * C := by nlinarith
    have hu' : u ≤ (2 * C) / θ := (le_div_iff₀ hθ).mpr (by nlinarith)
    calc u ≤ (2 * C) / θ := hu'
      _ = (2 / θ) * C := by ring

/-- The actual constrained inverse response to a center forcing is bounded
in Frobenius norm by `2/θ`, uniformly in every faithful trace-one density. -/
theorem response_frobenius_le (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (htr : realTrace (S : Matrix n n ℂ) = 1)
    (X : selfAdjoint (Matrix n n ℂ)) :
    let U := densityResponseDerivative_source_unrestricted H B θ hθ S hS X
    Real.sqrt (realTrace ((U : Matrix n n ℂ) * (U : Matrix n n ℂ))) ≤
      (2 / θ) * Real.sqrt (realTrace ((X : Matrix n n ℂ) * (X : Matrix n n ℂ))) := by
  let U := (densityTangentHessianEquiv_source_unrestricted H B θ hθ S hS).symm (densityCenterFunctional X)
  have hrep : densityTangentNegativeHessian H B θ S U U = densityCenterFunctional X U := by
    change densityTangentHessianEquiv_source_unrestricted H B θ hθ S hS U U = _
    dsimp only [U]
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hl := KSObjectiveCurvature.densityNegativeHessian_ge_of_density H B θ hθ S U hS htr
  change θ / 2 * realTrace (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) *
    ((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) ≤ densityTangentNegativeHessian H B θ S U U at hl
  rw [hrep] at hl
  change θ / 2 * realTrace (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) *
    ((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) ≤
      realTrace ((X : Matrix n n ℂ) * ((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) at hl
  have hc := (le_abs_self _).trans (trace_pairing_le_frobenius X U)
  have hUtr : 0 ≤ realTrace (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) *
      ((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) := by
    have he : (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))ᴴ = U :=
      (U : selfAdjoint (Matrix n n ℂ)).property
    simpa only [he] using realTrace_conjTranspose_mul_self_nonneg
      (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))
  have hs := Real.sq_sqrt hUtr
  change Real.sqrt (realTrace (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) *
    ((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ))) ≤ _
  let u := Real.sqrt (realTrace (((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) *
    ((U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)))
  let x := Real.sqrt (realTrace ((X : Matrix n n ℂ) * (X : Matrix n n ℂ)))
  change θ / 2 * _ ≤ _ at hl
  have hineq : θ / 2 * u ^ 2 ≤ x * u := by nlinarith
  change u ≤ (2 / θ) * x
  by_cases hu : u = 0
  · rw [hu]
    positivity
  · have hup : 0 < u := (Real.sqrt_nonneg _).lt_of_ne' hu
    have hh : θ * u ≤ 2 * x := by nlinarith
    have hu' : u ≤ (2 * x) / θ := (le_div_iff₀ hθ).mpr (by nlinarith)
    calc u ≤ (2 * x) / θ := hu'
      _ = (2 / θ) * x := by ring

/-- This is a bound on the derivative of the actual canonical optimizer,
with all its faithfulness and trace hypotheses discharged. -/
theorem optimizer_derivative_frobenius_le [Nonempty n]
    (H X : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    let U := fderiv ℝ (fun K : selfAdjoint (Matrix n n ℂ) => hermitianDensityOptimizer (K : Matrix n n ℂ) B θ) H X
    Real.sqrt (realTrace ((U : Matrix n n ℂ) * (U : Matrix n n ℂ))) ≤
      (2 / θ) * Real.sqrt (realTrace ((X : Matrix n n ℂ) * (X : Matrix n n ℂ))) := by
  rw [(hasStrictFDerivAt_hermitianDensityOptimizer_source_unrestricted H B hθ).hasFDerivAt.fderiv]
  exact response_frobenius_le (H : Matrix n n ℂ) B θ hθ
    (hermitianDensityOptimizer (H : Matrix n n ℂ) B θ)
    (hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) B hθ)
    (hermitianDensityOptimizer_trace (H : Matrix n n ℂ) B θ) X

end MatrixSpencer.KSOptimizerInverseBound
