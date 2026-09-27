import MatrixSpencer.KSCompactResolvent
import MatrixSpencer.KSScalarRootIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

/-!
# The compact scalar resolvent integral is the principal square root

An explicit arctangent computation gives the positive-real seed. The identity
principle on the slit plane then identifies the constructed analytic integral
with `z ^ (1/2)`, including its exact square-root norm. No integral identity or
holomorphic extension is supplied as a hypothesis.
-/

open Set MeasureTheory
open scoped Topology unitInterval
noncomputable section
namespace MatrixSpencer.KSScalarHolomorphicRoot
open KSCompactResolvent

/-- The scalar denominator avoids zero throughout the real compact interval. -/
theorem denominator_ne_zero {z : ℂ} (hz : z ∈ Complex.slitPlane) (a : ℝ) :
    (a : ℂ)^2 + (1-(a : ℂ))^2*z ≠ 0 := by
  intro he
  by_cases ha : a = 1
  · simp [ha] at he
  have hb : 0 < (1-a)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm ha))
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  have hzim : z.im = 0 := him.resolve_left (sub_ne_zero.mpr (Ne.symm ha))
  have hzre : z.re ≤ 0 := by nlinarith [sq_nonneg a]
  simp [Complex.mem_slitPlane_iff, hzim, not_lt.mpr hzre] at hz

theorem functionDenominator_isUnit {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    IsUnit (functionDenominator ℂ z) := by
  apply (ContinuousMap.isUnit_iff_forall_isUnit _).mpr
  intro a
  rw [functionDenominator_apply]
  simpa [smul_eq_mul] using (isUnit_iff_ne_zero.mpr (denominator_ne_zero hz (a : ℝ)))

theorem analyticAt_integral {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (rootIntegral ℂ) z :=
  analyticAt_rootIntegral ℂ (functionDenominator_isUnit hz)

def principalRoot (z : ℂ) : ℂ := z ^ (1/2 : ℂ)

theorem analyticAt_principalRoot {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    AnalyticAt ℂ principalRoot z :=
  analyticAt_id.cpow analyticAt_const hz

theorem principalRoot_ofReal {x : ℝ} (hx : 0 ≤ x) :
    principalRoot (x : ℂ) = (Real.sqrt x : ℂ) := by
  rw [principalRoot, Real.sqrt_eq_rpow]
  convert (Complex.ofReal_cpow hx (1/2 : ℝ)).symm using 1; norm_num

theorem integral_ofReal {x : ℝ} (hx : 0 < x) :
    rootIntegral ℂ (x : ℂ) = principalRoot (x : ℂ) := by
  have hz : (x : ℂ) ∈ Complex.slitPlane := by
    simp [Complex.mem_slitPlane_iff, hx]
  rw [rootIntegral_eq_interval ℂ (functionDenominator_isUnit hz), principalRoot_ofReal hx.le]
  push_cast
  simpa only [smul_eq_mul, mul_one, Ring.inverse_eq_inv, div_eq_mul_inv] using KSScalarRootIntegral.normalized_complex_integral hx

/-- The scalar compact resolvent integral is the principal square root on the whole slit plane. -/
theorem integral_eq_principalRoot {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    rootIntegral ℂ z = principalRoot z := by
  have h1 : (1 : ℂ) ∈ Complex.slitPlane := by simp [Complex.mem_slitPlane_iff]
  apply AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
    (fun z hz => analyticAt_integral hz)
    (fun z hz => analyticAt_principalRoot hz)
    (Complex.starConvex_one_slitPlane.isPathConnected h1).isConnected.isPreconnected h1 ?_ hz
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  refine ⟨((1 + ε/2 : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
  · exact integral_ofReal (by linarith)
  · simp only [mem_singleton_iff]
    intro h
    have he := congrArg Complex.re h
    simp at he
    linarith
  · rw [dist_eq_norm]
    have he : ((1+ε/2 : ℝ) : ℂ) - 1 = ((ε/2 : ℝ) : ℂ) := by push_cast; ring
    rw [norm_sub_rev, he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ε/2)]
    linarith

theorem norm_principalRoot (z : ℂ) : ‖principalRoot z‖ = Real.sqrt ‖z‖ := by
  rw [principalRoot, Real.sqrt_eq_rpow]
  convert Complex.norm_cpow_real z (1/2 : ℝ) using 1; norm_num

end MatrixSpencer.KSScalarHolomorphicRoot
