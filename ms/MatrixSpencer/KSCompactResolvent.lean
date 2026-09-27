import MatrixSpencer.KSAccretiveProductDomain
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Holomorphic compact resolvent integrals

The compact interval of rational resolvents is packaged in the Banach algebra
of continuous functions on `[0,1]`. Pointwise invertibility makes it a unit in
that algebra, so inversion followed by bounded linear integration is analytic.
This constructs the auxiliary analytic extension; the integral itself uses
only real spectral parameters. Its identification with a trace square root
and the explicit value bound are supplied in subsequent modules.
-/

open Matrix Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace MatrixSpencer.KSCompactResolvent
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

def Domain (M : Matrix n n ℂ) : Prop := spectrum ℂ M ⊆ Complex.slitPlane

def denominator (M : Matrix n n ℂ) (a : ℝ) : Matrix n n ℂ :=
  ((a : ℂ)^2) • (1 : Matrix n n ℂ) + ((1-(a : ℂ))^2) • M

def kernel (M : Matrix n n ℂ) (a : ℝ) : Matrix n n ℂ :=
  M * (denominator M a)⁻¹

theorem nonpos_not_mem {M : Matrix n n ℂ} (hM : Domain M) {r : ℝ} (hr : r ≤ 0) :
    (r : ℂ) ∉ spectrum ℂ M := by
  intro h
  have := hM h
  simp [Complex.mem_slitPlane_iff, not_lt.mpr hr] at this

theorem denominator_isUnit {M : Matrix n n ℂ} (hM : Domain M) {a : ℝ}
    (_ha : a ∈ Icc (0 : ℝ) 1) : IsUnit (denominator M a) := by
  by_cases ha1 : a = 1
  · simp [denominator, ha1]
  have hb : (1-a)^2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm ha1))
  let r : ℝ := -(a^2) / (1-a)^2
  have hr : r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg a)) (sq_nonneg _)
  have hu := (spectrum.notMem_iff.mp (nonpos_not_mem hM hr)).neg
  have hbC : (1-(a : ℂ))^2 ≠ 0 := by exact_mod_cast hb
  have he : denominator M a = (Units.mk0 ((1-(a : ℂ))^2) hbC) •
      (-(algebraMap ℂ (Matrix n n ℂ) (r : ℂ) - M)) := by
    simp only [denominator, Units.smul_def, Units.val_mk0, neg_sub,
      Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul]
    have hrval : (1-a)^2 * r = -(a^2) := by
      dsimp [r]
      exact mul_div_cancel₀ _ hb
    have hc := congrArg Complex.ofReal hrval
    push_cast at hc
    rw [hc]
    module
  rw [he]
  exact hu.smul _

theorem analyticAt_kernel {M : Matrix n n ℂ} (hM : Domain M) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) : AnalyticAt ℂ (fun X => kernel X a) M := by
  have hd : AnalyticAt ℂ (fun X : Matrix n n ℂ => denominator X a) M := by
    exact analyticAt_const.add (analyticAt_id.const_smul (c := (1-(a : ℂ))^2))
  have hinv : AnalyticAt ℂ Ring.inverse (denominator M a) :=
    analyticOnNhd_inverse _ (denominator_isUnit hM ha)
  have hi := hinv.comp (f := fun X : Matrix n n ℂ => denominator X a) hd
  simpa only [kernel, Matrix.nonsing_inv_eq_ringInverse] using analyticAt_id.mul hi

section CompactAlgebra
open scoped unitInterval
variable (A : Type*) [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
private theorem integrable_continuousMap (f : C(I, A)) : Integrable f :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Integration on the compact unit interval, as a bounded complex-linear map. -/
def integralCLM : C(I, A) →L[ℂ] A :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ a : I, f a
      map_add' := fun f g => integral_add (integrable_continuousMap A f)
        (integrable_continuousMap A g)
      map_smul' := fun z f => integral_smul z f } 1 (by
        intro f
        have hh := norm_integral_le_of_norm_le_const
          (μ := (volume : Measure I)) (C := ‖f‖)
          (Filter.Eventually.of_forall fun a => ContinuousMap.norm_coe_le_norm f a)
        simpa using hh)

def alpha : C(I, A) := ⟨fun a => ((a : ℝ) : ℂ)^2 • (1 : A), by fun_prop⟩
def beta : C(I, A) := ⟨fun a => (1-((a : ℝ) : ℂ))^2 • (1 : A), by fun_prop⟩
def functionDenominator (M : A) : C(I, A) :=
  alpha A + beta A * ContinuousMap.const I M

def functionKernel (M : A) : C(I, A) :=
  ContinuousMap.const I M * Ring.inverse (functionDenominator A M)

def rootIntegral (M : A) : A :=
  ((2 / Real.pi : ℝ) : ℂ) • integralCLM A (functionKernel A M)

omit [CompleteSpace A] in
theorem analyticAt_functionDenominator (M : A) :
    AnalyticAt ℂ (functionDenominator A) M := by
  exact analyticAt_const.add (analyticAt_const.mul
    ((ContinuousLinearMap.const ℂ I : A →L[ℂ] C(I,A)).analyticAt M))

theorem analyticAt_functionKernel {M : A} (hM : IsUnit (functionDenominator A M)) :
    AnalyticAt ℂ (functionKernel A) M := by
  have hi : AnalyticAt ℂ Ring.inverse (functionDenominator A M) :=
    analyticOnNhd_inverse _ hM
  exact (ContinuousLinearMap.const ℂ I : A →L[ℂ] C(I,A)).analyticAt M |>.mul
    (hi.comp (f := functionDenominator A) (analyticAt_functionDenominator A M))

theorem analyticAt_rootIntegral {M : A} (hM : IsUnit (functionDenominator A M)) :
    AnalyticAt ℂ (rootIntegral A) M := by
  exact ((integralCLM A).analyticAt (functionKernel A M) |>.comp (f := functionKernel A)
    (analyticAt_functionKernel A hM)).const_smul

omit [CompleteSpace A] in
theorem functionDenominator_apply (M : A) (a : I) :
    functionDenominator A M a = ((a : ℝ) : ℂ)^2 • (1 : A) +
      (1-((a : ℝ) : ℂ))^2 • M := by
  simp [functionDenominator, alpha, beta]

theorem functionKernel_apply {M : A} (hM : IsUnit (functionDenominator A M)) (a : I) :
    functionKernel A M a = M * Ring.inverse (((a : ℝ) : ℂ)^2 • (1 : A) +
      (1-((a : ℝ) : ℂ))^2 • M) := by
  have hi : Ring.inverse (functionDenominator A M) a =
      Ring.inverse (functionDenominator A M a) := by
    have hunit := (ContinuousMap.isUnit_iff_forall_isUnit _).mp hM a
    have he := congrArg (fun f : C(I,A) => f a)
      (Ring.inverse_mul_cancel (functionDenominator A M) hM)
    simpa using (Ring.eq_mul_inverse_iff_mul_eq _ 1 _ hunit).mpr he
  simp only [functionKernel, ContinuousMap.mul_apply, ContinuousMap.const_apply, hi,
    functionDenominator_apply]

theorem rootIntegral_eq_interval {M : A} (hM : IsUnit (functionDenominator A M)) :
    rootIntegral A M = ((2 / Real.pi : ℝ) : ℂ) • ∫ a in (0 : ℝ)..1,
      M * Ring.inverse ((a : ℂ)^2 • (1 : A) + (1-(a : ℂ))^2 • M) := by
  unfold rootIntegral
  congr 1
  change (∫ a : I, functionKernel A M a) = _
  rw [integral_congr_ae (Filter.Eventually.of_forall (functionKernel_apply A hM))]
  have he := integral_subtype (s := Icc (0 : ℝ) 1) measurableSet_Icc
    (fun a : ℝ => M * Ring.inverse ((a : ℂ)^2 • (1 : A) + (1-(a : ℂ))^2 • M))
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one] at he
  exact he

end CompactAlgebra
open scoped unitInterval

theorem matrix_functionDenominator_isUnit {M : Matrix n n ℂ} (hM : Domain M) :
    IsUnit (functionDenominator (Matrix n n ℂ) M) := by
  apply (ContinuousMap.isUnit_iff_forall_isUnit _).mpr
  intro a
  simpa only [functionDenominator_apply, denominator] using denominator_isUnit hM a.property

theorem matrix_rootIntegral_analyticAt {M : Matrix n n ℂ} (hM : Domain M) :
    AnalyticAt ℂ (rootIntegral (Matrix n n ℂ)) M :=
  analyticAt_rootIntegral _ (matrix_functionDenominator_isUnit hM)

def traceCLM : Matrix n n ℂ →L[ℂ] ℂ :=
  (Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap

/-- Auxiliary trace-square-root extension, defined by a compact real resolvent integral. -/
def traceRoot (M : Matrix n n ℂ) : ℂ :=
  Matrix.trace (rootIntegral (Matrix n n ℂ) M)

theorem traceRoot_analyticAt {M : Matrix n n ℂ} (hM : Domain M) :
    AnalyticAt ℂ traceRoot M :=
  (traceCLM (n := n)).analyticAt _ |>.comp (f := rootIntegral (Matrix n n ℂ))
    (matrix_rootIntegral_analyticAt hM)

theorem traceRoot_eq_integral {M : Matrix n n ℂ} (hM : Domain M) :
    traceRoot M = (2 / (Real.pi : ℂ)) * ∫ a in (0 : ℝ)..1, Matrix.trace (kernel M a) := by
  have hm := matrix_functionDenominator_isUnit hM
  change traceCLM (rootIntegral (Matrix n n ℂ) M) = _
  unfold rootIntegral
  rw [map_smul]
  change ((2 / Real.pi : ℝ) : ℂ) • traceCLM
    (∫ a : I, functionKernel (Matrix n n ℂ) M a) = _
  rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_continuousMap _ _)]
  simp only [smul_eq_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  congr 1
  have he : (∫ a : I, traceCLM (functionKernel (Matrix n n ℂ) M a)) =
      ∫ a : I, Matrix.trace (kernel M a) := by
    apply integral_congr_ae
    filter_upwards [] with a
    rw [functionKernel_apply _ hm]
    change Matrix.trace (M * Ring.inverse _) = _
    rw [kernel, denominator, Matrix.nonsing_inv_eq_ringInverse]
  rw [he]
  have he' := integral_subtype (s := Icc (0 : ℝ) 1) measurableSet_Icc
    (fun a : ℝ => Matrix.trace (kernel M a))
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one] at he'
  exact he'

end MatrixSpencer.KSCompactResolvent
