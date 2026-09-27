import HigherRankKS.PowerIntegralRepresentation
import HigherRankKS.WeightedCompactIntegral
import HigherRankKS.ResolventDerivatives

/-!
# Differentiation of the fractional matrix-power resolvent integral

A compact parameter makes the normalized resolvent a smooth element of a
Banach algebra. Bounded linear weighted integration then commutes with its
actual derivatives. The scalar representing measure is known to exist.
-/

open Matrix MatrixSpencer Set Filter MeasureTheory
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator unitInterval ContDiff

noncomputable section
namespace HigherRankKS.PowerIntegralDerivatives

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

open PowerIntegralRepresentation WeightedCompactIntegral

def leftCoeff : C(I, Matrix n n ℂ) := ⟨fun a => (a : ℝ) • 1, by fun_prop⟩
def rightCoeff : C(I, Matrix n n ℂ) := ⟨fun a => (1 - (a : ℝ)) • 1, by fun_prop⟩
def functionDenominator (M : Matrix n n ℂ) : C(I, Matrix n n ℂ) :=
  leftCoeff + rightCoeff * ContinuousMap.const I M

def functionKernel (M : Matrix n n ℂ) : C(I, Matrix n n ℂ) :=
  ContinuousMap.const I M * Ring.inverse (functionDenominator M)

theorem functionDenominator_apply (M : Matrix n n ℂ) (a : I) :
    functionDenominator M a = (a : ℝ) • 1 + (1 - (a : ℝ)) • M := by
  simp [functionDenominator, leftCoeff, rightCoeff]

theorem functionDenominator_isUnit {M : Matrix n n ℂ} (hM : M.PosDef) :
    IsUnit (functionDenominator M) := by
  apply (ContinuousMap.isUnit_iff_forall_isUnit _).mpr
  intro a
  rw [functionDenominator_apply]
  exact (posDef_convex_mixture Matrix.PosDef.one hM a.property.1
    (sub_nonneg.mpr a.property.2) (by ring)).isUnit

theorem analyticAt_functionDenominator (M : Matrix n n ℂ) :
    AnalyticAt ℝ functionDenominator M := by
  exact analyticAt_const.add (analyticAt_const.mul
    ((ContinuousLinearMap.const ℝ I : Matrix n n ℂ →L[ℝ] C(I, Matrix n n ℂ)).analyticAt M))

theorem analyticAt_functionKernel {M : Matrix n n ℂ} (hM : M.PosDef) :
    AnalyticAt ℝ functionKernel M := by
  have hi : AnalyticAt ℝ Ring.inverse (functionDenominator M) :=
    analyticOnNhd_inverse _ (functionDenominator_isUnit hM)
  exact (ContinuousLinearMap.const ℝ I : Matrix n n ℂ →L[ℝ] C(I, Matrix n n ℂ)).analyticAt M |>.mul
    (hi.comp (f := functionDenominator) (analyticAt_functionDenominator M))

theorem functionKernel_apply {M : Matrix n n ℂ} (hM : M.PosDef) (a : I) :
    functionKernel M a = M * ((a : ℝ) • 1 + (1 - (a : ℝ)) • M)⁻¹ := by
  have hunit := functionDenominator_isUnit hM
  have hi : Ring.inverse (functionDenominator M) a =
      Ring.inverse (functionDenominator M a) := by
    have hu := (ContinuousMap.isUnit_iff_forall_isUnit _).mp hunit a
    have he := congrArg (fun f : C(I, Matrix n n ℂ) => f a)
      (Ring.inverse_mul_cancel (functionDenominator M) hunit)
    simpa using (Ring.eq_mul_inverse_iff_mul_eq _ 1 _ hu).mpr he
  simp only [functionKernel, ContinuousMap.mul_apply, ContinuousMap.const_apply, hi,
    functionDenominator_apply, Matrix.nonsing_inv_eq_ringInverse]

theorem functionKernel_parameter {M : Matrix n n ℂ} (hM : M.PosDef)
    {t : ℝ} (ht : 0 < t) :
    functionKernel M (parameter t) = (1 + t) • resolventKernel M t := by
  have hp : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have hQ := hM.add_posSemidef
    (smul_nonneg ht.le (Matrix.PosDef.one.posSemidef.nonneg)).posSemidef
  rw [functionKernel_apply hM, parameter_coe ht]
  have hscalar : 1 - t / (1 + t) = (1 + t)⁻¹ := by field_simp; ring
  have hden : (t / (1 + t)) • (1 : Matrix n n ℂ) + (1 - t / (1 + t)) • M =
      (1 + t)⁻¹ • (M + t • 1) := by
    rw [hscalar, smul_add, smul_smul, div_eq_mul_inv, mul_comm t]
    exact add_comm _ _
  rw [hden, inv_real_smul hQ.isUnit (inv_ne_zero hp), inv_inv,
    Matrix.mul_smul, resolventKernel_eq_mul hM ht.le]
  rfl

theorem weight_cancel {α t : ℝ} (hα : α ∈ Ioo 0 1) (ht : 0 < t) :
    Real.rpowIntegrand₀₁ α t 1 * (1 + t) = t ^ (α - 1) := by
  rw [Real.rpowIntegrand₀₁_eq_pow_div hα ht.le zero_le_one, mul_one,
    add_comm 1 t, div_mul_cancel₀ _ (ne_of_gt (by linarith : 0 < t + 1))]

theorem power_eq_integralCLM {α : ℝ} (hα : α ∈ Ioo 0 1) (μ : Measure ℝ)
    (hμ : ScalarRepresentation α μ) {M : Matrix n n ℂ} (hM : M.PosDef) :
    CFC.rpow M α = integralCLM (μ.restrict (Ioi 0))
      (fun t => Real.rpowIntegrand₀₁ α t 1) (hμ 1 zero_le_one).1 (functionKernel M) := by
  rw [(resolvent_representation hα μ hμ M hM.posSemidef).2, integralCLM_apply]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [functionKernel_parameter hM ht, smul_smul, weight_cancel hα ht,
    resolventKernel_eq_mul hM ht.le]
  rfl

/-- The compact kernel is smooth along every affine matrix line. -/
theorem contDiffAt_functionKernel_curve {M : Matrix n n ℂ} (hM : M.PosDef)
    (U : Matrix n n ℂ) (k : ℕ) :
    ContDiffAt ℝ k (fun s : ℝ => functionKernel (M + s • U)) 0 := by
  have hline : ContDiffAt ℝ k (fun s : ℝ => M + s • U) 0 :=
    contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hk : ContDiffAt ℝ k functionKernel (M + (0 : ℝ) • U) := by
    simpa using (analyticAt_functionKernel hM).contDiffAt
  exact hk.comp 0 hline

theorem power_curve_eventuallyEq_integral {α : ℝ} (hα : α ∈ Ioo 0 1)
    (μ : Measure ℝ) (hμ : ScalarRepresentation α μ)
    {M U : Matrix n n ℂ} (hM : M.PosDef) (hU : U.IsHermitian) :
    (fun s : ℝ => CFC.rpow (M + s • U) α) =ᶠ[𝓝 0]
      (fun s => integralCLM (μ.restrict (Ioi 0))
        (fun t => Real.rpowIntegrand₀₁ α t 1) (hμ 1 zero_le_one).1
        (functionKernel (M + s • U))) := by
  filter_upwards [KSMovingOwnerHessian.eventually_posDef_transportLine hM hU] with s hs
  exact power_eq_integralCLM hα μ hμ hs

/-- Smoothness of the actual CFC power along a Hermitian direction,
proved from the compact resolvent integral. -/
theorem contDiffAt_power_curve {α : ℝ} (hα : α ∈ Ioo 0 1)
    {M U : Matrix n n ℂ} (hM : M.PosDef) (hU : U.IsHermitian) (k : ℕ) :
    ContDiffAt ℝ k (fun s : ℝ => CFC.rpow (M + s • U) α) 0 := by
  obtain ⟨μ, hμ⟩ := exists_scalarRepresentation hα
  let L : C(I, Matrix n n ℂ) →L[ℝ] Matrix n n ℂ :=
    integralCLM (μ.restrict (Ioi 0)) (fun t => Real.rpowIntegrand₀₁ α t 1)
      (hμ 1 zero_le_one).1
  have hh : ContDiffAt ℝ k (fun s : ℝ => L (functionKernel (M + s • U))) 0 :=
    L.contDiff.contDiffAt.comp 0 (contDiffAt_functionKernel_curve hM U k)
  exact hh.congr_of_eventuallyEq (power_curve_eventuallyEq_integral hα μ hμ hM hU)

theorem contDiffAt_resolventKernel_curve {M : Matrix n n ℂ} (hM : M.PosDef)
    (U : Matrix n n ℂ) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    ContDiffAt ℝ k (fun s : ℝ => resolventKernel (M + s • U) t) 0 := by
  let Q := M + t • (1 : Matrix n n ℂ)
  have hQ : Q.PosDef := hM.add_posSemidef
    (smul_nonneg ht (Matrix.PosDef.one.posSemidef.nonneg)).posSemidef
  have hi := KSMovingOwnerHessian.contDiffAt_inverseLine Q U hQ.isUnit
  have hi' : ContDiffAt ℝ k (KSMovingOwnerHessian.inverseLine Q U) 0 :=
    hi.of_le (by
      change ((k : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  simpa only [resolventKernel, resolvent, Q, KSMovingOwnerHessian.inverseLine,
    KSMovingOwnerHessian.transportLine, add_right_comm] using
    (contDiffAt_const.sub (hi'.const_smul t) :
      ContDiffAt ℝ k (fun s => (1 : Matrix n n ℂ) - t • KSMovingOwnerHessian.inverseLine Q U s) 0)

/-- The normalized compact integrand has the same derivatives as its
explicit scalar multiple of the usual resolvent kernel. -/
theorem iteratedDeriv_functionKernel_parameter {M U : Matrix n n ℂ}
    (hM : M.PosDef) (hU : U.IsHermitian) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    iteratedDeriv k (fun s : ℝ => functionKernel (M + s • U) (parameter t)) 0 =
      (1 + t) • iteratedDeriv k (fun s : ℝ => resolventKernel (M + s • U) t) 0 := by
  have he : (fun s : ℝ => functionKernel (M + s • U) (parameter t)) =ᶠ[𝓝 0]
      (fun s => (1 + t) • resolventKernel (M + s • U) t) := by
    filter_upwards [KSMovingOwnerHessian.eventually_posDef_transportLine hM hU] with s hs
    exact functionKernel_parameter hs ht
  rw [he.iteratedDeriv_eq k]
  exact iteratedDeriv_const_smul (contDiffAt_resolventKernel_curve hM U ht.le k) (1 + t)

/-- All finite directional derivatives may be passed through the actual
fractional-power integral; integrability is part of the conclusion. -/
theorem iteratedDeriv_power_integral {α : ℝ} (hα : α ∈ Ioo 0 1)
    (μ : Measure ℝ) (hμ : ScalarRepresentation α μ)
    {M U : Matrix n n ℂ} (hM : M.PosDef) (hU : U.IsHermitian) (k : ℕ) :
    IntegrableOn (fun t => t ^ (α - 1) •
      iteratedDeriv k (fun s : ℝ => resolventKernel (M + s • U) t) 0) (Ioi 0) μ ∧
    iteratedDeriv k (fun s : ℝ => CFC.rpow (M + s • U) α) 0 =
      ∫ t in Ioi 0, t ^ (α - 1) •
        iteratedDeriv k (fun s : ℝ => resolventKernel (M + s • U) t) 0 ∂μ := by
  have hk := contDiffAt_functionKernel_curve hM U k
  have he : (fun t => Real.rpowIntegrand₀₁ α t 1 •
      iteratedDeriv k (fun s : ℝ => functionKernel (M + s • U) (parameter t)) 0)
      =ᶠ[ae (μ.restrict (Ioi 0))] (fun t => t ^ (α - 1) •
        iteratedDeriv k (fun s : ℝ => resolventKernel (M + s • U) t) 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [iteratedDeriv_functionKernel_parameter hM hU ht k, smul_smul, weight_cancel hα ht]
  refine ⟨(integrable_iteratedDeriv _ _ (hμ 1 zero_le_one).1 hk).congr he, ?_⟩
  rw [(power_curve_eventuallyEq_integral hα μ hμ hM hU).iteratedDeriv_eq k,
    iteratedDeriv_integral _ _ (hμ 1 zero_le_one).1 hk]
  exact integral_congr_ae he

/-- Explicit first resolvent derivative, including its Bochner
integrability on the entire positive half-line. -/
theorem deriv_power_integral {α : ℝ} (hα : α ∈ Ioo 0 1)
    (μ : Measure ℝ) (hμ : ScalarRepresentation α μ)
    {M U : Matrix n n ℂ} (hM : M.PosDef) (hU : U.IsHermitian) :
    IntegrableOn (fun t => t ^ α • (resolvent M t * U * resolvent M t)) (Ioi 0) μ ∧
    deriv (fun s : ℝ => CFC.rpow (M + s • U) α) 0 =
      ∫ t in Ioi 0, t ^ α • (resolvent M t * U * resolvent M t) ∂μ := by
  have h := iteratedDeriv_power_integral hα μ hμ hM hU 1
  have he : (fun t => t ^ (α - 1) •
      iteratedDeriv 1 (fun s : ℝ => resolventKernel (M + s • U) t) 0)
      =ᶠ[ae (μ.restrict (Ioi 0))]
      (fun t => t ^ α • (resolvent M t * U * resolvent M t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [iteratedDeriv_one, (hasDerivAt_resolventKernel_curve hM U ht.le).deriv,
      smul_smul, Real.rpow_sub_one ht.ne', div_mul_cancel₀ _ ht.ne']
  refine ⟨h.1.congr he, ?_⟩
  simpa only [iteratedDeriv_one] using h.2.trans (integral_congr_ae he)

/-- The actual derivative of the CFC power is given by the resolvent
integral; no differentiation-under-integral premise is required. -/
theorem hasDerivAt_power_integral {α : ℝ} (hα : α ∈ Ioo 0 1)
    (μ : Measure ℝ) (hμ : ScalarRepresentation α μ)
    {M U : Matrix n n ℂ} (hM : M.PosDef) (hU : U.IsHermitian) :
    HasDerivAt (fun s : ℝ => CFC.rpow (M + s • U) α)
      (∫ t in Ioi 0, t ^ α • (resolvent M t * U * resolvent M t) ∂μ) 0 := by
  rw [← (deriv_power_integral hα μ hμ hM hU).2]
  exact ((contDiffAt_power_curve hα hM hU 1).differentiableAt (by norm_num)).hasDerivAt

/-- Explicit second resolvent derivative, including integrability.
Its negative is the positive Gram integrand used in the source metric. -/
theorem iteratedDeriv_two_power_integral {α : ℝ} (hα : α ∈ Ioo 0 1)
    (μ : Measure ℝ) (hμ : ScalarRepresentation α μ)
    {M U : Matrix n n ℂ} (hM : M.PosDef) (hU : U.IsHermitian) :
    IntegrableOn (fun t => (-2 * t ^ α) •
      (resolvent M t * U * resolvent M t * U * resolvent M t)) (Ioi 0) μ ∧
    iteratedDeriv 2 (fun s : ℝ => CFC.rpow (M + s • U) α) 0 =
      ∫ t in Ioi 0, (-2 * t ^ α) •
        (resolvent M t * U * resolvent M t * U * resolvent M t) ∂μ := by
  have h := iteratedDeriv_power_integral hα μ hμ hM hU 2
  have he : (fun t => t ^ (α - 1) •
      iteratedDeriv 2 (fun s : ℝ => resolventKernel (M + s • U) t) 0)
      =ᶠ[ae (μ.restrict (Ioi 0))]
      (fun t => (-2 * t ^ α) •
        (resolvent M t * U * resolvent M t * U * resolvent M t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [iteratedDeriv_two_resolventKernel_curve hM U ht.le, smul_smul,
      Real.rpow_sub_one ht.ne']
    congr 1
    have ht0 : 0 < t := ht
    field_simp [ht0.ne']
  exact ⟨h.1.congr he, h.2.trans (integral_congr_ae he)⟩

/-- Every fractional power is smooth on the open positive-definite cone
of the real vector space of Hermitian matrices. -/
theorem contDiffAt_power {α : ℝ} (hα : α ∈ Ioo 0 1)
    (M : selfAdjoint (Matrix n n ℂ)) (hM : (M : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (fun X : selfAdjoint (Matrix n n ℂ) =>
      CFC.rpow (X : Matrix n n ℂ) α) M := by
  obtain ⟨μ, hμ⟩ := exists_scalarRepresentation hα
  let L : C(I, Matrix n n ℂ) →L[ℝ] Matrix n n ℂ :=
    integralCLM (μ.restrict (Ioi 0)) (fun t => Real.rpowIntegrand₀₁ α t 1)
      (hμ 1 zero_le_one).1
  have hk : ContDiffAt ℝ ∞ (fun X : selfAdjoint (Matrix n n ℂ) =>
      functionKernel (X : Matrix n n ℂ)) M :=
    (analyticAt_functionKernel hM).contDiffAt.comp M
      (hermitianInclusion (n := n)).contDiff.contDiffAt
  have hh : ContDiffAt ℝ ∞ (fun X : selfAdjoint (Matrix n n ℂ) =>
      L (functionKernel (X : Matrix n n ℂ))) M := L.contDiff.contDiffAt.comp M hk
  apply hh.congr_of_eventuallyEq
  filter_upwards [eventually_posDef_of_posDef M hM] with X hX
  exact power_eq_integralCLM hα μ hμ hX

end HigherRankKS.PowerIntegralDerivatives
