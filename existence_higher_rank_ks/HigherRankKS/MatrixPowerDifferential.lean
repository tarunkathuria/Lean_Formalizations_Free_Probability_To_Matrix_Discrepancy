import HigherRankKS.PowerIntegralDerivatives
import HigherRankKS.CarrierConcavity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open Matrix MatrixSpencer Set Filter MeasureTheory
open scoped Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS.MatrixPowerDifferential

section Homogeneity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem euler_first (f : E → F) (α : ℝ) (x : E)
    (hfd : DifferentiableAt ℝ f x)
    (hhom : ∀ t : ℝ, 0 < t → f (t • x) = t ^ α • f x) :
    fderiv ℝ f x x = α • f x := by
  have hleft : HasDerivAt (fun t : ℝ => f (t • x)) (fderiv ℝ f x x) 1 := by
    have hd : HasFDerivAt f (fderiv ℝ f x) ((1 : ℝ) • x) := by simpa using hfd.hasFDerivAt
    simpa only [one_smul] using
      hd.comp_hasDerivAt (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).smul_const x)
  have hright : HasDerivAt (fun t : ℝ => t ^ α • f x) (α • f x) 1 := by
    simpa using (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := α)
      (Or.inl one_ne_zero)).smul_const (f x)
  have heq : (fun t : ℝ => f (t • x)) =ᶠ[𝓝 1] (fun t => t ^ α • f x) := by
    filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    exact hhom t ht
  exact (hleft.congr_of_eventuallyEq heq.symm).unique hright

theorem euler_second (f : E → F) (α : ℝ) (x U : E)
    (hf : ContDiffAt ℝ 2 f x)
    (hhom : ∀ᶠ y in 𝓝 x, ∀ t : ℝ, 0 < t → f (t • y) = t ^ α • f y) :
    fderiv ℝ (fderiv ℝ f) x U x = (α - 1) • fderiv ℝ f x U := by
  have hd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hdd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt
      (by norm_num)
  have heuler : (fun y => fderiv ℝ f y y) =ᶠ[𝓝 x] (fun y => α • f y) := by
    filter_upwards [hhom, hf.eventually (by simp)] with y hy hfy
    exact euler_first f α y (hfy.differentiableAt (by norm_num)) hy
  have hleft := hdd.hasFDerivAt.clm_apply (hasFDerivAt_id (𝕜 := ℝ) x)
  have hright := hd.hasFDerivAt.const_smul α
  have heq := congrArg (fun L : E →L[ℝ] F => L U)
    ((hleft.congr_of_eventuallyEq heuler.symm).unique hright)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smul_apply, id_eq] at heq
  rw [sub_smul, one_smul]
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using heq)

theorem iteratedDeriv_two_line (f : E → F) (x V : E)
    (hf : ContDiffAt ℝ 2 f x) :
    iteratedDeriv 2 (fun t : ℝ => f (x + t • V)) 0 =
      fderiv ℝ (fderiv ℝ f) x V V := by
  let γ : ℝ → E := fun t => x + t • V
  have hγ : ContDiff ℝ 2 γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hdγ : deriv γ = fun _ => V := by
    funext t
    simpa only [one_smul, zero_add] using
      ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const V)).deriv
  have hddγ : iteratedDeriv 2 γ 0 = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hdγ]
    simp
  have hfγ : ContDiffAt ℝ 2 f (γ 0) := by simpa [γ] using hf
  have h := iteratedDeriv_vcomp_two hfγ hγ.contDiffAt
  simpa only [γ, Function.comp_def, zero_smul, add_zero, hdγ, hddγ,
    iteratedFDeriv_two_apply, map_zero, add_zero] using h

end Homogeneity

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance matrixPowerDifferentialCStar : CStarAlgebra (Matrix n n ℂ) := {}

/-- The actual matrix power on the real vector space of Hermitian inputs. -/
def power (α : ℝ) (M : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ :=
  CFC.rpow (M : Matrix n n ℂ) α

def first (α : ℝ) (M U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ :=
  fderiv ℝ (power α) M U

def second (α : ℝ) (M U V : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ :=
  fderiv ℝ (fderiv ℝ (power α)) M U V

theorem smooth {α : ℝ} (hα : α ∈ Ioo 0 1)
    (M : selfAdjoint (Matrix n n ℂ)) (hM : (M : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (power α) M := PowerIntegralDerivatives.contDiffAt_power hα M hM

theorem first_radial {α : ℝ} (hα : α ∈ Ioo 0 1)
    (M : selfAdjoint (Matrix n n ℂ)) (hM : (M : Matrix n n ℂ).PosDef) :
    first α M M = α • power α M := by
  apply euler_first _ _ _ ((smooth hα M hM).differentiableAt (by simp))
  intro t ht
  exact matrix_rpow_smul hM.posSemidef ht.le hα.1.le

theorem second_radial {α : ℝ} (hα : α ∈ Ioo 0 1)
    (M U : selfAdjoint (Matrix n n ℂ)) (hM : (M : Matrix n n ℂ).PosDef) :
    second α M U M = (α - 1) • first α M U := by
  apply euler_second (power α) α M U ((smooth hα M hM).of_le (by
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top))
  filter_upwards [eventually_posDef_of_posDef M hM] with X hX
  intro t ht
  exact matrix_rpow_smul hX.posSemidef ht.le hα.1.le

theorem second_symm {α : ℝ} (hα : α ∈ Ioo 0 1)
    (M U V : selfAdjoint (Matrix n n ℂ)) (hM : (M : Matrix n n ℂ).PosDef) :
    second α M U V = second α M V U :=
  ((smooth hα M hM).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)).eq U V

theorem first_integral {α : ℝ} (hα : α ∈ Ioo 0 1) (μ : Measure ℝ)
    (hμ : PowerIntegralRepresentation.ScalarRepresentation α μ)
    (M U : selfAdjoint (Matrix n n ℂ)) (hM : (M : Matrix n n ℂ).PosDef) :
    first α M U = ∫ t in Ioi 0, t ^ α •
      (resolvent M t * (U : Matrix n n ℂ) * resolvent M t) ∂μ := by
  have hd : HasDerivAt (fun s : ℝ => power α (M + s • U)) (first α M U) 0 := by
    have hf : HasFDerivAt (power α) (fderiv ℝ (power α) M) (M + (0 : ℝ) • U) := by
      simpa using ((smooth hα M hM).differentiableAt (by simp)).hasFDerivAt
    simpa only [zero_add, one_smul] using hf.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_const (0 : ℝ) M).add ((hasDerivAt_id (0 : ℝ)).smul_const U))
  exact hd.unique (PowerIntegralDerivatives.hasDerivAt_power_integral hα μ hμ hM U.property)

theorem second_diagonal_integral {α : ℝ} (hα : α ∈ Ioo 0 1) (μ : Measure ℝ)
    (hμ : PowerIntegralRepresentation.ScalarRepresentation α μ)
    (M U : selfAdjoint (Matrix n n ℂ)) (hM : (M : Matrix n n ℂ).PosDef) :
    second α M U U = ∫ t in Ioi 0, (-2 * t ^ α) •
      (resolvent M t * (U : Matrix n n ℂ) * resolvent M t *
        (U : Matrix n n ℂ) * resolvent M t) ∂μ := by
  unfold second
  rw [← iteratedDeriv_two_line (power α) M U ((smooth hα M hM).of_le (by
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top))]
  exact (PowerIntegralDerivatives.iteratedDeriv_two_power_integral hα μ hμ hM U.property).2

end HigherRankKS.MatrixPowerDifferential
