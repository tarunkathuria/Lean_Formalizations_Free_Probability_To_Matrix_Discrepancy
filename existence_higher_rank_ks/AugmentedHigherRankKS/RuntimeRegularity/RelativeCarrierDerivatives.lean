import AugmentedHigherRankKS.RuntimeRegularity.RelativeScalarPower
import AugmentedHigherRankKS.RuntimeRegularity.LocalLeibniz
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Uniform relative derivative bounds for the actual trace-perspective
carrier. A fixed congruence normalizes the matrix power before Leibniz's
inequality is applied, so no smallest-eigenvalue factor enters the estimate. -/

open Matrix MatrixSpencer HigherRankKS Set Filter
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKSRuntime.RelativeCarrierDerivatives

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

def sandwichCLM (W : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  ((LinearMap.mulRight ℝ W).comp (LinearMap.mulLeft ℝ W)).toContinuousLinearMap

@[simp] theorem sandwichCLM_apply (W X : Matrix n n ℂ) :
    sandwichCLM W X = W * X * W := rfl

theorem iteratedDeriv_isHermitian {f : ℝ → Matrix n n ℂ} {k : ℕ} {x : ℝ}
    (hf : ContDiffAt ℝ k f x) (hh : ∀ᶠ t in 𝓝 x, (f t).IsHermitian) :
    (iteratedDeriv k f x).IsHermitian := by
  let L : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
    (starL' ℝ : Matrix n n ℂ ≃L[ℝ] Matrix n n ℂ).toContinuousLinearMap
  have he : (fun t => L (f t)) =ᶠ[𝓝 x] f := by
    filter_upwards [hh] with t ht
    exact ht.eq
  have hd := WeightedCompactIntegral.iteratedDeriv_clm L hf
  exact hd.symm.trans (he.iteratedDeriv_eq k)

theorem norm_gives_order {X : Matrix n n ℂ} (hX : X.IsHermitian)
    {b : ℝ} (hb : ‖X‖ ≤ b) :
    (-b) • (1 : Matrix n n ℂ) ≤ X ∧ X ≤ b • (1 : Matrix n n ℂ) := by
  have hu := (show IsSelfAdjoint X from hX).le_algebraMap_norm_self
  have hl := (show IsSelfAdjoint (-X) from hX.neg).le_algebraMap_norm_self
  rw [Algebra.algebraMap_eq_smul_one] at hu hl
  rw [norm_neg] at hl
  have hu' := hu.trans (smul_le_smul_of_nonneg_right hb (zero_le_one :
    (0 : Matrix n n ℂ) ≤ 1))
  have hl' := hl.trans (smul_le_smul_of_nonneg_right hb (zero_le_one :
    (0 : Matrix n n ℂ) ≤ 1))
  exact ⟨by simpa only [neg_smul, neg_neg] using neg_le_neg hl', hu'⟩

theorem power_posDef {M : Matrix n n ℂ} (hM : M.PosDef)
    {α : ℝ} (hα : α ≠ 0) : (CFC.rpow M α).PosDef := by
  apply (CFC.rpow_nonneg.posSemidef).posDef_iff_isUnit.mpr
  exact (CFC.isUnit_rpow_iff M α hα hM.posSemidef.nonneg).mpr hM.isUnit

theorem normalized_power_derivative {α : ℝ} (hα : α ∈ Ioo 0 1)
    {M U : Matrix n n ℂ} (hM : M.PosDef) (hU : U.IsHermitian)
    {b : ℝ} (hb : 0 ≤ b) (hlo : (-b) • M ≤ U) (hhi : U ≤ b • M) (k : ℕ) :
    let P := CFC.rpow M α
    let V := (CFC.sqrt P)⁻¹
    ‖iteratedDeriv k (fun s : ℝ => V * CFC.rpow (M + s • U) α * V) 0‖ ≤
      (k.factorial : ℝ) * b ^ k := by
  dsimp only
  let P := CFC.rpow M α
  let V := (CFC.sqrt P)⁻¹
  have hP : P.PosDef := power_posDef hM hα.1.ne'
  have hs := HigherRankKS.PowerIntegralDerivatives.contDiffAt_power_curve hα hM hU k
  have he := WeightedCompactIntegral.iteratedDeriv_clm (sandwichCLM V) hs
  simp only [sandwichCLM_apply] at he
  change ‖iteratedDeriv k (fun s : ℝ => V * CFC.rpow (M + s • U) α * V) 0‖ ≤ _
  rw [he]
  by_cases hk : k = 0
  · subst k
    have hn := (RelativeResolventWords.normalized_direction hP hP.isHermitian
      (b := 1) zero_le_one (by simpa using neg_le_self hP.posSemidef.nonneg)
      (by simp)).2.1
    simpa only [iteratedDeriv_zero, zero_smul, add_zero, Nat.factorial_zero,
      Nat.cast_one, pow_zero, mul_one] using hn
  · have hd := RelativePowerDerivatives.power_derivative_relative hα hM hU hb hlo hhi k
      (Nat.pos_of_ne_zero hk)
    have hh : (iteratedDeriv k (fun s : ℝ => CFC.rpow (M + s • U) α) 0).IsHermitian :=
      iteratedDeriv_isHermitian hs (Filter.Eventually.of_forall (fun s =>
        CFC.rpow_nonneg.posSemidef.isHermitian))
    exact (RelativeResolventWords.normalized_direction hP hh (by positivity)
      hd.1 hd.2).2.1

theorem carrier_derivative_relative {β : ℝ} (hβ : β ∈ Ioo 0 1)
    {M U : Matrix n n ℂ} (hM : M.PosDef) (hU : U.IsHermitian)
    {b : ℝ} (hb : 0 ≤ b) (hlo : (-b) • M ≤ U) (hhi : U ≤ b • M) (k : ℕ) :
    -((k + 1) * (k.factorial : ℝ) * b ^ k) • carrierPower β M ≤
        iteratedDeriv k (fun s : ℝ => carrierPower β (M + s • U)) 0 ∧
      iteratedDeriv k (fun s : ℝ => carrierPower β (M + s • U)) 0 ≤
        ((k + 1) * (k.factorial : ℝ) * b ^ k) • carrierPower β M := by
  let p := realTrace M
  let u := realTrace U
  have hp : 0 < p := by
    simpa only [Matrix.mul_one, p] using KSBalancedSpin.realTrace_mul_pos_of_posDef hM
      Matrix.PosDef.one.posSemidef (by simp)
  have hu : |u| ≤ b * p := by
    have hl := realTrace_mul_mono Matrix.PosDef.one.posSemidef hlo
    have hh := realTrace_mul_mono Matrix.PosDef.one.posSemidef hhi
    simp only [Matrix.one_mul, realTrace_smul] at hl hh
    exact abs_le.mpr ⟨by dsimp [p, u]; linarith, hh⟩
  let P := CFC.rpow M (1 - β)
  let V := (CFC.sqrt P)⁻¹
  have hα : 1 - β ∈ Ioo 0 1 := ⟨by linarith [hβ.2], by linarith [hβ.1]⟩
  have hP : P.PosDef := power_posDef hM hα.1.ne'
  have hS : (CFC.sqrt P).IsHermitian := hP.posDef_sqrt.isHermitian
  letI : Invertible (CFC.sqrt P) := hP.posDef_sqrt.isUnit.invertible
  have hSS : CFC.sqrt P * CFC.sqrt P = P := CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg
  have hSV : CFC.sqrt P * V = 1 := Matrix.mul_inv_of_invertible _
  have hVS : V * CFC.sqrt P = 1 := Matrix.inv_mul_of_invertible _
  let f : ℝ → ℝ := fun s => (p + s * u) ^ β
  let g : ℝ → Matrix n n ℂ := fun s => V * CFC.rpow (M + s • U) (1 - β) * V
  have hf : ContDiffAt ℝ k f 0 := by
    exact (show ContDiffAt ℝ k (fun s : ℝ => p + s * u) 0 by fun_prop).rpow_const_of_ne
      (by simpa using hp.ne')
  have hpw := HigherRankKS.PowerIntegralDerivatives.contDiffAt_power_curve hα hM hU k
  have hg : ContDiffAt ℝ k g 0 := (sandwichCLM V).contDiff.contDiffAt.comp 0 hpw
  have hfbound : ∀ i ≤ k, ‖iteratedDeriv i f 0‖ ≤ (i.factorial : ℝ) * b ^ i * p ^ β := by
    intro i hi
    by_cases hz : i = 0
    · subst i
      simp only [iteratedDeriv_zero, f, zero_mul, add_zero, Nat.factorial_zero,
        Nat.cast_one, pow_zero, mul_one, one_mul]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp.le β)]
    · simpa only [Real.norm_eq_abs] using
        RelativeScalarPower.affine_power_relative hp hb hu hβ i (Nat.pos_of_ne_zero hz)
  have hgbound : ∀ i ≤ k, ‖iteratedDeriv i g 0‖ ≤ (i.factorial : ℝ) * b ^ i := by
    intro i _
    exact normalized_power_derivative hα hM hU hb hlo hhi i
  have hn := LocalLeibniz.norm_iteratedDeriv_smul_factorial hf hg hb
    (Real.rpow_nonneg hp.le β) hfbound hgbound
  have hcurve : (fun s => f s • g s) =
      (fun s => sandwichCLM V (carrierPower β (M + s • U))) := by
    funext s
    simp only [sandwichCLM_apply, carrierPower, realTrace_add, realTrace_smul,
      Matrix.mul_smul, Matrix.smul_mul, f, g, p, u]
    rfl
  have hcs : ContDiffAt ℝ k (fun s : ℝ => carrierPower β (M + s • U)) 0 := by
    simpa only [carrierPower, realTrace_add, realTrace_smul, f, p, u] using hf.smul hpw
  rw [hcurve, WeightedCompactIntegral.iteratedDeriv_clm _ hcs] at hn
  simp only [sandwichCLM_apply] at hn
  have hhd : (iteratedDeriv k (fun s : ℝ => carrierPower β (M + s • U)) 0).IsHermitian := by
    apply iteratedDeriv_isHermitian hcs
    filter_upwards [KSMovingOwnerHessian.eventually_posDef_transportLine hM hU] with s hs
    exact carrierPower_isHermitian β hs.posSemidef
  have hh : (V * iteratedDeriv k (fun s : ℝ => carrierPower β (M + s • U)) 0 * V).IsHermitian := by
    simpa only [show Vᴴ = V from hS.inv.eq] using Matrix.isHermitian_mul_mul_conjTranspose V hhd
  obtain ⟨hl, hu⟩ := norm_gives_order hh hn
  have hl' := KrausContraction.congruence_mono hl (CFC.sqrt P) hS
  have hu' := KrausContraction.congruence_mono hu (CFC.sqrt P) hS
  have he : CFC.sqrt P * (V * iteratedDeriv k
      (fun s : ℝ => carrierPower β (M + s • U)) 0 * V) * CFC.sqrt P =
      iteratedDeriv k (fun s : ℝ => carrierPower β (M + s • U)) 0 := by
    simp only [← Matrix.mul_assoc, hSV, Matrix.one_mul]
    rw [Matrix.mul_assoc, hVS, Matrix.mul_one]
  rw [he] at hl' hu'
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hSS] at hl' hu'
  constructor
  · convert hl' using 1 <;> dsimp [carrierPower, P, p] <;> module
  · convert hu' using 1 <;> dsimp [carrierPower, P, p] <;> module

end HigherRankKSRuntime.RelativeCarrierDerivatives
