import AugmentedHigherRankKS.RuntimeRegularity.RelativeCarrierDerivatives
import HigherRankKS.SourceCompression

/-! Scalar weight products preserve relative coefficient bounds. This is
applied before the fixed positive maps defining each supported source owner. -/

open Matrix MatrixSpencer HigherRankKS Set Filter
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKSRuntime.RelativeProductDerivatives
open RelativeCarrierDerivatives

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

theorem succ_le_two_pow (k : ℕ) : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Nat.cast_succ, pow_succ]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith

theorem carrier_derivative_geometric {β : ℝ} (hβ : β ∈ Ioo 0 1)
    {M U : Matrix n n ℂ} (hM : M.PosDef) (hU : U.IsHermitian)
    {b : ℝ} (hb : 0 ≤ b) (hlo : (-b) • M ≤ U) (hhi : U ≤ b • M) (k : ℕ) :
    -((k.factorial : ℝ) * (2 * b) ^ k) • carrierPower β M ≤
        iteratedDeriv k (fun s : ℝ => carrierPower β (M + s • U)) 0 ∧
      iteratedDeriv k (fun s : ℝ => carrierPower β (M + s • U)) 0 ≤
        ((k.factorial : ℝ) * (2 * b) ^ k) • carrierPower β M := by
  obtain ⟨hl, hu⟩ := carrier_derivative_relative hβ hM hU hb hlo hhi k
  have hc : (k + 1) * (k.factorial : ℝ) * b ^ k ≤
      (k.factorial : ℝ) * (2 * b) ^ k := by
    rw [mul_pow]
    have hh := mul_le_mul_of_nonneg_right (succ_le_two_pow k)
      (show 0 ≤ (k.factorial : ℝ) * b ^ k by positivity)
    convert hh using 1 <;> ring
  have hP := (carrierPower_posSemidef β hM.posSemidef).nonneg
  exact ⟨(smul_le_smul_of_nonneg_right (neg_le_neg hc) hP).trans hl,
    hu.trans (smul_le_smul_of_nonneg_right hc hP)⟩

theorem product_derivative_relative {f : ℝ → ℝ} {g : ℝ → Matrix n n ℂ}
    {k : ℕ} {x c d e : ℝ} {P : Matrix n n ℂ}
    (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x)
    (hh : ∀ᶠ t in 𝓝 x, (g t).IsHermitian) (hP : P.PosDef)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hfbound : ∀ i ≤ k, ‖iteratedDeriv i f x‖ ≤ (i.factorial : ℝ) * d ^ i * c)
    (hgbound : ∀ i ≤ k,
      -((i.factorial : ℝ) * e ^ i) • P ≤ iteratedDeriv i g x ∧
        iteratedDeriv i g x ≤ ((i.factorial : ℝ) * e ^ i) • P) :
    -((k.factorial : ℝ) * (d + e) ^ k) • (c • P) ≤
        iteratedDeriv k (fun t => f t • g t) x ∧
      iteratedDeriv k (fun t => f t • g t) x ≤
        ((k.factorial : ℝ) * (d + e) ^ k) • (c • P) := by
  let V := (CFC.sqrt P)⁻¹
  let G := fun t => sandwichCLM V (g t)
  have hG : ContDiffAt ℝ k G x := (sandwichCLM V).contDiff.contDiffAt.comp x hg
  have hGn : ∀ i ≤ k, ‖iteratedDeriv i G x‖ ≤ (i.factorial : ℝ) * e ^ i := by
    intro i hi
    have hgi : ContDiffAt ℝ i g x := hg.of_le (by exact_mod_cast hi)
    rw [WeightedCompactIntegral.iteratedDeriv_clm _ hgi]
    exact (RelativeResolventWords.normalized_direction hP (iteratedDeriv_isHermitian hgi hh)
      (by positivity) (hgbound i hi).1 (hgbound i hi).2).2.1
  have hn := LocalLeibniz.norm_iteratedDeriv_smul_geometric hf hG hd he hc hfbound hGn
  have hcs := hf.smul hg
  have hcurve : (fun t => f t • G t) =
      (fun t => sandwichCLM V (f t • g t)) := by
    funext t
    exact (map_smul (sandwichCLM V) (f t) (g t)).symm
  rw [hcurve, WeightedCompactIntegral.iteratedDeriv_clm _ hcs] at hn
  simp only [sandwichCLM_apply] at hn
  have hD : (iteratedDeriv k (fun t => f t • g t) x).IsHermitian := by
    apply iteratedDeriv_isHermitian hcs
    filter_upwards [hh] with t ht
    change (f t • g t)ᴴ = f t • g t
    simp only [Matrix.conjTranspose_smul, star_trivial, ht.eq]
  have hS := hP.posDef_sqrt.isHermitian
  have hV : V.IsHermitian := hS.inv
  have hVD : (V * iteratedDeriv k (fun t => f t • g t) x * V).IsHermitian := by
    simpa only [hV.eq] using Matrix.isHermitian_mul_mul_conjTranspose V hD
  obtain ⟨hl, hu⟩ := norm_gives_order hVD hn
  have hl' := KrausContraction.congruence_mono hl (CFC.sqrt P) hS
  have hu' := KrausContraction.congruence_mono hu (CFC.sqrt P) hS
  letI : Invertible (CFC.sqrt P) := hP.posDef_sqrt.isUnit.invertible
  have hSS : CFC.sqrt P * CFC.sqrt P = P := CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg
  have hSV : CFC.sqrt P * V = 1 := Matrix.mul_inv_of_invertible _
  have hVS : V * CFC.sqrt P = 1 := Matrix.inv_mul_of_invertible _
  have hre : CFC.sqrt P * (V * iteratedDeriv k (fun t => f t • g t) x * V) *
      CFC.sqrt P = iteratedDeriv k (fun t => f t • g t) x := by
    simp only [← Matrix.mul_assoc, hSV, Matrix.one_mul]
    rw [Matrix.mul_assoc, hVS, Matrix.mul_one]
  rw [hre] at hl' hu'
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hSS] at hl' hu'
  constructor
  · convert hl' using 1 <;> module
  · convert hu' using 1 <;> module

theorem weighted_carrier_derivative_relative {β : ℝ} (hβ : β ∈ Ioo 0 1)
    {M U : Matrix n n ℂ} (hM : M.PosDef) (hU : U.IsHermitian)
    {b : ℝ} (hb : 0 ≤ b) (hlo : (-b) • M ≤ U) (hhi : U ≤ b • M)
    {f : ℝ → ℝ} {k : ℕ} {c d : ℝ} (hf : ContDiffAt ℝ k f 0)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hfbound : ∀ i ≤ k, ‖iteratedDeriv i f 0‖ ≤ (i.factorial : ℝ) * d ^ i * c) :
    -((k.factorial : ℝ) * (d + 2 * b) ^ k) • (c • carrierPower β M) ≤
        iteratedDeriv k (fun t => f t • carrierPower β (M + t • U)) 0 ∧
      iteratedDeriv k (fun t => f t • carrierPower β (M + t • U)) 0 ≤
        ((k.factorial : ℝ) * (d + 2 * b) ^ k) • (c • carrierPower β M) := by
  have hsm : ContDiffAt ℝ k (fun s : ℝ => carrierPower β (M + s • U)) 0 := by
    have hp : 0 < realTrace M := by
      simpa only [Matrix.mul_one] using KSBalancedSpin.realTrace_mul_pos_of_posDef hM
        Matrix.PosDef.one.posSemidef (by simp)
    have ht : ContDiffAt ℝ k (fun s : ℝ => Real.rpow (realTrace (M + s • U)) β) 0 :=
      ((realTraceCLM (n := n)).contDiff.contDiffAt.comp 0
        (show ContDiffAt ℝ k (fun s : ℝ => M + s • U) 0 by fun_prop)).rpow_const_of_ne
        (by simpa using hp.ne')
    exact ht.smul (HigherRankKS.PowerIntegralDerivatives.contDiffAt_power_curve
      ⟨by linarith [hβ.2], by linarith [hβ.1]⟩ hM hU k)
  refine product_derivative_relative hf hsm ?_ (carrierPower_posDef β hM) hc hd
    (by positivity) hfbound ?_
  · filter_upwards [KSMovingOwnerHessian.eventually_posDef_transportLine hM hU] with t ht
    exact carrierPower_isHermitian β ht.posSemidef
  · intro i _
    exact carrier_derivative_geometric hβ hM hU hb hlo hhi i

end HigherRankKSRuntime.RelativeProductDerivatives
