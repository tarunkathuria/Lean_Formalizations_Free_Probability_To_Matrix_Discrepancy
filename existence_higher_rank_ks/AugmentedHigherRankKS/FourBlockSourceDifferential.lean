import AugmentedHigherRankKS.FourBlockSourceDerivatives
import HigherRankKS.CarrierDerivative

/-! Positivity and radial contact for the actual nonlinear four-block source derivative. -/
noncomputable section
set_option maxHeartbeats 800000
open Matrix MatrixSpencer HigherRankKS Filter Set
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance sourceDifferentialCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}

theorem source_mono_density (A : ι → Matrix n n ℂ) {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {S T : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef) (hST : S ≤ T) :
    source A β c S ≤ source A β c T := by
  have hD : (T-S).PosSemidef := Matrix.le_iff.mp hST
  have hs := source_weighted_add_le A hβ hβ1 hc hS hD (by norm_num : (0:ℝ) ≤ 1)
    (by norm_num : (0:ℝ) ≤ 1)
  simp only [one_smul, add_sub_cancel] at hs
  exact (le_add_of_nonneg_right (source_posSemidef A β hc hD).nonneg).trans hs

theorem source_smul_density (A : ι → Matrix n n ℂ) {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef)
    {t : ℝ} (ht : 0 < t) : source A β c (t • S) = t • source A β c S := by
  apply le_antisymm
  · have hs := source_weighted_add_le A hβ hβ1 hc (hS.smul ht.le) hS
      (inv_nonneg.mpr ht.le) (by norm_num : (0:ℝ) ≤ 0)
    simp only [zero_smul, add_zero, smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at hs
    have hb := smul_le_smul_of_nonneg_left hs ht.le
    simpa only [smul_smul, mul_inv_cancel₀ ht.ne', one_smul] using hb
  · have hs := source_weighted_add_le A hβ hβ1 hc hS hS ht.le (by norm_num : (0:ℝ) ≤ 0)
    simpa only [zero_smul, add_zero] using hs

def densitySource (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) := source A β c S

theorem densitySource_smooth (A : ι → Matrix n n ℂ) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (densitySource A ((1:ℝ)/2^k) c) S :=
  (contDiffAt_jointSource A k hk c S hS).comp S (contDiffAt_const.prodMk contDiffAt_id)

theorem densitySource_fderiv_posSemidef (A : ι → Matrix n n ℂ) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (hX : (X : Matrix (FourSpin n) (FourSpin n) ℂ).PosSemidef) :
    (fderiv ℝ (densitySource A ((1:ℝ)/2^k) c) S X).PosSemidef := by
  have hd := (densitySource_smooth A k hk c S hS).differentiableAt (by simp)
  have hl : HasDerivAt (fun t : ℝ => S+t • X) X 0 := by
    simpa only [zero_add, one_smul, Pi.add_apply] using (hasDerivAt_const (0:ℝ) S).add ((hasDerivAt_id (0:ℝ)).smul_const X)
  have hcomp := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
  apply matrix_derivative_nonneg_of_right_order hcomp
  intro t ht
  simp only [Function.comp_apply, densitySource, zero_smul, add_zero]
  apply source_mono_density A (by positivity) ?_ hc hS.posSemidef
  · exact le_add_of_nonneg_right (hX.smul ht.le).nonneg
  · apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)

theorem densitySource_fderiv_radial (A : ι → Matrix n n ℂ) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    fderiv ℝ (densitySource A ((1:ℝ)/2^k) c) S S = source A ((1:ℝ)/2^k) c S := by
  have hd := (densitySource_smooth A k hk c S hS).differentiableAt (by simp)
  have hl : HasDerivAt (fun t : ℝ => S+t • S) S 0 := by
    simpa only [zero_add, one_smul, Pi.add_apply] using (hasDerivAt_const (0:ℝ) S).add ((hasDerivAt_id (0:ℝ)).smul_const S)
  have hcomp := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
  have he : (fun t : ℝ => densitySource A ((1:ℝ)/2^k) c (S+t • S)) =ᶠ[𝓝 0]
      (fun t => (1+t) • source A ((1:ℝ)/2^k) c S) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (-1:ℝ)<0 by norm_num)] with t ht
    change -1 < t at ht
    change source A _ c ((S : Matrix (FourSpin n) (FourSpin n) ℂ)+t • (S : Matrix (FourSpin n) (FourSpin n) ℂ)) = _
    rw [show (S : Matrix (FourSpin n) (FourSpin n) ℂ)+t • (S : Matrix (FourSpin n) (FourSpin n) ℂ) =
      (1+t) • (S : Matrix (FourSpin n) (FourSpin n) ℂ) by module]
    apply source_smul_density A (by positivity) ?_ hc hS.posSemidef (by linarith)
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hr : HasDerivAt (fun t : ℝ => (1+t) • source A ((1:ℝ)/2^k) c S)
      (source A ((1:ℝ)/2^k) c S) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).const_add 1).smul_const (source A ((1:ℝ)/2^k) c S))
  exact hcomp.unique (hr.congr_of_eventuallyEq he)

end AugmentedHigherRankKS
