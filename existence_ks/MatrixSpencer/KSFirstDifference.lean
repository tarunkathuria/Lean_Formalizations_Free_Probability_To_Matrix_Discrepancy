import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Certified first-derivative reports from a centered finite stencil

The implementation calls the supplied value report at the two actual sample
points. Its accuracy theorem proves the Taylor error from continuous second
differentiability on the sampled segment and a second-derivative bound; no
Taylor remainder is assumed. The value-report accuracy remains an explicit
interface to the objective evaluator.
-/

open Set
open scoped Topology
noncomputable section
namespace MatrixSpencer.KSFirstDifference

/-- Arithmetic evaluation of the two sampled values. -/
def sampleSlope (plus minus t : ℝ) : ℝ := (plus - minus) / (2 * t)

/-- The callable centered first-difference stencil. -/
def stencil (r : ℝ → ℝ) (x t : ℝ) : ℝ := sampleSlope (r (x + t)) (r (x - t)) t

theorem sampleSlope_swap (plus minus t : ℝ) :
    sampleSlope minus plus t = -sampleSlope plus minus t := by
  unfold sampleSlope
  ring

theorem stencil_reflect (r : ℝ → ℝ) (t : ℝ) :
    stencil (fun u => r (-u)) 0 t = -stencil r 0 t := by
  simp only [stencil, zero_add, zero_sub, neg_neg]
  exact sampleSlope_swap _ _ _

/-- The one-sided quadratic error is proved by the actual Lagrange Taylor theorem. -/
theorem positive_remainder (f : ℝ → ℝ) {t L : ℝ} (ht : 0 < t)
    (hf : ContDiffOn ℝ 2 f (Icc 0 t)) (hd : DifferentiableAt ℝ f 0)
    (hL : ∀ u ∈ Ioo 0 t, |iteratedDeriv 2 f u| ≤ L) :
    |f t - f 0 - t * deriv f 0| ≤ L * t ^ 2 / 2 := by
  obtain ⟨u, hu, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) ht hf
  have hdw : derivWithin f (Icc 0 t) 0 = deriv f 0 :=
    hd.hasDerivAt.hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc ht) 0 (left_mem_Icc.mpr ht.le))
  have hpoly : taylorWithinEval f 1 (Icc 0 t) 0 t = f 0 + t * deriv f 0 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval,
      iteratedDerivWithin_one, hdw]
    norm_num
  rw [hpoly] at hrem
  norm_num at hrem
  have heq : f t - f 0 - t * deriv f 0 = iteratedDeriv 2 f u * t ^ 2 / 2 := by linarith
  rw [heq, abs_div, abs_mul, abs_of_nonneg (sq_nonneg t)]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hL u hu) (sq_nonneg t)) (by norm_num)

/-- Exact objective samples give the centered derivative error `L*t/2`. -/
theorem exact_stencil_error_zero (f : ℝ → ℝ) {t L : ℝ} (ht : 0 < t)
    (hf : ContDiffOn ℝ 2 f (Icc (-t) t))
    (hL : ∀ u ∈ Icc (-t) t, |iteratedDeriv 2 f u| ≤ L) :
    |stencil f 0 t - deriv f 0| ≤ L * t / 2 := by
  have hd : DifferentiableAt ℝ f 0 :=
    (hf.contDiffAt (Icc_mem_nhds_iff.mpr ⟨by linarith, ht⟩)).differentiableAt (by norm_num)
  have hfp : ContDiffOn ℝ 2 f (Icc 0 t) := hf.mono (by intro u hu; constructor <;> linarith [hu.1, hu.2])
  have hp := positive_remainder f ht hfp hd (fun u hu => hL u ⟨by linarith [hu.1], hu.2.le⟩)
  have hfn : ContDiffOn ℝ 2 (fun u => f (-u)) (Icc 0 t) :=
    hf.comp contDiff_neg.contDiffOn (by intro u hu; constructor <;> linarith [hu.1, hu.2])
  have hdn : DifferentiableAt ℝ (fun u => f (-u)) 0 := by
    exact (show DifferentiableAt ℝ f (-(0 : ℝ)) by simpa using hd).comp 0 differentiableAt_id.neg
  have hLn (u : ℝ) (hu : u ∈ Ioo 0 t) : |iteratedDeriv 2 (fun v => f (-v)) u| ≤ L := by
    rw [iteratedDeriv_comp_neg]
    simpa using hL (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hn := positive_remainder (fun u => f (-u)) ht hfn hdn hLn
  simp only [neg_zero, deriv_comp_neg] at hn
  have herr : |f t - f (-t) - (2 * t) * deriv f 0| ≤ L * t ^ 2 := by
    rcases abs_le.mp hp with ⟨hp₁, hp₂⟩
    rcases abs_le.mp hn with ⟨hn₁, hn₂⟩
    apply abs_le.mpr
    constructor <;> nlinarith
  have heq : stencil f 0 t - deriv f 0 =
      (f t - f (-t) - (2 * t) * deriv f 0) / (2 * t) := by
    simp only [stencil, sampleSlope, zero_add, zero_sub]
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos (by norm_num) ht)]
  calc
    _ ≤ (L * t ^ 2) / (2 * t) := div_le_div_of_nonneg_right herr (by positivity)
    _ = L * t / 2 := by field_simp

/-- Two value errors of size `ν` contribute at most `ν/t` to the centered derivative. -/
theorem stencil_value_error (f r : ℝ → ℝ) (x : ℝ) {t ν : ℝ} (ht : 0 < t)
    (hp : |r (x + t) - f (x + t)| ≤ ν) (hm : |r (x - t) - f (x - t)| ≤ ν) :
    |stencil r x t - stencil f x t| ≤ ν / t := by
  have he : stencil r x t - stencil f x t =
      ((r (x + t) - f (x + t)) - (r (x - t) - f (x - t))) / (2 * t) := by
    unfold stencil sampleSlope
    ring
  rw [he, abs_div, abs_of_pos (mul_pos (by norm_num) ht)]
  have hn : |(r (x + t) - f (x + t)) - (r (x - t) - f (x - t))| ≤ 2 * ν := by
    exact (abs_sub _ _).trans (by linarith)
  calc
    _ ≤ (2 * ν) / (2 * t) := div_le_div_of_nonneg_right hn (by positivity)
    _ = ν / t := by ring

/-- Centered first-difference accuracy at the origin, from actual `C²` calculus. -/
theorem stencil_error_zero (f r : ℝ → ℝ) {t L ν : ℝ} (ht : 0 < t)
    (hf : ContDiffOn ℝ 2 f (Icc (-t) t))
    (hL : ∀ u ∈ Icc (-t) t, |iteratedDeriv 2 f u| ≤ L)
    (hp : |r t - f t| ≤ ν) (hm : |r (-t) - f (-t)| ≤ ν) :
    |stencil r 0 t - deriv f 0| ≤ L * t / 2 + ν / t := by
  have hv := stencil_value_error f r 0 ht (by simpa using hp) (by simpa using hm)
  exact (abs_sub_le (stencil r 0 t) (stencil f 0 t) (deriv f 0)).trans
    (by linarith [exact_stencil_error_zero f ht hf hL])

/-- The same calculus guarantee at any center of the actual sampled interval. -/
theorem stencil_error (f r : ℝ → ℝ) (x : ℝ) {t L ν : ℝ} (ht : 0 < t)
    (hf : ContDiffOn ℝ 2 f (Icc (x - t) (x + t)))
    (hL : ∀ u ∈ Icc (x - t) (x + t), |iteratedDeriv 2 f u| ≤ L)
    (hp : |r (x + t) - f (x + t)| ≤ ν) (hm : |r (x - t) - f (x - t)| ≤ ν) :
    |stencil r x t - deriv f x| ≤ L * t / 2 + ν / t := by
  have hf' : ContDiffOn ℝ 2 (fun u => f (x + u)) (Icc (-t) t) :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn
      (by intro u hu; constructor <;> linarith [hu.1, hu.2])
  have hL' (u : ℝ) (hu : u ∈ Icc (-t) t) :
      |iteratedDeriv 2 (fun v => f (x + v)) u| ≤ L := by
    rw [iteratedDeriv_comp_const_add]
    exact hL (x + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h := stencil_error_zero (fun u => f (x + u)) (fun u => r (x + u)) ht hf' hL'
    hp (by simpa only [sub_eq_add_neg] using hm)
  simpa only [stencil, sampleSlope, zero_add, zero_sub, deriv_comp_const_add,
    add_zero, ← sub_eq_add_neg] using h

section Direction
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The actual two-query directional stencil in any real vector space. -/
def directionalStencil (r : E → ℝ) (x v : E) (t : ℝ) : ℝ :=
  sampleSlope (r (x + t • v)) (r (x - t • v)) t

/-- Negating the direction swaps the two actual oracle queries. -/
theorem directionalStencil_neg (r : E → ℝ) (x v : E) (t : ℝ) :
    directionalStencil r x (-v) t = -directionalStencil r x v t := by
  simp only [directionalStencil, smul_neg, sub_neg_eq_add, ← sub_eq_add_neg]
  exact sampleSlope_swap _ _ _

theorem directionalStencil_eq_curve (r : E → ℝ) (x v : E) (t : ℝ) :
    directionalStencil r x v t = stencil (fun u => r (x + u • v)) 0 t := by
  simp only [directionalStencil, stencil, zero_add, zero_sub, neg_smul, ← sub_eq_add_neg]

/-- Directional version: the regularity and second-derivative cap are imposed on
 the actual line sampled by the numerical stencil. -/
theorem directionalStencil_error (f r : E → ℝ) (x v : E) {t L ν : ℝ} (ht : 0 < t)
    (hf : ContDiffOn ℝ 2 (fun u => f (x + u • v)) (Icc (-t) t))
    (hL : ∀ u ∈ Icc (-t) t, |iteratedDeriv 2 (fun w => f (x + w • v)) u| ≤ L)
    (hp : |r (x + t • v) - f (x + t • v)| ≤ ν)
    (hm : |r (x - t • v) - f (x - t • v)| ≤ ν) :
    |directionalStencil r x v t - deriv (fun u : ℝ => f (x + u • v)) 0| ≤ L * t / 2 + ν / t := by
  rw [directionalStencil_eq_curve]
  exact stencil_error_zero (fun u : ℝ => f (x + u • v)) (fun u : ℝ => r (x + u • v))
    ht hf hL hp (by simpa only [neg_smul, sub_eq_add_neg] using hm)

end Direction
end MatrixSpencer.KSFirstDifference
