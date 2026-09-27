import MatrixSpencer.KSFiniteDifference
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Fourth-derivative certificates for actual numerical Hessian stencils

Taylor remainders are derived from the Lagrange theorem and actual `C⁴`
regularity. The scalar and directional stencils use their actual value
queries. Mixed entries are obtained by polarization along the two lines
`u+v` and `u-v`; the center report cancels from the four-query formula.
Only the stated derivative bounds and value-report accuracies are inputs.
-/

open Set
open scoped Topology
noncomputable section
namespace MatrixSpencer.KSFourthDifference

open KSFiniteDifference

/-- The cubic Taylor polynomial on the positive half-interval has the
ordinary derivatives at the center, justified by local `C³` regularity. -/
theorem taylor_cubic_eq (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t)
    (hd : ContDiffAt ℝ 3 f 0) :
    taylorWithinEval f 3 (Icc 0 t) 0 t =
      cubic (f 0) (deriv f 0) (iteratedDeriv 2 f 0) (iteratedDeriv 3 f 0) t := by
  have h₁ : iteratedDerivWithin 1 f (Icc 0 t) 0 = iteratedDeriv 1 f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht) (hd.of_le (by norm_num))
      (left_mem_Icc.mpr ht.le)
  have h₂ : iteratedDerivWithin 2 f (Icc 0 t) 0 = iteratedDeriv 2 f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht) (hd.of_le (by norm_num))
      (left_mem_Icc.mpr ht.le)
  have h₃ : iteratedDerivWithin 3 f (Icc 0 t) 0 = iteratedDeriv 3 f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht) hd (left_mem_Icc.mpr ht.le)
  norm_num [taylorWithinEval_succ, taylor_within_zero_eval, h₁, h₂, h₃,
    iteratedDeriv_one, cubic]
  ring

/-- A fourth-order remainder proved by the actual Lagrange Taylor theorem. -/
theorem positive_remainder (f : ℝ → ℝ) {t M : ℝ} (ht : 0 < t)
    (hf : ContDiffOn ℝ 4 f (Icc 0 t)) (hd : ContDiffAt ℝ 3 f 0)
    (hM : ∀ u ∈ Ioo 0 t, |iteratedDeriv 4 f u| ≤ M) :
    |f t - cubic (f 0) (deriv f 0) (iteratedDeriv 2 f 0) (iteratedDeriv 3 f 0) t| ≤
      M * t ^ 4 / 24 := by
  obtain ⟨u, hu, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 3) ht hf
  rw [taylor_cubic_eq f ht hd] at hrem
  norm_num at hrem
  rw [hrem, abs_div, abs_mul, abs_of_nonneg (pow_nonneg ht.le 4)]
  norm_num
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hM u hu) (pow_nonneg ht.le 4)) (by norm_num)

/-- Both signed Taylor remainders are discharged from one sampled interval. -/
theorem signed_remainders (f : ℝ → ℝ) {t M : ℝ} (ht : 0 < t)
    (hf : ContDiffOn ℝ 4 f (Icc (-t) t))
    (hM : ∀ u ∈ Icc (-t) t, |iteratedDeriv 4 f u| ≤ M) :
    |f t - cubic (f 0) (deriv f 0) (iteratedDeriv 2 f 0) (iteratedDeriv 3 f 0) t| ≤
        M * t ^ 4 / 24 ∧
      |f (-t) - cubic (f 0) (deriv f 0) (iteratedDeriv 2 f 0) (iteratedDeriv 3 f 0) (-t)| ≤
        M * t ^ 4 / 24 := by
  have hd : ContDiffAt ℝ 3 f 0 :=
    (hf.contDiffAt (Icc_mem_nhds_iff.mpr ⟨by linarith, ht⟩)).of_le (by norm_num)
  have hfp : ContDiffOn ℝ 4 f (Icc 0 t) :=
    hf.mono (by intro u hu; constructor <;> linarith [hu.1, hu.2])
  have hp := positive_remainder f ht hfp hd
    (fun u hu => hM u ⟨by linarith [hu.1], hu.2.le⟩)
  have hfn : ContDiffOn ℝ 4 (fun u => f (-u)) (Icc 0 t) :=
    hf.comp contDiff_neg.contDiffOn (by intro u hu; constructor <;> linarith [hu.1, hu.2])
  have hdn : ContDiffAt ℝ 3 (fun u => f (-u)) 0 := by
    exact (show ContDiffAt ℝ 3 f (-(0 : ℝ)) by simpa using hd).comp 0 contDiff_neg.contDiffAt
  have hMn (u : ℝ) (hu : u ∈ Ioo 0 t) : |iteratedDeriv 4 (fun v => f (-v)) u| ≤ M := by
    rw [iteratedDeriv_comp_neg]
    simpa using hM (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hn := positive_remainder (fun u => f (-u)) ht hfn hdn hMn
  have hc : cubic (f (-(0 : ℝ))) (deriv (fun u => f (-u)) 0)
      (iteratedDeriv 2 (fun u => f (-u)) 0) (iteratedDeriv 3 (fun u => f (-u)) 0) t =
      cubic (f 0) (deriv f 0) (iteratedDeriv 2 f 0) (iteratedDeriv 3 f 0) (-t) := by
    simp only [deriv_comp_neg, iteratedDeriv_comp_neg, neg_zero]
    norm_num [cubic]
    ring
  exact ⟨hp, by rwa [hc] at hn⟩

theorem symmetric_average_error_zero (f : ℝ → ℝ) {t M : ℝ} (ht : 0 < t)
    (hf : ContDiffOn ℝ 4 f (Icc (-t) t))
    (hM : ∀ u ∈ Icc (-t) t, |iteratedDeriv 4 f u| ≤ M) :
    |(f t + f (-t)) / 2 - f 0 - iteratedDeriv 2 f 0 * t ^ 2 / 2| ≤ M * t ^ 4 / 24 := by
  obtain ⟨hp, hm⟩ := signed_remainders f ht hf hM
  exact symmetric_average_error _ _ _ _ _ _ _ _ hp hm

/-- Three actual value queries for the centered second derivative. -/
def secondStencil (r : ℝ → ℝ) (x t : ℝ) : ℝ :=
  (r (x + t) - 2 * r x + r (x - t)) / t ^ 2

theorem secondStencil_error_zero (f r : ℝ → ℝ) {t M ν : ℝ} (ht : 0 < t)
    (hf : ContDiffOn ℝ 4 f (Icc (-t) t))
    (hM : ∀ u ∈ Icc (-t) t, |iteratedDeriv 4 f u| ≤ M)
    (hp : |r t - f t| ≤ ν) (hz : |r 0 - f 0| ≤ ν) (hm : |r (-t) - f (-t)| ≤ ν) :
    |secondStencil r 0 t - iteratedDeriv 2 f 0| ≤ M * t ^ 2 / 12 + 4 * ν / t ^ 2 := by
  obtain ⟨hplus, hminus⟩ := signed_remainders f ht hf hM
  simpa only [secondStencil, zero_add, zero_sub] using
    centered_second_difference_error _ _ _ _ _ _ _ _ _ _ _ _ ht hplus hminus hp hz hm

theorem exact_secondStencil_error_zero (f : ℝ → ℝ) {t M : ℝ} (ht : 0 < t)
    (hf : ContDiffOn ℝ 4 f (Icc (-t) t))
    (hM : ∀ u ∈ Icc (-t) t, |iteratedDeriv 4 f u| ≤ M) :
    |secondStencil f 0 t - iteratedDeriv 2 f 0| ≤ M * t ^ 2 / 12 := by
  simpa using secondStencil_error_zero f f (ν := 0) ht hf hM
    (by simp) (by simp) (by simp)

section Direction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual second derivative on an affine line is the actual ambient
Hessian quadratic form; no critical-point hypothesis is needed. -/
theorem line_second (f : E → ℝ) (x v : E) (hf : ContDiffAt ℝ 2 f x) :
    iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0 =
      fderiv ℝ (fderiv ℝ f) x v v := by
  have hd (t : ℝ) : deriv (fun u : ℝ => x + u • v) t = v := by
    simpa using (((hasDerivAt_id t).smul_const v).const_add x).deriv
  have hd₂ : iteratedDeriv 2 (fun t : ℝ => x + t • v) 0 = 0 := by
    rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [show deriv (fun t : ℝ => x + t • v) = fun _ => v from funext hd]
    simp
  have hG : ContDiffAt ℝ 2 (fun t : ℝ => x + t • v) 0 := by fun_prop
  have hf' : ContDiffAt ℝ 2 f (x + (0 : ℝ) • v) := by simpa using hf
  have hh := iteratedDeriv_vcomp_two hf' hG
  simpa only [Function.comp_def, zero_smul, add_zero, hd 0, hd₂,
    iteratedFDeriv_two_apply, map_zero, add_zero] using hh

def directionalSecond (r : E → ℝ) (x v : E) (t : ℝ) : ℝ :=
  (r (x + t • v) - 2 * r x + r (x - t • v)) / t ^ 2

theorem directionalSecond_eq_curve (r : E → ℝ) (x v : E) (t : ℝ) :
    directionalSecond r x v t = secondStencil (fun u => r (x + u • v)) 0 t := by
  simp only [directionalSecond, secondStencil, zero_add, zero_smul, add_zero,
    neg_smul, sub_eq_add_neg]

theorem directionalSecond_error (f r : E → ℝ) (x v : E) {t M ν : ℝ} (ht : 0 < t)
    (hf₀ : ContDiffAt ℝ 2 f x)
    (hf : ContDiffOn ℝ 4 (fun u => f (x + u • v)) (Icc (-t) t))
    (hM : ∀ u ∈ Icc (-t) t, |iteratedDeriv 4 (fun w => f (x + w • v)) u| ≤ M)
    (hp : |r (x + t • v) - f (x + t • v)| ≤ ν)
    (hz : |r x - f x| ≤ ν) (hm : |r (x - t • v) - f (x - t • v)| ≤ ν) :
    |directionalSecond r x v t - fderiv ℝ (fderiv ℝ f) x v v| ≤
      M * t ^ 2 / 12 + 4 * ν / t ^ 2 := by
  have hh := secondStencil_error_zero (fun u => f (x + u • v))
    (fun u => r (x + u • v)) ht hf hM hp
    (by simpa only [zero_smul, add_zero] using hz)
    (by simpa only [neg_smul, sub_eq_add_neg] using hm)
  rwa [← directionalSecond_eq_curve, line_second f x v hf₀] at hh

/-- The quantitative symmetric-movement estimate, derived from the actual
fourth derivative on the queried line. -/
theorem directional_average_le (f : E → ℝ) (x v : E) {t M : ℝ} (ht : 0 < t)
    (hf₀ : ContDiffAt ℝ 2 f x)
    (hf : ContDiffOn ℝ 4 (fun u => f (x + u • v)) (Icc (-t) t))
    (hM : ∀ u ∈ Icc (-t) t, |iteratedDeriv 4 (fun w => f (x + w • v)) u| ≤ M) :
    (f (x + t • v) + f (x - t • v)) / 2 ≤ f x +
      fderiv ℝ (fderiv ℝ f) x v v * t ^ 2 / 2 + M * t ^ 4 / 24 := by
  have hh := (abs_le.mp (symmetric_average_error_zero (fun u => f (x + u • v)) ht hf hM)).2
  rw [line_second f x v hf₀] at hh
  simp only [zero_smul, add_zero, neg_smul, ← sub_eq_add_neg] at hh
  linarith

/-- Four actual queries. The first pair lies on `u+v`, the second on `u-v`. -/
def mixedStencil (r : E → ℝ) (x u v : E) (t : ℝ) : ℝ :=
  (r (x + t • (u + v)) - r (x + t • (u - v)) -
    r (x - t • (u - v)) + r (x - t • (u + v))) / (4 * t ^ 2)

theorem mixedStencil_eq_four_queries (r : E → ℝ) (x u v : E) (t : ℝ) :
    mixedStencil r x u v t =
      (r (x + t • u + t • v) - r (x + t • u - t • v) -
        r (x - t • u + t • v) + r (x - t • u - t • v)) / (4 * t ^ 2) := by
  have hp : x + t • (u + v) = x + t • u + t • v := by module
  have hm : x + t • (u - v) = x + t • u - t • v := by module
  have hn : x - t • (u - v) = x - t • u + t • v := by module
  have hnn : x - t • (u + v) = x - t • u - t • v := by module
  simp only [mixedStencil, hp, hm, hn, hnn]

theorem mixedStencil_eq_polarized (r : E → ℝ) (x u v : E) (t : ℝ) :
    mixedStencil r x u v t =
      (directionalSecond r x (u + v) t - directionalSecond r x (u - v) t) / 4 := by
  unfold mixedStencil directionalSecond
  ring

theorem hessian_polarized (f : E → ℝ) (x u v : E) (hf : ContDiffAt ℝ 2 f x) :
    (fderiv ℝ (fderiv ℝ f) x (u + v) (u + v) -
      fderiv ℝ (fderiv ℝ f) x (u - v) (u - v)) / 4 =
      fderiv ℝ (fderiv ℝ f) x u v := by
  have hs := hf.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact le_rfl)
  simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    hs v u]
  ring

/-- The exact mixed stencil has error `(Mplus+Mminus)*t²/48` when the
fourth derivatives on its two query lines have those separate caps. -/
theorem exact_mixedStencil_error (f : E → ℝ) (x u v : E) {t Mplus Mminus : ℝ} (ht : 0 < t)
    (hf₀ : ContDiffAt ℝ 2 f x)
    (hfp : ContDiffOn ℝ 4 (fun s => f (x + s • (u + v))) (Icc (-t) t))
    (hfm : ContDiffOn ℝ 4 (fun s => f (x + s • (u - v))) (Icc (-t) t))
    (hMp : ∀ s ∈ Icc (-t) t, |iteratedDeriv 4 (fun w => f (x + w • (u + v))) s| ≤ Mplus)
    (hMm : ∀ s ∈ Icc (-t) t, |iteratedDeriv 4 (fun w => f (x + w • (u - v))) s| ≤ Mminus) :
    |mixedStencil f x u v t - fderiv ℝ (fderiv ℝ f) x u v| ≤
      (Mplus + Mminus) * t ^ 2 / 48 := by
  have hp := directionalSecond_error f f x (u + v) (ν := 0) ht hf₀ hfp hMp
    (by simp) (by simp) (by simp)
  have hm := directionalSecond_error f f x (u - v) (ν := 0) ht hf₀ hfm hMm
    (by simp) (by simp) (by simp)
  simp only [mul_zero, zero_div, add_zero] at hp hm
  have he : mixedStencil f x u v t - fderiv ℝ (fderiv ℝ f) x u v =
      ((directionalSecond f x (u + v) t - fderiv ℝ (fderiv ℝ f) x (u + v) (u + v)) -
        (directionalSecond f x (u - v) t - fderiv ℝ (fderiv ℝ f) x (u - v) (u - v))) / 4 := by
    rw [mixedStencil_eq_polarized, ← hessian_polarized f x u v hf₀]
    ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  calc
    _ ≤ (Mplus * t ^ 2 / 12 + Mminus * t ^ 2 / 12) / 4 :=
      div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add hp hm)) (by norm_num)
    _ = _ := by ring

/-- Actual four-query value errors contribute `ν/t²`; the center is not queried. -/
theorem mixedStencil_error (f r : E → ℝ) (x u v : E) {t Mplus Mminus ν : ℝ} (ht : 0 < t)
    (hf₀ : ContDiffAt ℝ 2 f x)
    (hfp : ContDiffOn ℝ 4 (fun s => f (x + s • (u + v))) (Icc (-t) t))
    (hfm : ContDiffOn ℝ 4 (fun s => f (x + s • (u - v))) (Icc (-t) t))
    (hMp : ∀ s ∈ Icc (-t) t, |iteratedDeriv 4 (fun w => f (x + w • (u + v))) s| ≤ Mplus)
    (hMm : ∀ s ∈ Icc (-t) t, |iteratedDeriv 4 (fun w => f (x + w • (u - v))) s| ≤ Mminus)
    (hPP : |r (x + t • (u + v)) - f (x + t • (u + v))| ≤ ν)
    (hPM : |r (x + t • (u - v)) - f (x + t • (u - v))| ≤ ν)
    (hMP : |r (x - t • (u - v)) - f (x - t • (u - v))| ≤ ν)
    (hMM : |r (x - t • (u + v)) - f (x - t • (u + v))| ≤ ν) :
    |mixedStencil r x u v t - fderiv ℝ (fderiv ℝ f) x u v| ≤
      (Mplus + Mminus) * t ^ 2 / 48 + ν / t ^ 2 := by
  have hv : |mixedStencil r x u v t - mixedStencil f x u v t| ≤ ν / t ^ 2 :=
    mixed_stencil_report_error _ _ _ _ _ _ _ _ _ _ ht hPP hPM hMP hMM
  have he := exact_mixedStencil_error f x u v ht hf₀ hfp hfm hMp hMm
  exact (abs_sub_le _ (mixedStencil f x u v t) _).trans (by linarith)

/-- For coordinate mixed entries the two unnormalized diagonal lines
usually have fourth-derivative caps `4 M`, giving the conventional
`M t²/6 + ν/t²` error with all Taylor hypotheses already discharged. -/
theorem mixedStencil_error_four_cap (f r : E → ℝ) (x u v : E) {t M ν : ℝ} (ht : 0 < t)
    (hf₀ : ContDiffAt ℝ 2 f x)
    (hfp : ContDiffOn ℝ 4 (fun s => f (x + s • (u + v))) (Icc (-t) t))
    (hfm : ContDiffOn ℝ 4 (fun s => f (x + s • (u - v))) (Icc (-t) t))
    (hMp : ∀ s ∈ Icc (-t) t, |iteratedDeriv 4 (fun w => f (x + w • (u + v))) s| ≤ 4 * M)
    (hMm : ∀ s ∈ Icc (-t) t, |iteratedDeriv 4 (fun w => f (x + w • (u - v))) s| ≤ 4 * M)
    (hPP : |r (x + t • (u + v)) - f (x + t • (u + v))| ≤ ν)
    (hPM : |r (x + t • (u - v)) - f (x + t • (u - v))| ≤ ν)
    (hMP : |r (x - t • (u - v)) - f (x - t • (u - v))| ≤ ν)
    (hMM : |r (x - t • (u + v)) - f (x - t • (u + v))| ≤ ν) :
    |mixedStencil r x u v t - fderiv ℝ (fderiv ℝ f) x u v| ≤
      M * t ^ 2 / 6 + ν / t ^ 2 := by
  have hh := mixedStencil_error f r x u v ht hf₀ hfp hfm hMp hMm hPP hPM hMP hMM
  have he : (4 * M + 4 * M) * t ^ 2 / 48 + ν / t ^ 2 =
      M * t ^ 2 / 6 + ν / t ^ 2 := by ring
  rwa [he] at hh

end Direction
end MatrixSpencer.KSFourthDifference
