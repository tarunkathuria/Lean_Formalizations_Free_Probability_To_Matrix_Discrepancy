import MatrixSpencer.KSFourthDifference

/-! The new algorithm needs a uniform third derivative, not a fourth
derivative. These estimates derive its actual centered value stencils from
the Lagrange Taylor theorem. Source-specific hypotheses are discharged in
separate analytic modules; they are explicit here as intermediate lemmas. -/

open Set
open scoped Topology
noncomputable section
namespace HigherRankKSRuntime.ThirdDifference

def quadratic (f0 d1 d2 t : ℝ) : ℝ := f0 + d1 * t + d2 * t ^ 2 / 2

theorem quadratic_symmetric_sum (f0 d1 d2 t : ℝ) :
    quadratic f0 d1 d2 t + quadratic f0 d1 d2 (-t) = 2 * f0 + d2 * t ^ 2 := by
  unfold quadratic
  ring

theorem taylor_quadratic_eq (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t)
    (hd : ContDiffAt ℝ 2 f 0) :
    taylorWithinEval f 2 (Icc 0 t) 0 t =
      quadratic (f 0) (deriv f 0) (iteratedDeriv 2 f 0) t := by
  have h₁ : iteratedDerivWithin 1 f (Icc 0 t) 0 = iteratedDeriv 1 f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht) (hd.of_le (by norm_num))
      (left_mem_Icc.mpr ht.le)
  have h₂ : iteratedDerivWithin 2 f (Icc 0 t) 0 = iteratedDeriv 2 f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht) hd (left_mem_Icc.mpr ht.le)
  norm_num [taylorWithinEval_succ, taylor_within_zero_eval, h₁, h₂,
    iteratedDeriv_one, quadratic]
  ring

theorem positive_remainder (f : ℝ → ℝ) {t M : ℝ} (ht : 0 < t)
    (hf : ContDiffOn ℝ 3 f (Icc 0 t)) (hd : ContDiffAt ℝ 2 f 0)
    (hM : ∀ u ∈ Ioo 0 t, |iteratedDeriv 3 f u| ≤ M) :
    |f t - quadratic (f 0) (deriv f 0) (iteratedDeriv 2 f 0) t| ≤
      M * t ^ 3 / 6 := by
  obtain ⟨u, hu, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) ht hf
  rw [taylor_quadratic_eq f ht hd] at hrem
  norm_num at hrem
  rw [hrem, abs_div, abs_mul, abs_of_nonneg (pow_nonneg ht.le 3)]
  norm_num
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hM u hu) (pow_nonneg ht.le 3)) (by norm_num)

theorem signed_remainders (f : ℝ → ℝ) {t M : ℝ} (ht : 0 < t)
    (hf : ContDiffOn ℝ 3 f (Icc (-t) t))
    (hM : ∀ u ∈ Icc (-t) t, |iteratedDeriv 3 f u| ≤ M) :
    |f t - quadratic (f 0) (deriv f 0) (iteratedDeriv 2 f 0) t| ≤ M * t ^ 3 / 6 ∧
    |f (-t) - quadratic (f 0) (deriv f 0) (iteratedDeriv 2 f 0) (-t)| ≤ M * t ^ 3 / 6 := by
  have hd : ContDiffAt ℝ 2 f 0 :=
    (hf.contDiffAt (Icc_mem_nhds_iff.mpr ⟨by linarith, ht⟩)).of_le (by norm_num)
  have hfp : ContDiffOn ℝ 3 f (Icc 0 t) :=
    hf.mono (by intro u hu; constructor <;> linarith [hu.1, hu.2])
  have hp := positive_remainder f ht hfp hd
    (fun u hu => hM u ⟨by linarith [hu.1], hu.2.le⟩)
  have hfn : ContDiffOn ℝ 3 (fun u => f (-u)) (Icc 0 t) :=
    hf.comp contDiff_neg.contDiffOn (by intro u hu; constructor <;> linarith [hu.1, hu.2])
  have hdn : ContDiffAt ℝ 2 (fun u => f (-u)) 0 := by
    exact (show ContDiffAt ℝ 2 f (-(0 : ℝ)) by simpa using hd).comp 0 contDiff_neg.contDiffAt
  have hMn (u : ℝ) (hu : u ∈ Ioo 0 t) : |iteratedDeriv 3 (fun v => f (-v)) u| ≤ M := by
    rw [iteratedDeriv_comp_neg]
    simpa using hM (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hn := positive_remainder (fun u => f (-u)) ht hfn hdn hMn
  have hc : quadratic (f (-(0 : ℝ))) (deriv (fun u => f (-u)) 0)
      (iteratedDeriv 2 (fun u => f (-u)) 0) t =
      quadratic (f 0) (deriv f 0) (iteratedDeriv 2 f 0) (-t) := by
    simp only [deriv_comp_neg, iteratedDeriv_comp_neg, neg_zero]
    norm_num [quadratic]
  exact ⟨hp, by rwa [hc] at hn⟩

theorem symmetric_average_error_zero (f : ℝ → ℝ) {t M : ℝ} (ht : 0 < t)
    (hf : ContDiffOn ℝ 3 f (Icc (-t) t))
    (hM : ∀ u ∈ Icc (-t) t, |iteratedDeriv 3 f u| ≤ M) :
    |(f t + f (-t)) / 2 - f 0 - iteratedDeriv 2 f 0 * t ^ 2 / 2| ≤ M * t ^ 3 / 6 := by
  obtain ⟨hp, hm⟩ := signed_remainders f ht hf hM
  have hs := quadratic_symmetric_sum (f 0) (deriv f 0) (iteratedDeriv 2 f 0) t
  obtain ⟨hpL, hpU⟩ := abs_le.mp hp
  obtain ⟨hmL, hmU⟩ := abs_le.mp hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem secondStencil_error_zero (f r : ℝ → ℝ) {t M ν : ℝ} (ht : 0 < t)
    (hf : ContDiffOn ℝ 3 f (Icc (-t) t))
    (hM : ∀ u ∈ Icc (-t) t, |iteratedDeriv 3 f u| ≤ M)
    (hp : |r t - f t| ≤ ν) (hz : |r 0 - f 0| ≤ ν) (hm : |r (-t) - f (-t)| ≤ ν) :
    |MatrixSpencer.KSFourthDifference.secondStencil r 0 t - iteratedDeriv 2 f 0| ≤
      M * t / 3 + 4 * ν / t ^ 2 := by
  have ht₂ : 0 < t ^ 2 := sq_pos_of_pos ht
  have hrem := symmetric_average_error_zero f ht hf hM
  obtain ⟨hrL, hrU⟩ := abs_le.mp hrem
  obtain ⟨hpL, hpU⟩ := abs_le.mp hp
  obtain ⟨hzL, hzU⟩ := abs_le.mp hz
  obtain ⟨hmL, hmU⟩ := abs_le.mp hm
  have hn : |r t - 2 * r 0 + r (-t) - iteratedDeriv 2 f 0 * t ^ 2| ≤
      M * t ^ 3 / 3 + 4 * ν := abs_le.mpr ⟨by linarith, by linarith⟩
  have he : MatrixSpencer.KSFourthDifference.secondStencil r 0 t - iteratedDeriv 2 f 0 =
      (r t - 2 * r 0 + r (-t) - iteratedDeriv 2 f 0 * t ^ 2) / t ^ 2 := by
    simp only [MatrixSpencer.KSFourthDifference.secondStencil, zero_add, zero_sub]
    field_simp
  rw [he, abs_div, abs_of_pos ht₂]
  calc
    _ ≤ (M * t ^ 3 / 3 + 4 * ν) / t ^ 2 := div_le_div_of_nonneg_right hn ht₂.le
    _ = _ := by field_simp

section Direction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
open MatrixSpencer.KSFourthDifference

theorem directionalSecond_error (f r : E → ℝ) (x v : E) {t M ν : ℝ} (ht : 0 < t)
    (hf₀ : ContDiffAt ℝ 2 f x)
    (hf : ContDiffOn ℝ 3 (fun u => f (x + u • v)) (Icc (-t) t))
    (hM : ∀ u ∈ Icc (-t) t, |iteratedDeriv 3 (fun w => f (x + w • v)) u| ≤ M)
    (hp : |r (x + t • v) - f (x + t • v)| ≤ ν)
    (hz : |r x - f x| ≤ ν) (hm : |r (x - t • v) - f (x - t • v)| ≤ ν) :
    |directionalSecond r x v t - fderiv ℝ (fderiv ℝ f) x v v| ≤
      M * t / 3 + 4 * ν / t ^ 2 := by
  have hh := secondStencil_error_zero (fun u => f (x + u • v))
    (fun u => r (x + u • v)) ht hf hM hp
    (by simpa only [zero_smul, add_zero] using hz)
    (by simpa only [neg_smul, sub_eq_add_neg] using hm)
  rwa [← directionalSecond_eq_curve, line_second f x v hf₀] at hh

theorem directional_average_le (f : E → ℝ) (x v : E) {t M : ℝ} (ht : 0 < t)
    (hf₀ : ContDiffAt ℝ 2 f x)
    (hf : ContDiffOn ℝ 3 (fun u => f (x + u • v)) (Icc (-t) t))
    (hM : ∀ u ∈ Icc (-t) t, |iteratedDeriv 3 (fun w => f (x + w • v)) u| ≤ M) :
    (f (x + t • v) + f (x - t • v)) / 2 ≤ f x +
      fderiv ℝ (fderiv ℝ f) x v v * t ^ 2 / 2 + M * t ^ 3 / 6 := by
  have hh := (abs_le.mp (symmetric_average_error_zero (fun u => f (x + u • v)) ht hf hM)).2
  rw [line_second f x v hf₀] at hh
  simp only [zero_smul, add_zero, neg_smul, ← sub_eq_add_neg] at hh
  linarith

theorem exact_mixedStencil_error (f : E → ℝ) (x u v : E) {t Mplus Mminus : ℝ} (ht : 0 < t)
    (hf₀ : ContDiffAt ℝ 2 f x)
    (hfp : ContDiffOn ℝ 3 (fun s => f (x + s • (u + v))) (Icc (-t) t))
    (hfm : ContDiffOn ℝ 3 (fun s => f (x + s • (u - v))) (Icc (-t) t))
    (hMp : ∀ s ∈ Icc (-t) t, |iteratedDeriv 3 (fun w => f (x + w • (u + v))) s| ≤ Mplus)
    (hMm : ∀ s ∈ Icc (-t) t, |iteratedDeriv 3 (fun w => f (x + w • (u - v))) s| ≤ Mminus) :
    |mixedStencil f x u v t - fderiv ℝ (fderiv ℝ f) x u v| ≤
      (Mplus + Mminus) * t / 12 := by
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
    _ ≤ (Mplus * t / 3 + Mminus * t / 3) / 4 :=
      div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add hp hm)) (by norm_num)
    _ = _ := by ring

/-- Actual four-query value errors contribute `ν/t²`; the center is not queried. -/
theorem mixedStencil_error (f r : E → ℝ) (x u v : E) {t Mplus Mminus ν : ℝ} (ht : 0 < t)
    (hf₀ : ContDiffAt ℝ 2 f x)
    (hfp : ContDiffOn ℝ 3 (fun s => f (x + s • (u + v))) (Icc (-t) t))
    (hfm : ContDiffOn ℝ 3 (fun s => f (x + s • (u - v))) (Icc (-t) t))
    (hMp : ∀ s ∈ Icc (-t) t, |iteratedDeriv 3 (fun w => f (x + w • (u + v))) s| ≤ Mplus)
    (hMm : ∀ s ∈ Icc (-t) t, |iteratedDeriv 3 (fun w => f (x + w • (u - v))) s| ≤ Mminus)
    (hPP : |r (x + t • (u + v)) - f (x + t • (u + v))| ≤ ν)
    (hPM : |r (x + t • (u - v)) - f (x + t • (u - v))| ≤ ν)
    (hMP : |r (x - t • (u - v)) - f (x - t • (u - v))| ≤ ν)
    (hMM : |r (x - t • (u + v)) - f (x - t • (u + v))| ≤ ν) :
    |mixedStencil r x u v t - fderiv ℝ (fderiv ℝ f) x u v| ≤
      (Mplus + Mminus) * t / 12 + ν / t ^ 2 := by
  have hv : |mixedStencil r x u v t - mixedStencil f x u v t| ≤ ν / t ^ 2 :=
    MatrixSpencer.KSFiniteDifference.mixed_stencil_report_error
      _ _ _ _ _ _ _ _ _ _ ht hPP hPM hMP hMM
  have he := exact_mixedStencil_error f x u v ht hf₀ hfp hfm hMp hMm
  exact (abs_sub_le _ (mixedStencil f x u v t) _).trans (by linarith)


end Direction
end HigherRankKSRuntime.ThirdDifference
