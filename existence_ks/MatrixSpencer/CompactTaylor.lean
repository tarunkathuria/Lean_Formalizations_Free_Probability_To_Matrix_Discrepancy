import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Topology.Compactness.Compact

/-! Uniform second-order Taylor remainders for compact families of scalar slices. -/

open Set Filter
open scoped Topology ContDiff

namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Actual second derivative in the scalar slice direction. -/
def scalarSliceSecond (g : P × ℝ → ℝ) (q : P × ℝ) : ℝ :=
  iteratedFDeriv ℝ 2 g q (fun _ => (0, 1))

theorem iteratedDeriv_scalar_slice_two (g : P × ℝ → ℝ) (p : P) (t : ℝ)
    (hg : ContDiffAt ℝ 2 g (p, t)) :
    iteratedDeriv 2 (fun s => g (p, s)) t = scalarSliceSecond g (p, t) := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => (p, r)) (0, 1) s :=
    (hasDerivAt_const s p).prodMk (hasDerivAt_id s)
  have hdf : deriv (fun r : ℝ => (p, r)) = fun _ => (0, 1) := funext fun s => (hd s).deriv
  have hdd : iteratedDeriv 2 (fun r : ℝ => (p, r)) t = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hdf]
    exact deriv_const t (0, 1)
  have he := iteratedDeriv_vcomp_two hg
    (contDiffAt_const.prodMk contDiffAt_id : ContDiffAt ℝ 2 (fun r : ℝ => (p, r)) t)
  simpa only [Function.comp_def, hdf, hdd, map_zero, add_zero, scalarSliceSecond] using he

theorem continuousAt_scalarSliceSecond (g : P × ℝ → ℝ) (q : P × ℝ)
    (hg : ContDiffAt ℝ 2 g q) : ContinuousAt (scalarSliceSecond g) q :=
  (hg.iteratedFDeriv_right (m := 0) (i := 2) (by norm_num)).continuousAt.eval_const _

/-- On a compact parameter set, the second-order scalar Taylor error is uniformly o(h²).
The assumption is actual joint C² at each base point, not a uniform remainder premise. -/
theorem compact_uniform_scalar_taylor_two
    (g : P × ℝ → ℝ) (K : Set P) (hK : IsCompact K)
    (hg : ∀ p ∈ K, ContDiffAt ℝ 2 g (p, 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ K, ∀ h ∈ Icc (0 : ℝ) δ,
      |g (p, h) - g (p, 0) - h * deriv (fun t => g (p, t)) 0 -
        h ^ 2 / 2 * iteratedDeriv 2 (fun t => g (p, t)) 0| ≤ ε * h ^ 2 := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ p ∈ K,
      ContDiffAt ℝ 2 g (p, t) ∧ |scalarSliceSecond g (p, t) - scalarSliceSecond g (p, 0)| < ε := by
    apply hK.eventually_forall_of_forall_eventually
    intro p hp
    have hgp := hg p hp
    have hswap : ContinuousAt (fun z : ℝ × P => (z.2, z.1)) (0, p) := continuousAt_snd.prodMk continuousAt_fst
    have hbase : ContinuousAt (fun z : ℝ × P => (z.2, (0 : ℝ))) (0, p) :=
      continuousAt_snd.prodMk continuousAt_const
    have hc := continuousAt_scalarSliceSecond g (p, 0) hgp
    have hdiff := ((ContinuousAt.comp (g := scalarSliceSecond g)
      (f := fun z : ℝ × P => (z.2, z.1)) hc hswap).sub
      (ContinuousAt.comp (g := scalarSliceSecond g)
        (f := fun z : ℝ × P => (z.2, (0 : ℝ))) hc hbase)).norm
    have hsmall : ∀ᶠ z : ℝ × P in 𝓝 (0, p),
        |scalarSliceSecond g (z.2, z.1) - scalarSliceSecond g (z.2, 0)| < ε := by
      simpa only [Function.comp_apply, Real.norm_eq_abs, sub_self, abs_zero] using
        hdiff.eventually (gt_mem_nhds (by simpa only [Function.comp_apply, sub_self, norm_zero] using hε))
    filter_upwards [hswap.eventually (hgp.eventually (by norm_num)), hsmall] with z hz hs
    exact ⟨hz, hs⟩
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r / 2, by positivity, ?_⟩
  intro p hp h hh
  rcases hh.1.eq_or_lt with hzero | hpos
  · subst h
    simp
  have hnear (s : ℝ) (hs : s ∈ Icc (0 : ℝ) h) : dist s 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    exact hs.2.trans_lt (hh.2.trans_lt (by linarith))
  have hslice : ContDiffOn ℝ 2 (fun t : ℝ => g (p, t)) (Icc 0 h) := by
    intro s hs
    exact (((hb (hnear s hs)) p hp).1.comp s (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  obtain ⟨s, hs, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hpos hslice
  have hsd : ContDiffAt ℝ 2 (fun t : ℝ => g (p, t)) 0 :=
    (hg p hp).comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have hdw : derivWithin (fun t : ℝ => g (p, t)) (Icc 0 h) 0 = deriv (fun t : ℝ => g (p, t)) 0 :=
    hsd.differentiableAt (by norm_num) |>.hasDerivAt.hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc hpos) 0 (left_mem_Icc.mpr hpos.le))
  have hpoly : taylorWithinEval (fun t => g (p, t)) 1 (Icc 0 h) 0 h =
      g (p, 0) + h * deriv (fun t => g (p, t)) 0 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval,
      iteratedDerivWithin_one, hdw]
    norm_num
  rw [hpoly, iteratedDeriv_scalar_slice_two g p s ((hb (hnear s ⟨hs.1.le, hs.2.le⟩)) p hp).1] at hrem
  have hsmall := ((hb (hnear s ⟨hs.1.le, hs.2.le⟩)) p hp).2
  rw [iteratedDeriv_scalar_slice_two g p 0 (hg p hp)]
  have he : g (p, h) - g (p, 0) - h * deriv (fun t => g (p, t)) 0 -
      h ^ 2 / 2 * scalarSliceSecond g (p, 0) =
      (scalarSliceSecond g (p, s) - scalarSliceSecond g (p, 0)) * h ^ 2 / 2 := by
    norm_num at hrem
    linarith
  rw [he, abs_div, abs_mul, abs_of_nonneg (sq_nonneg h)]
  norm_num
  calc
    |scalarSliceSecond g (p, s) - scalarSliceSecond g (p, 0)| * h ^ 2 / 2 ≤ ε * h ^ 2 / 2 := by
      gcongr
    _ ≤ ε * h ^ 2 := by nlinarith [mul_nonneg hε.le (sq_nonneg h)]

section MatchedCurve
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A linear displacement and a simultaneous quadratic displacement. -/
def matchedCurve (p : E × E × E) (h : ℝ) : E := p.1 + h • p.2.1 + h ^ 2 • p.2.2

@[simp] theorem matchedCurve_zero (p : E × E × E) : matchedCurve p 0 = p.1 := by
  simp [matchedCurve]

theorem contDiff_matchedCurve :
    ContDiff ℝ ∞ (fun q : (E × E × E) × ℝ => matchedCurve q.1 q.2) := by
  unfold matchedCurve
  fun_prop

theorem hasDerivAt_matchedCurve (p : E × E × E) (t : ℝ) :
    HasDerivAt (matchedCurve p) (p.2.1 + (2 * t) • p.2.2) t := by
  have h := ((hasDerivAt_const t p.1).add ((hasDerivAt_id t).smul_const p.2.1)).add
    (((hasDerivAt_id t).pow 2).smul_const p.2.2)
  simpa only [zero_add, one_smul, pow_one, Nat.cast_ofNat, mul_one, matchedCurve, id_eq, Nat.reduceSub, Pi.add_apply, Pi.pow_apply] using h

theorem iteratedDeriv_matchedCurve_two (p : E × E × E) (t : ℝ) :
    iteratedDeriv 2 (matchedCurve p) t = (2 : ℝ) • p.2.2 := by
  have hd : deriv (matchedCurve p) = fun s => p.2.1 + (2 * s) • p.2.2 :=
    funext fun s => (hasDerivAt_matchedCurve p s).deriv
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd]
  have h := (hasDerivAt_const t p.2.1).add (((hasDerivAt_id t).const_mul 2).smul_const p.2.2)
  simpa only [mul_one, zero_add] using h.deriv

theorem deriv_comp_matchedCurve_zero (f : E → ℝ) (p : E × E × E)
    (hf : ContDiffAt ℝ 2 f p.1) :
    deriv (fun h => f (matchedCurve p h)) 0 = fderiv ℝ f p.1 p.2.1 := by
  have hf' : ContDiffAt ℝ 2 f (matchedCurve p 0) := by simpa only [matchedCurve_zero] using hf
  have hd := (hf'.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_matchedCurve p 0)
  simpa only [matchedCurve_zero, mul_zero, zero_smul, add_zero] using hd.deriv

theorem iteratedDeriv_comp_matchedCurve_two_zero (f : E → ℝ) (p : E × E × E)
    (hf : ContDiffAt ℝ 2 f p.1) :
    iteratedDeriv 2 (fun h => f (matchedCurve p h)) 0 =
      fderiv ℝ (fderiv ℝ f) p.1 p.2.1 p.2.1 + 2 * fderiv ℝ f p.1 p.2.2 := by
  have hf' : ContDiffAt ℝ 2 f (matchedCurve p 0) := by simpa only [matchedCurve_zero] using hf
  have hc : ContDiffAt ℝ 2 (matchedCurve p) 0 :=
    ((contDiff_matchedCurve (E := E)).contDiffAt.comp 0 (contDiffAt_const.prodMk contDiffAt_id)).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have he := iteratedDeriv_vcomp_two hf' hc
  simpa only [Function.comp_def, matchedCurve_zero, (hasDerivAt_matchedCurve p 0).deriv,
    mul_zero, zero_smul, add_zero, iteratedDeriv_matchedCurve_two, map_smul,
    smul_eq_mul, iteratedFDeriv_two_apply] using he

/-- Compact uniform matched-step Taylor expansion in any real normed vector space. -/
theorem compact_uniform_matched_taylor_two
    (f : E → ℝ) (K : Set (E × E × E)) (hK : IsCompact K)
    (hf : ∀ p ∈ K, ContDiffAt ℝ 2 f p.1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ K, ∀ h ∈ Icc (0 : ℝ) δ,
      |f (matchedCurve p h) - f p.1 - h * fderiv ℝ f p.1 p.2.1 -
        h ^ 2 * ((1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) p.1 p.2.1 p.2.1 +
          fderiv ℝ f p.1 p.2.2)| ≤ ε * h ^ 2 := by
  let g : (E × E × E) × ℝ → ℝ := fun q => f (matchedCurve q.1 q.2)
  have hg (p : E × E × E) (hp : p ∈ K) : ContDiffAt ℝ 2 g (p, 0) := by
    have hfp : ContDiffAt ℝ 2 f (matchedCurve p 0) := by simpa only [matchedCurve_zero] using hf p hp
    exact hfp.comp (p, 0) ((contDiff_matchedCurve (E := E)).contDiffAt.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
  obtain ⟨δ, hδ, hb⟩ := compact_uniform_scalar_taylor_two g K hK hg hε
  refine ⟨δ, hδ, ?_⟩
  intro p hp h hh
  have hbound := hb p hp h hh
  change |f (matchedCurve p h) - f (matchedCurve p 0) -
    h * deriv (fun t => f (matchedCurve p t)) 0 -
    h ^ 2 / 2 * iteratedDeriv 2 (fun t => f (matchedCurve p t)) 0| ≤ _ at hbound
  rw [matchedCurve_zero, deriv_comp_matchedCurve_zero f p (hf p hp),
    iteratedDeriv_comp_matchedCurve_two_zero f p (hf p hp)] at hbound
  convert hbound using 1
  congr 1
  ring

end MatchedCurve

end
end MatrixSpencer
