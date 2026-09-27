import MatrixSpencer.CompactTaylor
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! A negative direction of the actual Hessian excludes a local minimum.
This uses a proved Taylor estimate, rather than an assumed local-descent oracle. -/

open Set Filter
open scoped Topology

namespace MatrixSpencer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ks_not_isLocalMin_of_hessian_neg
    (f : E → ℝ) (x v : E) (hf : ContDiffAt ℝ 2 f x)
    (hneg : fderiv ℝ (fderiv ℝ f) x v v < 0) : ¬ IsLocalMin f x := by
  intro hmin
  let q := fderiv ℝ (fderiv ℝ f) x v v
  have hq : q < 0 := hneg
  have hε : 0 < -q / 4 := by linarith
  obtain ⟨δ, hδ, hTaylor⟩ := compact_uniform_matched_taylor_two f
    ({(x, v, (0 : E))} : Set (E × E × E)) isCompact_singleton
    (by intro p hp; simpa only [Set.mem_singleton_iff.mp hp] using hf) hε
  have hz : fderiv ℝ f x = 0 := hmin.fderiv_eq_zero
  have htend : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa using hc.continuousAt.tendsto (x := (0 : ℝ))
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, f x ≤ f (x + t • v) := htend.eventually hmin
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let t := min δ r / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htδ : t ≤ δ := by dsimp [t]; linarith [min_le_left δ r]
  have htr : dist t 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    dsimp [t]
    linarith [min_le_right δ r]
  have hval := hball htr
  have hrem := hTaylor (x, v, 0) (by simp) t ⟨ht.le, htδ⟩
  simp only [matchedCurve, hz, ContinuousLinearMap.zero_apply, map_zero,
    smul_zero, add_zero, mul_zero, sub_zero] at hrem
  have hu := (abs_le.mp hrem).2
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  change f (x + t • v) - f x - t ^ 2 * ((1 / 2 : ℝ) * q) ≤ -q / 4 * t ^ 2 at hu
  have : q * t ^ 2 < 0 := mul_neg_of_neg_of_pos hq ht2
  nlinarith

end MatrixSpencer
