import MatrixSpencer.KSCauchyDerivatives
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-!
# Real derivative bounds from complex analytic extensions

Scalar restriction preserves the multilinear derivative norm. Precomposition
with a real continuous linear chart and taking a real linear value functional
therefore transports the quantitative Cauchy bound to actual real derivatives.
This file provides the generic bridge only, not the KS holomorphic extension.
-/

open Set Metric
open scoped ContDiff Topology
noncomputable section
namespace MatrixSpencer.KSCauchyRealBridge
set_option maxHeartbeats 800000

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem norm_iteratedFDeriv_real_eq {f : E → F} {x : E} {k : ℕ}
    (hf : ContDiffAt ℂ k f x) :
    ‖iteratedFDeriv ℝ k f x‖ = ‖iteratedFDeriv ℂ k f x‖ := by
  rw [← hf.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  exact ContinuousMultilinearMap.norm_restrictScalars _

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
/-- Local precomposition formula, so a global smooth extension is unnecessary. -/
theorem iteratedFDeriv_comp_chart {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (L : G →L[ℝ] E) {x : G} (hx : L x ∈ s) (k : ℕ) :
    iteratedFDeriv ℝ k (f ∘ L) x =
      (iteratedFDeriv ℝ k f (L x)).compContinuousLinearMap (fun _ => L) := by
  have hpre := hs.preimage L.continuous
  have hh := L.iteratedFDerivWithin_comp_right hf hs.uniqueDiffOn hpre.uniqueDiffOn hx
    (show (k : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDerivWithin_of_isOpen k hpre hx,
    iteratedFDerivWithin_of_isOpen k hs hx] at hh
  exact hh

theorem norm_iteratedFDeriv_real_chart_le {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℂ ∞ f s) (L : G →L[ℝ] E) (P : F →L[ℝ] H)
    {x : G} (hx : L x ∈ s) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (P ∘ f ∘ L) x‖ ≤
      ‖P‖ * ‖iteratedFDeriv ℂ k f (L x)‖ * ‖L‖ ^ k := by
  have hfr : ContDiffOn ℝ ∞ f s := hf.restrict_scalars ℝ
  have hcomp : ContDiffAt ℝ ∞ (f ∘ L) x :=
    (hfr.contDiffAt (hs.mem_nhds hx)).comp x L.contDiff.contDiffAt
  rw [P.iteratedFDeriv_comp_left hcomp (WithTop.coe_le_coe.mpr le_top),
    iteratedFDeriv_comp_chart hs hfr L hx]
  apply (P.norm_compContinuousMultilinearMap_le _).trans
  have hn := (iteratedFDeriv ℝ k f (L x)).norm_compContinuousLinearMap_le (fun _ : Fin k => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hn
  rw [norm_iteratedFDeriv_real_eq ((hf.contDiffAt (hs.mem_nhds hx)).of_le
    (WithTop.coe_le_coe.mpr le_top))] at hn
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hn (norm_nonneg P)

/-- A bounded complex extension supplies the actual real-chart derivative
caps. The chart and value maps are explicit continuous linear contractions. -/
theorem real_chart_derivatives_le_common_cap {f : E → F} (L : G →L[ℝ] E)
    (P : F →L[ℝ] H) {x : G} {R K : ℝ}
    (hR : 0 < R) (hRone : R ≤ 1) (hK : 0 ≤ K)
    (hL : ‖L‖ ≤ 1) (hP : ‖P‖ ≤ 1)
    (hf : ContDiffOn ℂ ∞ f (ball (L x) R))
    (hbound : ∀ y ∈ ball (L x) R, ‖f y‖ ≤ K) :
    ∀ k : ℕ, 2 ≤ k → k ≤ 4 →
      ‖iteratedFDeriv ℝ k (P ∘ f ∘ L) x‖ ≤ K * (10 / R) ^ 4 := by
  intro k hk₂ hk₄
  have hc := KSCauchyDerivatives.iterated_derivatives_le_common_cap hR hRone hK hf hbound k hk₂ hk₄
  have hh := norm_iteratedFDeriv_real_chart_le isOpen_ball hf L P (mem_ball_self hR) k
  have hpow : ‖L‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg L) hL
  calc _ ≤ ‖P‖ * ‖iteratedFDeriv ℂ k f (L x)‖ * ‖L‖ ^ k := hh
    _ ≤ 1 * (K * (10 / R) ^ 4) * 1 := by gcongr
    _ = _ := by ring

/-- An affine base point is allowed in the complex extension. It has no
effect on the derivative constants or on the real nature of the chart. -/
theorem real_affine_chart_derivatives_le_common_cap {f : E → F} (a : E)
    (L : G →L[ℝ] E) (P : F →L[ℝ] H) {x : G} {R K : ℝ}
    (hR : 0 < R) (hRone : R ≤ 1) (hK : 0 ≤ K)
    (hL : ‖L‖ ≤ 1) (hP : ‖P‖ ≤ 1)
    (hf : ContDiffOn ℂ ∞ f (ball (a + L x) R))
    (hbound : ∀ y ∈ ball (a + L x) R, ‖f y‖ ≤ K) :
    ∀ k : ℕ, 2 ≤ k → k ≤ 4 →
      ‖iteratedFDeriv ℝ k (fun z => P (f (a + L z))) x‖ ≤ K * (10 / R) ^ 4 := by
  have hm : MapsTo (fun y : E => a + y) (ball (L x) R) (ball (a + L x) R) := by
    intro y hy
    simpa only [mem_ball, dist_add_left] using hy
  have hg : ContDiff ℂ ∞ (fun y : E => a + y) := contDiff_const.add contDiff_id
  exact real_chart_derivatives_le_common_cap (f := fun y => f (a + y)) (x := x)
    L P hR hRone hK hL hP
    (hf.comp hg.contDiffOn hm)
    (fun y hy => hbound _ (hm hy))

end MatrixSpencer.KSCauchyRealBridge
