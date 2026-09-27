import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Module

/-! Strict concavity from the actual Frechet Hessian on an open convex set. -/
open Set Filter Topology
namespace MatrixSpencer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem strictConcaveOn_of_fderiv2_neg {D : Set E} (hD : Convex ℝ D)
    (hopen : IsOpen D) {f : E → ℝ}
    (hf : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hf' : ∀ x ∈ D, DifferentiableAt ℝ (fderiv ℝ f) x)
    (hneg : ∀ x ∈ D, ∀ v : E, v ≠ 0 → fderiv ℝ (fderiv ℝ f) x v v < 0) :
    StrictConcaveOn ℝ D f := by
  refine ⟨hD, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  let v := y - x
  let l : ℝ → E := fun t => x + t • v
  let g : ℝ → ℝ := f ∘ l
  have hv : v ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hl (t : ℝ) : HasDerivAt l v t := by
    simpa only [one_smul] using ((hasDerivAt_id t).smul_const v).const_add x
  have hlc : Continuous l := continuous_const.add (continuous_id.smul continuous_const)
  have hlmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : l t ∈ D := by
    have he : l t = (1 - t) • x + t • y := by dsimp only [l, v]; module
    rw [he]
    exact hD hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hg (t : ℝ) (ht : l t ∈ D) : HasDerivAt g (fderiv ℝ f (l t) v) t :=
    (hf (l t) ht).hasFDerivAt.comp_hasDerivAt t (hl t)
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) :=
    fun t ht => (hg t (hlmem t ht)).continuousAt.continuousWithinAt
  have hg2 (t : ℝ) (ht : l t ∈ D) : deriv (deriv g) t =
      fderiv ℝ (fderiv ℝ f) (l t) v v := by
    have haux := ((hf' (l t) ht).hasFDerivAt.comp_hasDerivAt t (hl t)).clm_apply
      (hasDerivAt_const t v)
    have hd : HasDerivAt (fun s => fderiv ℝ f (l s) v)
        (fderiv ℝ (fderiv ℝ f) (l t) v v) t := by
      simpa only [ContinuousLinearMap.map_zero, zero_add, add_zero, Function.comp_def] using haux
    have he : (fun s => fderiv ℝ f (l s) v) =ᶠ[𝓝 t] deriv g := by
      filter_upwards [hlc.continuousAt (hopen.mem_nhds ht)] with s hs
      exact (hg s hs).deriv.symm
    exact (hd.congr_of_eventuallyEq he.symm).deriv
  have hgstrict : StrictConcaveOn ℝ (Icc (0 : ℝ) 1) g := by
    apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) hgc
    intro t ht
    have htm := hlmem t (interior_subset ht)
    change deriv (deriv g) t < 0
    rw [hg2 t htm]
    exact hneg (l t) htm v hv
  have hineq := hgstrict.2 (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) ≠ 1) ha hb hab
  have hzero : g 0 = f x := by simp [g, l]
  have hone : g 1 = f y := by simp [g, l, v]
  have hlb : l b = a • x + b • y := by
    have hae : a = 1 - b := by linarith
    rw [hae]
    dsimp only [l, v]
    module
  have hi : a * g 0 + b * g 1 < g b := by
    simpa only [smul_eq_mul, mul_zero, mul_one, zero_add] using hineq
  rw [hzero, hone] at hi
  change a * f x + b * f y < f (l b) at hi
  rwa [hlb] at hi

end MatrixSpencer
