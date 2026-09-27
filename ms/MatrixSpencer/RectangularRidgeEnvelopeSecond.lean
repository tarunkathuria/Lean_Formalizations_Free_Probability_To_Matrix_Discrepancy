import MatrixSpencer.KSEnvelopeFourth

/-! A covariance-envelope estimate that only bounds the covariance column of
the joint Hessian. Density-only regularizers do not enter this column. -/
open Set Filter
open scoped ContDiff Topology
noncomputable section
namespace MatrixSpencer.RectangularRidgeEnvelopeSecond
open KSEnvelopeFourth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance ridgeBlockSecondGroup : NormedAddCommGroup ((ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance ridgeBlockSecondSpace : NormedSpace ℝ ((ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance ridgeBlockHessianGroup : NormedAddCommGroup ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance ridgeBlockHessianSpace : NormedSpace ℝ ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := inferInstance

theorem fderiv_snd_horizontal (r : E → ℝ) (p : ℝ × E) :
    fderiv ℝ (fun q : ℝ × E => r q.2) p (1,0) = 0 := by
  by_cases hd : DifferentiableAt ℝ (fun q : ℝ × E => r q.2) p
  · have hl := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0
      (((hasDerivAt_id (0 : ℝ)).smul_const (((1 : ℝ),(0 : E)))).const_add p) (by simp)
    have he : (fun z : ℝ => (fun q : ℝ × E => r q.2) (p + z • ((1 : ℝ),(0 : E)))) =
        (fun _ : ℝ => r p.2) := by funext z; simp
    simp only [Function.comp_def, id_eq, one_smul] at hl
    rw [he] at hl
    exact hl.unique (hasDerivAt_const 0 (r p.2))
  · rw [fderiv_zero_of_not_differentiableAt hd]
    rfl

theorem second_horizontal_eq_of_first {F G : (ℝ × E) → ℝ} {p : ℝ × E}
    (hF : ContDiffAt ℝ 2 F p) (hG : ContDiffAt ℝ 2 G p)
    (he : ∀ᶠ q : ℝ × E in 𝓝 p, fderiv ℝ F q (1,0) = fderiv ℝ G q (1,0))
    (v : ℝ × E) : second F p v (1,0) = second G p v (1,0) := by
  have hFd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    (hF.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hGd : DifferentiableAt ℝ (fderiv ℝ G) p :=
    (hG.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hf := hFd.hasFDerivAt.clm_apply (hasFDerivAt_const (𝕜 := ℝ) ((1 : ℝ),(0 : E)) p)
  have hg := hGd.hasFDerivAt.clm_apply (hasFDerivAt_const (𝕜 := ℝ) ((1 : ℝ),(0 : E)) p)
  have her : (fun q => fderiv ℝ F q (1,0)) =ᶠ[𝓝 p] (fun q => fderiv ℝ G q (1,0)) := he
  have hh := (hf.congr_of_eventuallyEq her.symm).unique hg
  have hv := DFunLike.congr_fun hh v
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply] using hv

/-- The source Hessian can replace the full objective Hessian in the second
optimized-value estimate when they agree in the covariance column. -/
theorem value_second_le_of_horizontal_block {I : Set ℝ} (hI : IsOpen I) {s : ℝ → E}
    (hs : ContDiffOn ℝ 4 s I) {F : (ℝ × E) → ℝ}
    (hF : ∀ t ∈ I, ContDiffAt ℝ 4 F (lift s t))
    (hstat : ∀ t ∈ I, ∀ u : E, fderiv ℝ F (lift s t) (0,u) = 0)
    {t : ℝ} (ht : t ∈ I) {g B : ℝ} (hg : 0 < g) (hB : 0 ≤ B)
    (Q : (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) (hQ : ‖Q‖ ≤ B)
    (hblock : ∀ v : ℝ × E, second F (lift s t) v (1,0) = Q v (1,0))
    (hcoercive : ∀ u : E, g*‖u‖^2 ≤ -second F (lift s t) (0,u) (0,u)) :
    |iteratedDeriv 2 (fun z => F (lift s z)) t| ≤ B*(1+B/g) := by
  have hfirst : ‖deriv s t‖ ≤ B/g := by
    have hz := stationary_second_reverse hI hs hF hstat ht (deriv s t)
    have he : velocity s t = ((1 : ℝ),(0 : E)) + ((0 : ℝ),deriv s t) := by simp [velocity]
    rw [he, map_add, hblock] at hz
    have hc := hcoercive (deriv s t)
    have hn := norm_second_apply Q ((0 : ℝ),deriv s t) ((1 : ℝ),(0 : E))
    simp only [Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one,
      max_eq_right (norm_nonneg _), mul_one] at hn
    have hb := mul_le_mul_of_nonneg_right hQ (norm_nonneg (deriv s t))
    apply cancel_coercive hg (norm_nonneg _) hB
    have hh := (le_abs_self _).trans (hn.trans hb)
    linarith
  have hv : ‖velocity s t‖ ≤ 1+B/g := by
    simp only [velocity, Prod.norm_def, norm_one]
    exact max_le (by have hh := div_nonneg hB hg.le; linarith) (hfirst.trans (by linarith))
  rw [value_second hI hs hF hstat ht]
  have hz := stationary_second hI hs hF hstat ht (deriv s t)
  have he : second F (lift s t) (velocity s t) (velocity s t) =
      second F (lift s t) (velocity s t) (1,0) := by
    calc
      _ = second F (lift s t) (velocity s t) ((1,0)+(0,deriv s t)) := by
        congr 1
        ext <;> simp [velocity]
      _ = _ := by rw [map_add, hz, add_zero]
  rw [he, hblock]
  have hn := norm_second_apply Q (velocity s t) ((1 : ℝ),(0 : E))
  have hone : ‖((1 : ℝ),(0 : E))‖ = 1 := by simp
  rw [hone,mul_one] at hn
  exact hn.trans (mul_le_mul hQ hv (norm_nonneg _) hB)

end MatrixSpencer.RectangularRidgeEnvelopeSecond
