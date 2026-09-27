import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Fourth derivatives of stationary envelopes

On an open real parameter interval, a `C⁴` stationary branch for a `C⁴`
objective satisfies the exact fourth envelope identity. Every derivative is
an actual `deriv` or `fderiv`; the mixed cancellations are proved by twice
differentiating vertical stationarity. No response or envelope identity is
assumed.

The quantitative corollaries derive first and second branch derivative bounds
from density Hessian coercivity and explicit joint derivative caps. They then
prove the bound `(B + 3*B^2/g) * (1+B/g)^4` used for the outer Taylor estimate.
All norms are those of the stated normed coordinates; the joint product uses
its usual maximum norm. A trace-zero density chart can serve as the fiber.

This is reusable local calculus. Instantiating it for the actual KS optimized
potential still requires the explicit joint derivative cap and the chart's
stationarity/smoothness identifications. It does not assert that those final
analytic inputs or the numerical outer mesh have been discharged.
-/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace MatrixSpencer.KSEnvelopeFourth
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Joint (E : Type*) := ℝ × E
local instance : NormedAddCommGroup (Joint E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (Joint E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (Joint E →L[ℝ] Joint E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (Joint E →L[ℝ] Joint E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (Joint E →L[ℝ] Joint E →L[ℝ] Joint E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (Joint E →L[ℝ] Joint E →L[ℝ] Joint E →L[ℝ] ℝ) := inferInstance

def lift (s : ℝ → E) (t : ℝ) : Joint E := (t, s t)
def velocity (s : ℝ → E) (t : ℝ) : Joint E := (1, deriv s t)
def acceleration (s : ℝ → E) (t : ℝ) : Joint E := (0, deriv (deriv s) t)
abbrev second (F : Joint E → ℝ) := fderiv ℝ (fderiv ℝ F)
abbrev third (F : Joint E → ℝ) := fderiv ℝ (second F)
abbrev fourth (F : Joint E → ℝ) := fderiv ℝ (third F)

theorem norm_second_apply (A : Joint E →L[ℝ] Joint E →L[ℝ] ℝ) (u v : Joint E) :
    |A u v| ≤ ‖A‖ * ‖u‖ * ‖v‖ := by
  calc |A u v| ≤ ‖A u‖ * ‖v‖ := by simpa only [Real.norm_eq_abs] using (A u).le_opNorm v
    _ ≤ _ := mul_le_mul_of_nonneg_right (A.le_opNorm u) (norm_nonneg v)

theorem norm_third_apply (A : Joint E →L[ℝ] Joint E →L[ℝ] Joint E →L[ℝ] ℝ)
    (u v w : Joint E) : |A u v w| ≤ ‖A‖ * ‖u‖ * ‖v‖ * ‖w‖ := by
  calc |A u v w| ≤ ‖A u‖ * ‖v‖ * ‖w‖ := norm_second_apply (A u) v w
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (A.le_opNorm u) (norm_nonneg v)) (norm_nonneg w)

theorem norm_fourth_apply
    (A : Joint E →L[ℝ] Joint E →L[ℝ] Joint E →L[ℝ] Joint E →L[ℝ] ℝ)
    (u v w z : Joint E) : |A u v w z| ≤ ‖A‖ * ‖u‖ * ‖v‖ * ‖w‖ * ‖z‖ := by
  calc |A u v w z| ≤ ‖A u‖ * ‖v‖ * ‖w‖ * ‖z‖ := norm_third_apply (A u) v w z
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (A.le_opNorm u) (norm_nonneg v)) (norm_nonneg w)) (norm_nonneg z)

/-- Scalar cancellation used in both differentiated stationarity estimates. -/
theorem cancel_coercive {g x C : ℝ} (hg : 0 < g) (hx : 0 ≤ x) (hC : 0 ≤ C)
    (h : g * x ^ 2 ≤ C * x) : x ≤ C / g := by
  by_cases hz : x = 0
  · rw [hz]; positivity
  · have hp : 0 < x := hx.lt_of_ne' hz
    apply (le_div_iff₀ hg).mpr
    nlinarith

variable {I : Set ℝ} (hI : IsOpen I) {s : ℝ → E}
  (hs : ContDiffOn ℝ 4 s I) {F : Joint E → ℝ}
  (hF : ∀ t ∈ I, ContDiffAt ℝ 4 F (lift s t))
  (hstat : ∀ t ∈ I, ∀ u : E, fderiv ℝ F (lift s t) (0,u) = 0)

include hI hs

theorem hasDerivAt_lift {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (lift s) (velocity s t) t :=
  (hasDerivAt_id t).prodMk ((hs.contDiffAt (hI.mem_nhds ht)).differentiableAt (by norm_num)).hasDerivAt

theorem hasDerivAt_velocity {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (velocity s) (acceleration s t) t :=
  (hasDerivAt_const t (1 : ℝ)).prodMk
    (((hs.deriv_of_isOpen hI (by norm_num : (3 : WithTop ℕ∞) + 1 ≤ 4)).contDiffAt
      (hI.mem_nhds ht)).differentiableAt (by norm_num)).hasDerivAt

include hF

theorem hasDerivAt_first_along {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun z => fderiv ℝ F (lift s z))
      (second F (lift s t) (velocity s t)) t :=
  (((hF t ht).fderiv_right (by norm_num : (3 : WithTop ℕ∞) + 1 ≤ 4)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_lift hI hs ht)

theorem hasDerivAt_second_along {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun z => second F (lift s z))
      (third F (lift s t) (velocity s t)) t :=
  ((((hF t ht).fderiv_right (by norm_num : (3 : WithTop ℕ∞) + 1 ≤ 4)).fderiv_right
    (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_lift hI hs ht)

theorem hasDerivAt_third_along {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun z => third F (lift s z))
      (fourth F (lift s t) (velocity s t)) t :=
  (((((hF t ht).fderiv_right (by norm_num : (3 : WithTop ℕ∞) + 1 ≤ 4)).fderiv_right
    (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt le_rfl).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_lift hI hs ht)

include hstat

/-- Differentiating the actual vertical stationarity equation once. -/
theorem stationary_second {t : ℝ} (ht : t ∈ I) (u : E) :
    second F (lift s t) (velocity s t) (0,u) = 0 := by
  have hd := (hasDerivAt_first_along hI hs hF ht).clm_apply
    (hasDerivAt_const t ((0 : ℝ),u))
  have he : (fun z => fderiv ℝ F (lift s z) (0,u)) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    filter_upwards [hI.mem_nhds ht] with z hz
    exact hstat z hz u
  have hz := hd.congr_of_eventuallyEq he.symm
  simpa only [map_zero, add_zero] using hz.unique (hasDerivAt_const t (0 : ℝ))

/-- Differentiating vertical stationarity twice, with a fixed vertical test. -/
theorem stationary_third {t : ℝ} (ht : t ∈ I) (u : E) :
    third F (lift s t) (velocity s t) (velocity s t) (0,u) +
      second F (lift s t) (acceleration s t) (0,u) = 0 := by
  have hd := ((hasDerivAt_second_along hI hs hF ht).clm_apply
    (hasDerivAt_velocity hI hs ht)).clm_apply (hasDerivAt_const t ((0 : ℝ),u))
  have he : (fun z => second F (lift s z) (velocity s z) (0,u)) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    filter_upwards [hI.mem_nhds ht] with z hz
    exact stationary_second hI hs hF hstat hz u
  have hz := hd.congr_of_eventuallyEq he.symm
  simpa only [ContinuousLinearMap.add_apply, map_zero, add_zero] using
    hz.unique (hasDerivAt_const t (0 : ℝ))


/-- The reverse mixed second derivative also vanishes by Hessian symmetry. -/
theorem stationary_second_reverse {t : ℝ} (ht : t ∈ I) (u : E) :
    second F (lift s t) (0,u) (velocity s t) = 0 := by
  rw [((hF t ht).isSymmSndFDerivAt (by norm_num)).eq]
  exact stationary_second hI hs hF hstat ht u

/-- Differentiating the reverse mixed stationarity identity. -/
theorem stationary_third_reverse {t : ℝ} (ht : t ∈ I) (u : E) :
    third F (lift s t) (velocity s t) (0,u) (velocity s t) +
      second F (lift s t) (0,u) (acceleration s t) = 0 := by
  have hd := ((hasDerivAt_second_along hI hs hF ht).clm_apply
    (hasDerivAt_const t ((0 : ℝ),u))).clm_apply (hasDerivAt_velocity hI hs ht)
  have he : (fun z => second F (lift s z) (0,u) (velocity s z)) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    filter_upwards [hI.mem_nhds ht] with z hz
    exact stationary_second_reverse hI hs hF hstat hz u
  have hz := hd.congr_of_eventuallyEq he.symm
  simpa only [ContinuousLinearMap.add_apply, map_zero, add_zero, zero_add] using
    hz.unique (hasDerivAt_const t (0 : ℝ))

omit hstat in
/-- The derivative of the actual value along the branch, before cancellation. -/
theorem value_deriv {t : ℝ} (ht : t ∈ I) :
    deriv (fun z => F (lift s z)) t = fderiv ℝ F (lift s t) (velocity s t) :=
  (((hF t ht).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_lift hI hs ht)).deriv

/-- The second envelope derivative contains no acceleration term. -/
theorem value_second {t : ℝ} (ht : t ∈ I) :
    iteratedDeriv 2 (fun z => F (lift s z)) t =
      second F (lift s t) (velocity s t) (velocity s t) := by
  rw [show (2 : ℕ) = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have he : deriv (fun z => F (lift s z)) =ᶠ[𝓝 t]
      (fun z => fderiv ℝ F (lift s z) (velocity s z)) := by
    filter_upwards [hI.mem_nhds ht] with z hz
    exact value_deriv hI hs hF hz
  rw [he.deriv_eq]
  rw [((hasDerivAt_first_along hI hs hF ht).clm_apply (hasDerivAt_velocity hI hs ht)).deriv]
  rw [show fderiv ℝ F (lift s t) (acceleration s t) = 0 from hstat t ht _]
  exact add_zero _

/-- All mixed acceleration terms in the third derivative vanish. -/
theorem value_third {t : ℝ} (ht : t ∈ I) :
    iteratedDeriv 3 (fun z => F (lift s z)) t =
      third F (lift s t) (velocity s t) (velocity s t) (velocity s t) := by
  rw [show (3 : ℕ) = 2+1 from rfl, iteratedDeriv_succ]
  have he : iteratedDeriv 2 (fun z => F (lift s z)) =ᶠ[𝓝 t]
      (fun z => second F (lift s z) (velocity s z) (velocity s z)) := by
    filter_upwards [hI.mem_nhds ht] with z hz
    exact value_second hI hs hF hstat hz
  rw [he.deriv_eq]
  rw [(((hasDerivAt_second_along hI hs hF ht).clm_apply
    (hasDerivAt_velocity hI hs ht)).clm_apply (hasDerivAt_velocity hI hs ht)).deriv]
  simp only [ContinuousLinearMap.add_apply]
  rw [show second F (lift s t) (acceleration s t) (velocity s t) = 0 from
    stationary_second_reverse hI hs hF hstat ht _,
    show second F (lift s t) (velocity s t) (acceleration s t) = 0 from
      stationary_second hI hs hF hstat ht _]
  simp

/-- Exact fourth stationary-envelope identity, with actual derivatives. -/
theorem value_fourth {t : ℝ} (ht : t ∈ I) :
    iteratedDeriv 4 (fun z => F (lift s z)) t =
      fourth F (lift s t) (velocity s t) (velocity s t) (velocity s t) (velocity s t) -
      3 * second F (lift s t) (acceleration s t) (acceleration s t) := by
  rw [show (4 : ℕ) = 3+1 from rfl, iteratedDeriv_succ]
  have he : iteratedDeriv 3 (fun z => F (lift s z)) =ᶠ[𝓝 t]
      (fun z => third F (lift s z) (velocity s z) (velocity s z) (velocity s z)) := by
    filter_upwards [hI.mem_nhds ht] with z hz
    exact value_third hI hs hF hstat hz
  rw [he.deriv_eq]
  rw [((((hasDerivAt_third_along hI hs hF ht).clm_apply
    (hasDerivAt_velocity hI hs ht)).clm_apply (hasDerivAt_velocity hI hs ht)).clm_apply
      (hasDerivAt_velocity hI hs ht)).deriv]
  simp only [ContinuousLinearMap.add_apply]
  have hsym : third F (lift s t) (acceleration s t) (velocity s t) (velocity s t) =
      third F (lift s t) (velocity s t) (acceleration s t) (velocity s t) := by
    have heq := (((hF t ht).fderiv_right
      (by norm_num : (3 : WithTop ℕ∞) + 1 ≤ 4)).isSymmSndFDerivAt
        (by norm_num)).eq (acceleration s t) (velocity s t)
    exact DFunLike.congr_fun heq (velocity s t)
  have h1 := stationary_third hI hs hF hstat ht (deriv (deriv s) t)
  have h2 := stationary_third_reverse hI hs hF hstat ht (deriv (deriv s) t)
  change third F (lift s t) (velocity s t) (velocity s t) (acceleration s t) +
      second F (lift s t) (acceleration s t) (acceleration s t) = 0 at h1
  change third F (lift s t) (velocity s t) (acceleration s t) (velocity s t) +
      second F (lift s t) (acceleration s t) (acceleration s t) = 0 at h2
  rw [hsym]
  linarith


/-- First derivative bound obtained from actual differentiated stationarity,
not from an assumed response formula. -/
theorem optimizer_first_le {t : ℝ} (ht : t ∈ I) {g B : ℝ} (hg : 0 < g)
    (hB : 0 ≤ B) (h₂ : ‖second F (lift s t)‖ ≤ B)
    (hcoercive : ∀ u : E, g * ‖u‖ ^ 2 ≤ -second F (lift s t) (0,u) (0,u)) :
    ‖deriv s t‖ ≤ B / g := by
  have hz := stationary_second hI hs hF hstat ht (deriv s t)
  have he : velocity s t = ((1 : ℝ),(0 : E)) + ((0 : ℝ),deriv s t) := by simp [velocity]
  rw [he, map_add, ContinuousLinearMap.add_apply] at hz
  have hc := hcoercive (deriv s t)
  have hn := norm_second_apply (second F (lift s t)) ((1 : ℝ),(0 : E)) ((0 : ℝ),deriv s t)
  simp only [Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one, max_eq_right (norm_nonneg _),
    mul_one] at hn
  have hb := mul_le_mul_of_nonneg_right h₂ (norm_nonneg (deriv s t))
  apply cancel_coercive hg (norm_nonneg _) hB
  have hh := (le_abs_self _).trans (hn.trans hb)
  linarith

/-- The actual lifted branch velocity has a completely explicit bound. -/
theorem velocity_le {t : ℝ} (ht : t ∈ I) {g B : ℝ} (hg : 0 < g)
    (hB : 0 ≤ B) (h₂ : ‖second F (lift s t)‖ ≤ B)
    (hcoercive : ∀ u : E, g * ‖u‖ ^ 2 ≤ -second F (lift s t) (0,u) (0,u)) :
    ‖velocity s t‖ ≤ 1 + B / g := by
  have hh := optimizer_first_le hI hs hF hstat ht hg hB h₂ hcoercive
  simp only [velocity, Prod.norm_def, norm_one]
  exact max_le (by have hh := div_nonneg hB hg.le; linarith) (hh.trans (by linarith))

/-- Second optimizer derivative controlled by differentiated stationarity
and the actual third joint derivative. -/
theorem optimizer_second_le {t : ℝ} (ht : t ∈ I) {g B : ℝ} (hg : 0 < g)
    (hB : 0 ≤ B) (h₃ : ‖third F (lift s t)‖ ≤ B)
    (hcoercive : ∀ u : E, g * ‖u‖ ^ 2 ≤ -second F (lift s t) (0,u) (0,u)) :
    ‖deriv (deriv s) t‖ ≤ (B / g) * ‖velocity s t‖ ^ 2 := by
  have hz := stationary_third hI hs hF hstat ht (deriv (deriv s) t)
  have hc := hcoercive (deriv (deriv s) t)
  have hn := norm_third_apply (third F (lift s t)) (velocity s t) (velocity s t)
    ((0 : ℝ),deriv (deriv s) t)
  simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] at hn
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h₃ (norm_nonneg (velocity s t))) (norm_nonneg (velocity s t)))
    (norm_nonneg (deriv (deriv s) t))
  have hh := (le_abs_self _).trans (hn.trans hb)
  have hineq : g * ‖deriv (deriv s) t‖ ^ 2 ≤
      (B * ‖velocity s t‖ ^ 2) * ‖deriv (deriv s) t‖ := by
    change third F (lift s t) (velocity s t) (velocity s t) ((0 : ℝ),deriv (deriv s) t) +
      second F (lift s t) ((0 : ℝ),deriv (deriv s) t) ((0 : ℝ),deriv (deriv s) t) = 0 at hz
    nlinarith
  have hr := cancel_coercive hg (norm_nonneg _) (mul_nonneg hB (sq_nonneg _)) hineq
  calc ‖deriv (deriv s) t‖ ≤ (B * ‖velocity s t‖ ^ 2) / g := hr
    _ = _ := by ring

/-- The Hessian correction is bounded using the differentiated stationarity
identity, avoiding an extra factor of the upper Hessian norm. -/
theorem correction_le {t : ℝ} (ht : t ∈ I) {g B : ℝ} (hg : 0 < g)
    (hB : 0 ≤ B) (h₃ : ‖third F (lift s t)‖ ≤ B)
    (hcoercive : ∀ u : E, g * ‖u‖ ^ 2 ≤ -second F (lift s t) (0,u) (0,u)) :
    |second F (lift s t) (acceleration s t) (acceleration s t)| ≤
      (B ^ 2 / g) * ‖velocity s t‖ ^ 4 := by
  have hz := stationary_third hI hs hF hstat ht (deriv (deriv s) t)
  have he : second F (lift s t) (acceleration s t) (acceleration s t) =
      -third F (lift s t) (velocity s t) (velocity s t) (acceleration s t) := by
    change third F (lift s t) (velocity s t) (velocity s t) (acceleration s t) +
      second F (lift s t) (acceleration s t) (acceleration s t) = 0 at hz
    linarith
  rw [he, abs_neg]
  have hn := norm_third_apply (third F (lift s t)) (velocity s t) (velocity s t) (acceleration s t)
  have ha : ‖acceleration s t‖ = ‖deriv (deriv s) t‖ := by simp [acceleration, Prod.norm_def]
  rw [ha] at hn
  calc |third F (lift s t) (velocity s t) (velocity s t) (acceleration s t)|
      ≤ ‖third F (lift s t)‖ * ‖velocity s t‖ * ‖velocity s t‖ * ‖deriv (deriv s) t‖ := hn
    _ ≤ B * ‖velocity s t‖ * ‖velocity s t‖ * ((B / g) * ‖velocity s t‖ ^ 2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h₃ (norm_nonneg _)) (norm_nonneg _)
      · exact optimizer_second_le hI hs hF hstat ht hg hB h₃ hcoercive
      · exact norm_nonneg _
      · positivity
    _ = _ := by ring

/-- Explicit fourth-derivative envelope cap. All norms are the actual
joint Fréchet derivative norms in the declared normed coordinates. -/
theorem value_fourth_le {t : ℝ} (ht : t ∈ I) {g B : ℝ} (hg : 0 < g)
    (hB : 0 ≤ B) (h₂ : ‖second F (lift s t)‖ ≤ B)
    (h₃ : ‖third F (lift s t)‖ ≤ B) (h₄ : ‖fourth F (lift s t)‖ ≤ B)
    (hcoercive : ∀ u : E, g * ‖u‖ ^ 2 ≤ -second F (lift s t) (0,u) (0,u)) :
    |iteratedDeriv 4 (fun z => F (lift s z)) t| ≤
      (B + 3 * B ^ 2 / g) * (1 + B / g) ^ 4 := by
  rw [value_fourth hI hs hF hstat ht]
  have hn := norm_fourth_apply (fourth F (lift s t)) (velocity s t) (velocity s t)
    (velocity s t) (velocity s t)
  have hb : |fourth F (lift s t) (velocity s t) (velocity s t) (velocity s t) (velocity s t)| ≤
      B * ‖velocity s t‖ ^ 4 := by
    calc _ ≤ ‖fourth F (lift s t)‖ * ‖velocity s t‖ * ‖velocity s t‖ * ‖velocity s t‖ * ‖velocity s t‖ := hn
      _ ≤ B * ‖velocity s t‖ * ‖velocity s t‖ * ‖velocity s t‖ * ‖velocity s t‖ := by
        gcongr
      _ = _ := by ring
  have hc := correction_le hI hs hF hstat ht hg hB h₃ hcoercive
  have hv := velocity_le hI hs hF hstat ht hg hB h₂ hcoercive
  calc _ ≤ |fourth F (lift s t) (velocity s t) (velocity s t) (velocity s t) (velocity s t)| +
        |3 * second F (lift s t) (acceleration s t) (acceleration s t)| := abs_sub _ _
    _ = |fourth F (lift s t) (velocity s t) (velocity s t) (velocity s t) (velocity s t)| +
        3 * |second F (lift s t) (acceleration s t) (acceleration s t)| := by rw [abs_mul]; norm_num
    _ ≤ B * ‖velocity s t‖ ^ 4 + 3 * ((B ^ 2 / g) * ‖velocity s t‖ ^ 4) := by gcongr
    _ = (B + 3 * B ^ 2 / g) * ‖velocity s t‖ ^ 4 := by ring
    _ ≤ _ := by gcongr

end MatrixSpencer.KSEnvelopeFourth
