import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Quantitative complex derivative bounds on normed balls

Scalar Cauchy estimates on complex affine lines bound the actual operator
norm of a Fréchet derivative. Repeated use on nested balls provides explicit
joint derivative bounds, without choosing coordinate bases or compact maxima.
The holomorphic extension and its value bound remain hypotheses of this
generic analytic lemma; they must be proved for the actual KS objective.
-/

open Set Metric
open scoped ContDiff Topology
noncomputable section
namespace MatrixSpencer.KSCauchyDerivatives

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

local instance : NormedAddCommGroup (E →L[ℂ] F) := inferInstance
local instance : NormedSpace ℂ (E →L[ℂ] F) := inferInstance
local instance : NormedAddCommGroup (E →L[ℂ] E →L[ℂ] F) := inferInstance
local instance : NormedSpace ℂ (E →L[ℂ] E →L[ℂ] F) := inferInstance
local instance : NormedAddCommGroup (E →L[ℂ] E →L[ℂ] E →L[ℂ] F) := inferInstance
local instance : NormedSpace ℂ (E →L[ℂ] E →L[ℂ] E →L[ℂ] F) := inferInstance
local instance : NormedAddCommGroup (E →L[ℂ] E →L[ℂ] E →L[ℂ] E →L[ℂ] F) := inferInstance
local instance : NormedSpace ℂ (E →L[ℂ] E →L[ℂ] E →L[ℂ] E →L[ℂ] F) := inferInstance

theorem norm_fderiv_le_of_ball_bound {f : E → F} {x : E} {r K : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K)
    (hf : DifferentiableOn ℂ f (ball x r))
    (hbound : ∀ y ∈ ball x r, ‖f y‖ ≤ K) :
    ‖fderiv ℂ f x‖ ≤ 2 * K / r := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  let l : ℂ → E := fun z => x + z • v
  have hl : Differentiable ℂ l := (differentiable_const x).add (differentiable_id.smul_const v)
  have hmem : ∀ z ∈ closedBall (0 : ℂ) (r / 2), l z ∈ ball x r := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    rw [mem_ball, dist_eq_norm]
    simp only [l, add_sub_cancel_left, norm_smul, hv, mul_one]
    linarith
  have hdiff : DiffContOnCl ℂ (f ∘ l) (ball 0 (r / 2)) := by
    constructor
    · apply hf.comp hl.differentiableOn
      intro z hz
      exact hmem z (ball_subset_closedBall hz)
    · apply hf.continuousOn.comp hl.continuous.continuousOn
      intro z hz
      exact hmem z (closure_ball_subset_closedBall hz)
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by positivity : 0 < r / 2) hdiff (fun z hz =>
      hbound (l z) (hmem z (sphere_subset_closedBall hz)))
  have hder : HasDerivAt (f ∘ l) (fderiv ℂ f x v) 0 := by
    have hf' := (hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasFDerivAt
    have hl' : HasDerivAt l v 0 := by
      simpa only [one_smul, zero_add] using
        (hasDerivAt_const (0 : ℂ) x).add ((hasDerivAt_id (0 : ℂ)).smul_const v)
    have hf'' : HasFDerivAt f (fderiv ℂ f x) (l 0) := by simpa [l] using hf'
    exact hf''.comp_hasDerivAt 0 hl'
  rw [hder.deriv] at hc
  convert hc using 1 <;> ring

/-- A fixed radial buffer gives the same derivative bound throughout the
smaller ball. This estimate also applies to operator-valued functions. -/
theorem norm_fderiv_le_on_smaller_ball {f : E → F} {x : E} {r s K : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K)
    (hf : DifferentiableOn ℂ f (ball x (s + r)))
    (hbound : ∀ y ∈ ball x (s + r), ‖f y‖ ≤ K) :
    ∀ y ∈ ball x s, ‖fderiv ℂ f y‖ ≤ 2 * K / r := by
  intro y hy
  have hsub : ball y r ⊆ ball x (s + r) := by
    intro z hz
    have hd := dist_triangle z y x
    rw [mem_ball] at hy hz ⊢
    linarith
  exact norm_fderiv_le_of_ball_bound hr hK (hf.mono hsub)
    (fun z hz => hbound z (hsub hz))

abbrev second (f : E → F) := fderiv ℂ (fderiv ℂ f)
abbrev third (f : E → F) := fderiv ℂ (second f)
abbrev fourth (f : E → F) := fderiv ℂ (third f)

/-- Actual derivatives through order four, with conservative Cauchy
constants. The product and operator norms are the declared normed norms. -/
theorem derivatives_le_of_ball_bound {f : E → F} {x : E} {r K : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K)
    (hf : ContDiffOn ℂ ∞ f (ball x (5 * r)))
    (hbound : ∀ y ∈ ball x (5 * r), ‖f y‖ ≤ K) :
    ‖second f x‖ ≤ K * (2 / r) ^ 2 ∧
    ‖third f x‖ ≤ K * (2 / r) ^ 3 ∧
    ‖fourth f x‖ ≤ K * (2 / r) ^ 4 := by
  have hd₀ := hf.differentiableOn (by norm_num)
  have hc₁ : ContDiffOn ℂ ∞ (fderiv ℂ f) (ball x (5 * r)) :=
    hf.fderiv_of_isOpen isOpen_ball (by simp)
  have hc₂ : ContDiffOn ℂ ∞ (second f) (ball x (5 * r)) :=
    hc₁.fderiv_of_isOpen isOpen_ball (by simp)
  have hc₃ : ContDiffOn ℂ ∞ (third f) (ball x (5 * r)) :=
    hc₂.fderiv_of_isOpen isOpen_ball (by simp)
  have hb₁ : ∀ y ∈ ball x (4 * r), ‖fderiv ℂ f y‖ ≤ K * (2 / r) := by
    have h := norm_fderiv_le_on_smaller_ball (f := f) (x := x) (s := 4 * r) hr hK
      (by rw [show 4 * r + r = 5 * r from by ring]; exact hd₀)
      (by rw [show 4 * r + r = 5 * r from by ring]; exact hbound)
    convert h using 3; ring
  have hb₂ : ∀ y ∈ ball x (3 * r), ‖second f y‖ ≤ K * (2 / r) ^ 2 := by
    have h := norm_fderiv_le_on_smaller_ball (s := 3 * r) hr (by positivity : 0 ≤ K * (2 / r))
      ((hc₁.differentiableOn (by norm_num)).mono
        (ball_subset_ball (by linarith : 3 * r + r ≤ 5 * r)))
      (by rw [show 3 * r + r = 4 * r from by ring]; exact hb₁)
    convert h using 3; ring
  have hb₃ : ∀ y ∈ ball x (2 * r), ‖third f y‖ ≤ K * (2 / r) ^ 3 := by
    have h := norm_fderiv_le_on_smaller_ball (s := 2 * r) hr (by positivity : 0 ≤ K * (2 / r) ^ 2)
      ((hc₂.differentiableOn (by norm_num)).mono
        (ball_subset_ball (by linarith : 2 * r + r ≤ 5 * r)))
      (by rw [show 2 * r + r = 3 * r from by ring]; exact hb₂)
    convert h using 3; ring
  have hb₄ : ∀ y ∈ ball x r, ‖fourth f y‖ ≤ K * (2 / r) ^ 4 := by
    have h := norm_fderiv_le_on_smaller_ball (s := r) hr (by positivity : 0 ≤ K * (2 / r) ^ 3)
      ((hc₃.differentiableOn (by norm_num)).mono
        (ball_subset_ball (by linarith : r + r ≤ 5 * r)))
      (by rw [show r + r = 2 * r from by ring]; exact hb₃)
    convert h using 3; ring
  exact ⟨hb₂ x (mem_ball_self (by positivity)),
    hb₃ x (mem_ball_self (by positivity)), hb₄ x (mem_ball_self hr)⟩

/-- One explicit cap for the three derivative orders used by the envelope. -/
theorem derivatives_le_common_cap {f : E → F} {x : E} {R K : ℝ}
    (hR : 0 < R) (hRone : R ≤ 1) (hK : 0 ≤ K)
    (hf : ContDiffOn ℂ ∞ f (ball x R))
    (hbound : ∀ y ∈ ball x R, ‖f y‖ ≤ K) :
    ‖second f x‖ ≤ K * (10 / R) ^ 4 ∧
    ‖third f x‖ ≤ K * (10 / R) ^ 4 ∧
    ‖fourth f x‖ ≤ K * (10 / R) ^ 4 := by
  have hradius : 5 * (R / 5) = R := by ring
  have h := derivatives_le_of_ball_bound (f := f) (x := x) (r := R / 5) (by positivity) hK
    (by rw [hradius]; exact hf) (by rw [hradius]; exact hbound)
  have he : (2 : ℝ) / (R / 5) = 10 / R := by ring
  rw [he] at h
  have ha : 1 ≤ (10 : ℝ) / R := (le_div_iff₀ hR).mpr (by linarith)
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha (by norm_num : 2 ≤ 4)) hK),
    h.2.1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha (by norm_num : 3 ≤ 4)) hK), h.2.2⟩

/-- The curried norms above are exactly the norms of the multilinear
iterated derivatives used by scalar restriction and composition theorems. -/
theorem iterated_derivatives_le_common_cap {f : E → F} {x : E} {R K : ℝ}
    (hR : 0 < R) (hRone : R ≤ 1) (hK : 0 ≤ K)
    (hf : ContDiffOn ℂ ∞ f (ball x R))
    (hbound : ∀ y ∈ ball x R, ‖f y‖ ≤ K) :
    ∀ k : ℕ, 2 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℂ k f x‖ ≤ K * (10 / R) ^ 4 := by
  have h := derivatives_le_common_cap hR hRone hK hf hbound
  intro k hk₂ hk₄
  interval_cases k
  · rw [← norm_iteratedFDeriv_fderiv (n := 1), ← norm_iteratedFDeriv_fderiv (n := 0),
      norm_iteratedFDeriv_zero]
    exact h.1
  · rw [← norm_iteratedFDeriv_fderiv (n := 2), ← norm_iteratedFDeriv_fderiv (n := 1),
      ← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero]
    exact h.2.1
  · rw [← norm_iteratedFDeriv_fderiv (n := 3), ← norm_iteratedFDeriv_fderiv (n := 2),
      ← norm_iteratedFDeriv_fderiv (n := 1), ← norm_iteratedFDeriv_fderiv (n := 0),
      norm_iteratedFDeriv_zero]
    exact h.2.2

end MatrixSpencer.KSCauchyDerivatives
