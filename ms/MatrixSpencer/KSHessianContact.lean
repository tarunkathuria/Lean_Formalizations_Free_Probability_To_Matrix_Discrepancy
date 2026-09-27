import MatrixSpencer.KSLocalDescent

/-!
# Derivative comparison at a smooth touching majorant

If `g ≤ f` near a contact point, their difference has a local minimum.
First derivatives coincide and the actual Hessian of `g` is bounded above
by the Hessian of `f`. The second-order comparison uses the previously
proved Taylor-based exclusion of a negative Hessian at a local minimum.
-/

open Filter Set
open scoped Topology ContDiff

namespace MatrixSpencer.KSHessianContact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem isLocalMin_sub_of_touching_majorant (f g : E → ℝ) (x : E)
    (hmajorant : ∀ᶠ y in 𝓝 x, g y ≤ f y) (hcontact : g x = f x) :
    IsLocalMin (fun y => f y - g y) x := by
  filter_upwards [hmajorant] with y hy
  change f x - g x ≤ f y - g y
  rw [hcontact, sub_self]
  exact sub_nonneg.mpr hy

/-- Contact identifies the complete Fréchet derivatives, not only one
directional derivative. -/
theorem fderiv_eq_of_touching_majorant (f g : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hmajorant : ∀ᶠ y in 𝓝 x, g y ≤ f y) (hcontact : g x = f x) :
    fderiv ℝ g x = fderiv ℝ f x := by
  have hmin := isLocalMin_sub_of_touching_majorant f g x hmajorant hcontact
  have hzero := hmin.hasFDerivAt_eq_zero
    ((hf.differentiableAt (by norm_num)).hasFDerivAt.sub
      (hg.differentiableAt (by norm_num)).hasFDerivAt)
  exact (sub_eq_zero.mp hzero).symm

/-- The Hessian of a difference is the difference of the actual Hessians.
The neighborhood identity is justified by the supplied local C² proofs. -/
theorem hessian_sub_apply (f g : E → ℝ) (x v w : E)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => f y - g y)) x v w =
      fderiv ℝ (fderiv ℝ f) x v w - fderiv ℝ (fderiv ℝ g) x v w := by
  have hevent : fderiv ℝ (fun y => f y - g y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y - fderiv ℝ g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hfy hgy
    exact fderiv_fun_sub (hfy.differentiableAt (by norm_num))
      (hgy.differentiableAt (by norm_num))
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [hevent.fderiv_eq, fderiv_fun_sub hdf hdg]
  simp only [ContinuousLinearMap.sub_apply]

/-- A smooth touching upper bound dominates every actual Hessian quadratic
form. No bound on a third or fourth derivative is required. -/
theorem hessian_le_of_touching_majorant (f g : E → ℝ) (x v : E)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hmajorant : ∀ᶠ y in 𝓝 x, g y ≤ f y) (hcontact : g x = f x) :
    fderiv ℝ (fderiv ℝ g) x v v ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  have hmin := isLocalMin_sub_of_touching_majorant f g x hmajorant hcontact
  have hnonneg : 0 ≤ fderiv ℝ (fderiv ℝ (fun y => f y - g y)) x v v := by
    by_contra hn
    exact (ks_not_isLocalMin_of_hessian_neg (fun y => f y - g y) x v
      (hf.sub hg) (lt_of_not_ge hn)) hmin
  rw [hessian_sub_apply f g x v v hf hg] at hnonneg
  exact sub_nonneg.mp hnonneg

theorem hessian_neg_of_touching_majorant (f g : E → ℝ) (x v : E)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hmajorant : ∀ᶠ y in 𝓝 x, g y ≤ f y) (hcontact : g x = f x)
    (hnegative : fderiv ℝ (fderiv ℝ f) x v v < 0) :
    fderiv ℝ (fderiv ℝ g) x v v < 0 :=
  (hessian_le_of_touching_majorant f g x v hf hg hmajorant hcontact).trans_lt hnegative

end MatrixSpencer.KSHessianContact
