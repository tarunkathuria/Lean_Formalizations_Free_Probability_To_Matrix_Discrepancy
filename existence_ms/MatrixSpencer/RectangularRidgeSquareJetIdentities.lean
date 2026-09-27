import MatrixSpencer.RectangularRidgeRootJetBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Actual differentiated square identities through order four

All jets below are actual iterated derivatives of a real matrix-valued curve.
The identities use smoothness only, never assumptions identifying derivatives.
-/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeSquareJetIdentities
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance ridgeSquareJetCStar : CStarAlgebra (Matrix n n ℂ) := {}

variable {f : ℝ → Matrix n n ℂ} {t : ℝ}

lemma hasDerivAt_jet (hf : ContDiffAt ℝ 4 f t) (r : ℕ) (hr : r < 4) :
    HasDerivAt (iteratedDeriv r f) (iteratedDeriv (r + 1) f t) t := by
  have hh := hf.contDiffWithinAt.differentiableWithinAt_iteratedDerivWithin
    (m := r) (by exact_mod_cast hr) (by simp : UniqueDiffOn ℝ (insert t Set.univ))
  have hd : DifferentiableAt ℝ (iteratedDeriv r f) t := by
    simpa only [iteratedDerivWithin_univ, differentiableWithinAt_univ] using hh
  simpa only [iteratedDeriv_succ] using hd.hasDerivAt

lemma square_first (hf : ContDiffAt ℝ 4 f t) :
    deriv (fun u => f u * f u) t =
      iteratedDeriv 1 f t * f t + f t * iteratedDeriv 1 f t := by
  have h := hasDerivAt_jet hf 0 (by norm_num)
  simpa only [iteratedDeriv_zero] using (h.fun_mul h).deriv

lemma square_second (hf : ContDiffAt ℝ 4 f t) :
    iteratedDeriv 2 (fun u => f u * f u) t =
      iteratedDeriv 2 f t * f t + (2 : ℝ) • (iteratedDeriv 1 f t * iteratedDeriv 1 f t) +
        f t * iteratedDeriv 2 f t := by
  have he : deriv (fun u => f u * f u) =ᶠ[𝓝 t]
      (fun u => iteratedDeriv 1 f u * f u + f u * iteratedDeriv 1 f u) := by
    filter_upwards [hf.eventually (by norm_num)] with u hu
    exact square_first hu
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    he.deriv_eq]
  have h0 := hasDerivAt_jet hf 0 (by norm_num)
  have h1 := hasDerivAt_jet hf 1 (by norm_num)
  simp only [iteratedDeriv_zero] at h0
  rw [((h1.fun_mul h0).fun_add (h0.fun_mul h1)).deriv]
  module

lemma square_third (hf : ContDiffAt ℝ 4 f t) :
    iteratedDeriv 3 (fun u => f u * f u) t =
      iteratedDeriv 3 f t * f t + (3 : ℝ) • (iteratedDeriv 2 f t * iteratedDeriv 1 f t) +
        (3 : ℝ) • (iteratedDeriv 1 f t * iteratedDeriv 2 f t) +
        f t * iteratedDeriv 3 f t := by
  have he : iteratedDeriv 2 (fun u => f u * f u) =ᶠ[𝓝 t]
      (fun u => iteratedDeriv 2 f u * f u +
        (2 : ℝ) • (iteratedDeriv 1 f u * iteratedDeriv 1 f u) +
        f u * iteratedDeriv 2 f u) := by
    filter_upwards [hf.eventually (by norm_num)] with u hu
    exact square_second hu
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, he.deriv_eq]
  have h0 := hasDerivAt_jet hf 0 (by norm_num)
  have h1 := hasDerivAt_jet hf 1 (by norm_num)
  have h2 := hasDerivAt_jet hf 2 (by norm_num)
  simp only [iteratedDeriv_zero] at h0
  rw [(((h2.fun_mul h0).fun_add ((h1.fun_mul h1).fun_const_smul (2 : ℝ))).fun_add (h0.fun_mul h2)).deriv]
  module

lemma square_fourth (hf : ContDiffAt ℝ 4 f t) :
    iteratedDeriv 4 (fun u => f u * f u) t =
      iteratedDeriv 4 f t * f t + (4 : ℝ) • (iteratedDeriv 3 f t * iteratedDeriv 1 f t) +
        (6 : ℝ) • (iteratedDeriv 2 f t * iteratedDeriv 2 f t) +
        (4 : ℝ) • (iteratedDeriv 1 f t * iteratedDeriv 3 f t) +
        f t * iteratedDeriv 4 f t := by
  have he : iteratedDeriv 3 (fun u => f u * f u) =ᶠ[𝓝 t]
      (fun u => iteratedDeriv 3 f u * f u +
        (3 : ℝ) • (iteratedDeriv 2 f u * iteratedDeriv 1 f u) +
        (3 : ℝ) • (iteratedDeriv 1 f u * iteratedDeriv 2 f u) +
        f u * iteratedDeriv 3 f u) := by
    filter_upwards [hf.eventually (by norm_num)] with u hu
    exact square_third hu
  conv_lhs => rw [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_succ]
  rw [he.deriv_eq]
  have h0 := hasDerivAt_jet hf 0 (by norm_num)
  have h1 := hasDerivAt_jet hf 1 (by norm_num)
  have h2 := hasDerivAt_jet hf 2 (by norm_num)
  have h3 := hasDerivAt_jet hf 3 (by norm_num)
  simp only [iteratedDeriv_zero] at h0
  rw [((((h3.fun_mul h0).fun_add ((h2.fun_mul h1).fun_const_smul (3 : ℝ))).fun_add
    ((h1.fun_mul h2).fun_const_smul (3 : ℝ))).fun_add (h0.fun_mul h3)).deriv]
  module

end MatrixSpencer.RectangularRidgeSquareJetIdentities
