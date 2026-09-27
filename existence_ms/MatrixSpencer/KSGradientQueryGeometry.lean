import MatrixSpencer.KSHermitianGradientReport
import MatrixSpencer.KSObjectiveUpper
import MatrixSpencer.KSFirstDifference
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# The actual density queries in the numerical gradient

Unit Frobenius directions and an explicit scalar step keep both queries
above half the density floor and below trace two. The scalar second derivative
is identified with the actual Fréchet Hessian along the sampled affine line.
-/

open Matrix Filter Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology
noncomputable section
namespace MatrixSpencer.KSGradientQueryGeometry

open KSHermitianDirections KSObjectiveUpper
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

theorem realDirection_trace_abs_le (i j : n) : |realTrace (realDirection i j)| ≤ 1 := by
  by_cases hij : i = j
  · subst j
    norm_num [realDirection, realTrace]
  · simp [realDirection, realTrace, hij, Ne.symm hij]

theorem imagDirection_trace_abs_le (i j : n) : |realTrace (imagDirection i j)| ≤ 1 := by
  by_cases hij : i = j
  · subst j
    simp [imagDirection]
  · simp [imagDirection, realTrace, hij, Ne.symm hij]

theorem norm_le_one_of_trace_square {D : Matrix n n ℂ} (hD : D.IsHermitian)
    (henergy : realTrace (D * D) ≤ 1) : ‖D‖ ≤ 1 := by
  nlinarith [norm_sq_le_trace_square hD, norm_nonneg D]

/-- Both signed queries are covered by the same absolute scalar condition. -/
theorem query_floor (S D : selfAdjoint (Matrix n n ℂ)) {a t u : ℝ}
    (hfloor : a • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ))
    (henergy : realTrace ((D : Matrix n n ℂ) * (D : Matrix n n ℂ)) ≤ 1)
    (htu : |u| ≤ t) (hta : t ≤ a / 2) :
    (a / 2) • (1 : Matrix n n ℂ) ≤ ((S + u • D : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) := by
  have hnorm := norm_le_one_of_trace_square D.property henergy
  have hbound : ‖u • (D : Matrix n n ℂ)‖ ≤ |u| := by
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith [abs_nonneg u]
  have hD : IsSelfAdjoint (u • (D : Matrix n n ℂ)) := by
    change (u • (D : Matrix n n ℂ))ᴴ = _
    simp only [Matrix.conjTranspose_smul, star_trivial, show (D : Matrix n n ℂ)ᴴ = D from D.property]
  have hlo : -|u| • (1 : Matrix n n ℂ) ≤ u • (D : Matrix n n ℂ) := by
    apply (smul_le_smul_of_nonneg_right (neg_le_neg hbound) zero_le_one).trans
    simpa only [Algebra.algebraMap_eq_smul_one, neg_smul] using hD.neg_algebraMap_norm_le_self
  have hsum := add_le_add hfloor hlo
  rw [← add_smul] at hsum
  exact (smul_le_smul_of_nonneg_right (by linarith : a / 2 ≤ a + -|u|) zero_le_one).trans hsum

theorem query_trace_le_two (S D : selfAdjoint (Matrix n n ℂ)) {t u : ℝ}
    (htrace : realTrace (S : Matrix n n ℂ) = 1)
    (hDtrace : |realTrace (D : Matrix n n ℂ)| ≤ 1)
    (htu : |u| ≤ t) (htone : t ≤ 1) :
    realTrace ((S + u • D : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) ≤ 2 := by
  change realTrace ((S : Matrix n n ℂ) + u • (D : Matrix n n ℂ)) ≤ 2
  rw [realTrace_add, realTrace_smul, htrace]
  have hb : |u * realTrace (D : Matrix n n ℂ)| ≤ |u| := by
    rw [abs_mul]
    nlinarith [abs_nonneg u]
  linarith [le_abs_self (u * realTrace (D : Matrix n n ℂ))]

section AffineCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem deriv_affine_comp (f : E → ℝ) (x v : E) (u : ℝ)
    (hf : DifferentiableAt ℝ f (x + u • v)) :
    deriv (fun w : ℝ => f (x + w • v)) u = fderiv ℝ f (x + u • v) v := by
  simpa only [Function.comp_def, id_eq, one_smul] using
    (hf.hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_id u).smul_const v |>.const_add x)).deriv

theorem iteratedDeriv_two_affine_comp (f : E → ℝ) (x v : E) (u : ℝ)
    (hf : ContDiffAt ℝ 2 f (x + u • v)) :
    iteratedDeriv 2 (fun w : ℝ => f (x + w • v)) u =
      fderiv ℝ (fderiv ℝ f) (x + u • v) v v := by
  have hg : ContDiffAt ℝ 2 (fun w : ℝ => x + w • v) u := by fun_prop
  have hd : deriv (fun w : ℝ => x + w • v) = fun _ => v := by
    funext w
    simpa only [id_eq, one_smul] using ((hasDerivAt_id w).smul_const v |>.const_add x).deriv
  have hdd : iteratedDeriv 2 (fun w : ℝ => x + w • v) u = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
    simp
  have h := iteratedDeriv_vcomp_two hf hg
  simpa only [Function.comp_def, hd, hdd, iteratedFDeriv_two_apply, map_zero, add_zero] using h

end AffineCalculus
end MatrixSpencer.KSGradientQueryGeometry
