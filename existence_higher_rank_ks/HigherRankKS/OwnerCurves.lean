import HigherRankKS.SourceProfile
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The coefficient curves used in the actual Hessian calculation. -/

open Set Filter
open scoped Topology ContDiff

noncomputable section
namespace HigherRankKS.OwnerCurves

theorem deriv_affine (f : ℝ → ℝ) (x h t : ℝ) :
    deriv (fun s => f (x + s * h)) t = h * deriv f (x + t * h) := by
  have he : (fun s => f (x + s * h)) = (fun s => (fun z => f (x + z)) (h * s)) := by
    funext s; rw [mul_comm s h]
  rw [he]
  have hb := deriv_comp_mul_left h (fun z => f (x + z)) t
  rw [deriv_comp_const_add] at hb
  simpa only [smul_eq_mul, mul_comm h t] using hb

theorem second_affine (f : ℝ → ℝ) (x h : ℝ) :
    iteratedDeriv 2 (fun t => f (x + t * h)) 0 = h ^ 2 * deriv (deriv f) x := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have he : deriv (fun s => f (x + s * h)) = fun t => h * deriv f (x + t * h) := by
    funext t; exact deriv_affine f x h t
  rw [he, deriv_const_mul_field, deriv_affine]
  simp only [zero_mul, add_zero]
  ring

variable {ι : Type*} [Fintype ι]

def weights (β : ℝ) (x h : ι → ℝ) (t : ℝ) : ι → ℝ :=
  fun i => SourceProfile.owner β (x i + t * h i)

@[simp] theorem weights_zero (β : ℝ) (x h : ι → ℝ) :
    weights β x h 0 = fun i => SourceProfile.owner β (x i) := by
  funext i; simp [weights]

theorem weights_smooth (β : ℝ) (x h : ι → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ ∞ (weights β x h) 0 := by
  apply contDiffAt_pi.mpr
  intro i
  have ho := (SourceProfile.contDiffOn_owner β ∞).contDiffAt (isOpen_Ioo.mem_nhds (hx i))
  have ho' : ContDiffAt ℝ ∞ (SourceProfile.owner β) (x i + (0 : ℝ) * h i) := by
    simpa using ho
  exact ho'.comp 0 (by fun_prop)

theorem weights_deriv (β : ℝ) (x h : ι → ℝ) (i : ι) :
    deriv (fun t => weights β x h t i) 0 = h i * deriv (SourceProfile.owner β) (x i) := by
  simpa only [weights, zero_mul, add_zero] using deriv_affine (SourceProfile.owner β) (x i) (h i) 0

theorem weights_second (β : ℝ) (x h : ι → ℝ) (i : ι) :
    iteratedDeriv 2 (fun t => weights β x h t i) 0 =
      h i ^ 2 * deriv (deriv (SourceProfile.owner β)) (x i) :=
  second_affine _ _ _

end HigherRankKS.OwnerCurves
