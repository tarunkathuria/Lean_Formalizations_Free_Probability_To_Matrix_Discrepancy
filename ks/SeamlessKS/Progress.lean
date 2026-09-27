import MatrixSpencer.KSCubeEntropy
import MatrixSpencer.KSFiniteCoinRun
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Progress lemmas for local outward and covariance-weighted symmetric moves.
No retirement routine or old KS signing theorem is used here. -/

open Set
open scoped BigOperators
noncomputable section
namespace SeamlessKS.Progress

open MatrixSpencer.KSCubeEntropy

def strengthenedEntropy (x : ℝ) : ℝ := u x + x ^ 2
def strengthenedEntropy' (x : ℝ) : ℝ := u' x + 2 * x

theorem strengthenedEntropy_concave :
    ConcaveOn ℝ (Icc (-1 : ℝ) 1) strengthenedEntropy := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos
    (f' := strengthenedEntropy') (f'' := fun x => -2 / (1 - x ^ 2) + 2)
    (convex_Icc _ _) (continuous_u.add (continuous_id.pow 2)).continuousOn
  · intro x hx
    have hx' : |x| < 1 := abs_lt.mpr (by simpa only [interior_Icc, mem_Ioo] using hx)
    convert ((hasDerivAt_u hx').add ((hasDerivAt_id x).pow 2)).hasDerivWithinAt using 1 <;>
      simp [strengthenedEntropy, strengthenedEntropy', pow_one]
  · intro x hx
    have hx' : |x| < 1 := abs_lt.mpr (by simpa only [interior_Icc, mem_Ioo] using hx)
    convert ((hasDerivAt_u' hx').add ((hasDerivAt_id x).const_mul 2)).hasDerivWithinAt using 1 <;>
      simp [strengthenedEntropy']
  · intro x hx
    have hx' : |x| < 1 := abs_lt.mpr (by simpa only [interior_Icc, mem_Ioo] using hx)
    have hp := one_sub_sq_pos hx'
    have hquot : -2 / (1 - x ^ 2) ≤ -2 := by
      apply (div_le_iff₀ hp).mpr
      nlinarith [sq_nonneg x]
    linarith

@[simp] theorem strengthenedEntropy_neg (x : ℝ) :
    strengthenedEntropy (-x) = strengthenedEntropy x := by
  simp [strengthenedEntropy]

theorem strengthenedEntropy_antitone {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    strengthenedEntropy y ≤ strengthenedEntropy x := by
  by_cases hy0 : y = 0
  · have hx0 : x = 0 := by linarith
    simp [hy0, hx0]
  have hyp : 0 < y := lt_of_le_of_ne (hx.trans hxy) (Ne.symm hy0)
  have hc := strengthenedEntropy_concave.2
    (show y ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
    (show -y ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
    (show 0 ≤ (y+x)/(2*y) by positivity)
    (show 0 ≤ (y-x)/(2*y) from div_nonneg (sub_nonneg.mpr hxy) (by positivity))
    (show (y+x)/(2*y)+(y-x)/(2*y)=1 by field_simp; ring)
  have he : (y+x)/(2*y)*y+(y-x)/(2*y)*(-y)=x := by field_simp; ring
  simp only [smul_eq_mul, strengthenedEntropy_neg] at hc
  rw [he] at hc
  have hw : (y+x)/(2*y)+(y-x)/(2*y)=1 := by field_simp; ring
  rw [← add_mul, hw, one_mul] at hc
  exact hc

theorem outward_entropy_drop_nonneg {x a : ℝ}
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hface : x+a ≤ 1) :
    u (x+a) ≤ u x - a^2 := by
  have hh := strengthenedEntropy_antitone hx (show x ≤ x+a by linarith) hface
  dsimp only [strengthenedEntropy] at hh
  nlinarith [mul_nonneg hx ha]

def outward (x a : ℝ) : ℝ := if 0 ≤ x then x+a else x-a

theorem outward_entropy_drop {x a : ℝ} (ha : 0 ≤ a)
    (hface : |x|+a ≤ 1) : u (outward x a) ≤ u x-a^2 := by
  by_cases hx : 0 ≤ x
  · rw [outward, if_pos hx]
    exact outward_entropy_drop_nonneg hx ha (by simpa [abs_of_nonneg hx] using hface)
  · rw [outward, if_neg hx]
    have hxn : x < 0 := lt_of_not_ge hx
    have hh := outward_entropy_drop_nonneg (neg_nonneg.mpr hxn.le) ha
      (by simpa [abs_of_neg hxn] using hface)
    have he : -x+a = -(x-a) := by ring
    rw [he, u_neg, u_neg] at hh
    exact hh

variable {N : ℕ}

def entropy (x : Fin N → ℝ) : ℝ := ∑ i, u (x i)

theorem entropy_bounds {x : Fin N → ℝ} (hx : ∀ i, |x i| ≤ 1) :
    0 ≤ entropy x ∧ entropy x ≤ (N : ℝ)*(2*Real.log 2) := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => (bounds (hx i)).1)
  · calc
      entropy x ≤ ∑ _i : Fin N, 2*Real.log 2 :=
        Finset.sum_le_sum (fun i _ => (bounds (hx i)).2)
      _ = _ := by simp

def proposal (x d : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    Fin N → ℝ := fun i => x i+t*(Real.sqrt (d i)*v i)

theorem proposal_displacement_le (x d : Fin N → ℝ)
    (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖=1)
    (hd : ∀ i, d i ≤ 2) (t : ℝ) (i : Fin N) :
    |proposal x d v t i-x i| ≤ |t| * Real.sqrt 2 := by
  have hvi : |v i| ≤ 1 := by simpa only [Real.norm_eq_abs, hv] using PiLp.norm_apply_le v i
  have hs : Real.sqrt (d i) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (hd i)
  simp only [proposal, add_sub_cancel_left, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left hvi (Real.sqrt_nonneg _)).trans (by simpa using hs))
    (abs_nonneg t)

theorem proposal_preserves_frozen (x d : Fin N → ℝ)
    (v : EuclideanSpace ℝ (Fin N)) (t : ℝ) (i : Fin N) (hd : d i=0) :
    proposal x d v t i=x i := by simp [proposal, hd]

theorem symmetric_entropy_drop (x d : Fin N → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hd : ∀ i, 1-x i^2 ≤ d i)
    (hdfrozen : ∀ i, |x i|=1 → d i=0)
    (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖=1)
    (hvfrozen : ∀ i, |x i|=1 → v i=0) (t : ℝ)
    (hinside : ∀ i, |x i|<1 → |t*(Real.sqrt (d i)*v i)| < 1-|x i|) :
    (entropy (proposal x d v t)+entropy (proposal x d v (-t)))/2 ≤
      entropy x-t^2 := by
  have hcoord (i : Fin N) :
      (u (proposal x d v t i)+u (proposal x d v (-t) i))/2 ≤
        u (x i)-t^2*(v i)^2 := by
    rcases lt_or_eq_of_le (hx i) with hi|hi
    · let r := t*(Real.sqrt (d i)*v i)
      have hp := symmetric_drop hi (hinside i hi)
      have hpos := one_sub_sq_pos hi
      have hdpos : 0 ≤ d i := hpos.le.trans (hd i)
      have hr : r^2=t^2*d i*(v i)^2 := by
        dsimp only [r]
        rw [mul_pow, mul_pow, Real.sq_sqrt hdpos]
        ring
      have hrat : t^2*(v i)^2 ≤ r^2/(1-x i^2) := by
        apply (le_div_iff₀ hpos).mpr
        rw [hr]
        nlinarith [mul_nonneg (sub_nonneg.mpr (hd i))
          (mul_nonneg (sq_nonneg t) (sq_nonneg (v i)))]
      have hh : (u (x i+r)+u (x i-r))/2 ≤ u (x i)-t^2*(v i)^2 := hp.trans (by linarith)
      simpa only [proposal, neg_mul, ← sub_eq_add_neg, r] using hh
    · simp only [proposal_preserves_frozen x d v t i (hdfrozen i hi),
        proposal_preserves_frozen x d v (-t) i (hdfrozen i hi), hvfrozen i hi,
        zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero]
      linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hcoord i)
  have hn : (∑ i, (v i)^2)=1 := by
    have hh := EuclideanSpace.norm_sq_eq v
    rw [hv] at hh
    simpa only [one_pow, Real.norm_eq_abs, sq_abs] using hh.symm
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hn, mul_one] at hsum
  exact hsum

theorem rounding_entropy_nonincreasing (x y : Fin N → ℝ)
    (hx : ∀ i, |x i|≤1) (hy : ∀ i, y i=x i ∨ y i=1 ∨ y i= -1) :
    entropy y ≤ entropy x := by
  apply Finset.sum_le_sum
  intro i _
  rcases hy i with he|he|he
  · rw [he]
  · rw [he, u_one]; exact (bounds (hx i)).1
  · rw [he, u_neg_one]; exact (bounds (hx i)).1

end SeamlessKS.Progress
