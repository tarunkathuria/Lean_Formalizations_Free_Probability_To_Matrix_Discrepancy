import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Deriv

/-!
# Scalar entropy and symmetric progress on the unit cube

The logarithms are real and evaluated at positive arguments for derivatives.
The entropy itself is continuous at both endpoints using `0 * log 0 = 0`.
-/

open Set
noncomputable section
namespace MatrixSpencer.KSCubeEntropy

def u (x : ℝ) : ℝ :=
  2 * Real.log 2 - (1 + x) * Real.log (1 + x) - (1 - x) * Real.log (1 - x)

def u' (x : ℝ) : ℝ := Real.log (1 - x) - Real.log (1 + x)

theorem continuous_u : Continuous u := by
  exact (continuous_const.sub (Real.continuous_mul_log.comp
    (continuous_const.add continuous_id))).sub
    (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))

theorem one_sub_sq_pos {x : ℝ} (hx : |x| < 1) : 0 < 1 - x ^ 2 := by
  nlinarith [sq_abs x, abs_nonneg x]

theorem hasDerivAt_u {x : ℝ} (hx : |x| < 1) : HasDerivAt u (u' x) x := by
  have hp : 0 < 1 + x := by linarith [(abs_lt.mp hx).1]
  have hm : 0 < 1 - x := by linarith [(abs_lt.mp hx).2]
  have hd := ((hasDerivAt_const x (2 * Real.log 2)).sub
    ((Real.hasDerivAt_mul_log hp.ne').comp x ((hasDerivAt_const x 1).add (hasDerivAt_id x)))).sub
    ((Real.hasDerivAt_mul_log hm.ne').comp x ((hasDerivAt_const x 1).sub (hasDerivAt_id x)))
  convert hd using 1
  dsimp only [u']
  ring

theorem hasDerivAt_u' {x : ℝ} (hx : |x| < 1) :
    HasDerivAt u' (-2 / (1 - x ^ 2)) x := by
  have hp : 0 < 1 + x := by linarith [(abs_lt.mp hx).1]
  have hm : 0 < 1 - x := by linarith [(abs_lt.mp hx).2]
  have hd := (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).log hm.ne').sub
    (((hasDerivAt_const x 1).add (hasDerivAt_id x)).log hp.ne')
  convert hd using 1
  simp only [Pi.sub_apply, Pi.add_apply, id_eq, zero_sub, zero_add]
  change -2 / (1 - x ^ 2) = -1 / (1 - x) - 1 / (1 + x)
  field_simp [hp.ne', hm.ne', (one_sub_sq_pos hx).ne']
  ring

@[simp] theorem u_neg (x : ℝ) : u (-x) = u x := by unfold u; simp only [← sub_eq_add_neg, sub_neg_eq_add]; ring
@[simp] theorem u_zero : u 0 = 2 * Real.log 2 := by simp [u]
@[simp] theorem u_one : u 1 = 0 := by norm_num [u]
@[simp] theorem u_neg_one : u (-1) = 0 := by rw [u_neg, u_one]

theorem concaveOn_u : ConcaveOn ℝ (Icc (-1 : ℝ) 1) u := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := u')
    (f'' := fun x => -2 / (1 - x ^ 2)) (convex_Icc _ _) continuous_u.continuousOn
  · intro x hx
    have hx' : |x| < 1 := abs_lt.mpr (by simpa only [interior_Icc, mem_Ioo] using hx)
    exact (hasDerivAt_u hx').hasDerivWithinAt
  · intro x hx
    have hx' : |x| < 1 := abs_lt.mpr (by simpa only [interior_Icc, mem_Ioo] using hx)
    exact (hasDerivAt_u' hx').hasDerivWithinAt
  · intro x hx
    have hx' : |x| < 1 := abs_lt.mpr (by simpa only [interior_Icc, mem_Ioo] using hx)
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (one_sub_sq_pos hx').le

theorem bounds {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ u x ∧ u x ≤ 2 * Real.log 2 := by
  have hxi := abs_le.mp hx
  have hlow := concaveOn_u.2 (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num)
    (show 0 ≤ (1 - x) / 2 by linarith) (show 0 ≤ (1 + x) / 2 by linarith)
    (show (1 - x) / 2 + (1 + x) / 2 = 1 by ring)
  have hhigh := concaveOn_u.2 hxi
    (show -x ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have he1 : (1 - x) / 2 * (-1 : ℝ) + (1 + x) / 2 * (1 : ℝ) = x := by ring
  have he0 : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * (-x) = 0 := by ring
  simp only [smul_eq_mul] at hlow hhigh
  rw [he1, u_neg_one, u_one] at hlow
  simp only [mul_zero, zero_add] at hlow
  rw [he0, u_zero, u_neg] at hhigh
  exact ⟨hlow, by linarith⟩

theorem shifted_interior {x r : ℝ} (_hx : |x| < 1) (hr : |r| < 1 - |x|) :
    |x + r| < 1 ∧ |x - r| < 1 := by
  constructor
  · exact (abs_add_le x r).trans_lt (by linarith)
  · exact (abs_sub x r).trans_lt (by linarith)

/-- Convexity of the reciprocal curvature under the symmetric pair, proved
by a rational inequality with all denominators strictly positive. -/
theorem reciprocal_pair_lower {x r : ℝ} (hx : |x| < 1) (hr : |r| < 1 - |x|) :
    2 / (1 - x ^ 2) ≤ 1 / (1 - (x + r) ^ 2) + 1 / (1 - (x - r) ^ 2) := by
  let A := 1 - (x + r) ^ 2
  let B := 1 - (x - r) ^ 2
  let a := 1 - x ^ 2
  have ha : 0 < a := one_sub_sq_pos hx
  have hA : 0 < A := one_sub_sq_pos (shifted_interior hx hr).1
  have hB : 0 < B := one_sub_sq_pos (shifted_interior hx hr).2
  have hsum : A + B ≤ 2 * a := by dsimp [A, B, a]; nlinarith [sq_nonneg r]
  have hprod : 2 * (A * B) ≤ a * (A + B) := by
    nlinarith [sq_nonneg (A - B), mul_nonneg (sub_nonneg.mpr hsum) (add_pos hA hB).le]
  change 2 / a ≤ 1 / A + 1 / B
  have he : 1 / A + 1 / B = (A + B) / (A * B) := by field_simp; ring
  rw [he]
  exact (div_le_div_iff₀ ha (mul_pos hA hB)).mpr (by nlinarith)

def symmetricRemainder (x r : ℝ) : ℝ := u (x + r) + u (x - r) + 2 * r ^ 2 / (1 - x ^ 2)

def symmetricRemainder' (x r : ℝ) : ℝ := u' (x + r) - u' (x - r) + 4 * r / (1 - x ^ 2)

def symmetricRemainder'' (x r : ℝ) : ℝ :=
  -2 / (1 - (x + r) ^ 2) - 2 / (1 - (x - r) ^ 2) + 4 / (1 - x ^ 2)

theorem hasDerivAt_symmetricRemainder {x r : ℝ} (hx : |x| < 1) (hr : |r| < 1 - |x|) :
    HasDerivAt (symmetricRemainder x) (symmetricRemainder' x r) r := by
  have hi := shifted_interior hx hr
  have hd := (((hasDerivAt_u hi.1).comp r ((hasDerivAt_const r x).add (hasDerivAt_id r))).add
    ((hasDerivAt_u hi.2).comp r ((hasDerivAt_const r x).sub (hasDerivAt_id r)))).add
      ((((hasDerivAt_id r).pow 2).const_mul 2).div_const (1 - x ^ 2))
  convert hd using 1
  dsimp only [symmetricRemainder']
  simp only [id_eq]
  ring

theorem hasDerivAt_symmetricRemainder' {x r : ℝ} (hx : |x| < 1) (hr : |r| < 1 - |x|) :
    HasDerivAt (symmetricRemainder' x) (symmetricRemainder'' x r) r := by
  have hi := shifted_interior hx hr
  have hd := (((hasDerivAt_u' hi.1).comp r ((hasDerivAt_const r x).add (hasDerivAt_id r))).sub
    ((hasDerivAt_u' hi.2).comp r ((hasDerivAt_const r x).sub (hasDerivAt_id r)))).add
      (((hasDerivAt_id r).const_mul 4).div_const (1 - x ^ 2))
  convert hd using 1
  dsimp only [symmetricRemainder'']
  ring

theorem symmetric_drop {x r : ℝ} (hx : |x| < 1) (hr : |r| < 1 - |x|) :
    (u (x + r) + u (x - r)) / 2 ≤ u x - r ^ 2 / (1 - x ^ 2) := by
  let D := Ioo (-(1 - |x|)) (1 - |x|)
  have hconc : ConcaveOn ℝ D (symmetricRemainder x) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := symmetricRemainder' x)
      (f'' := symmetricRemainder'' x) (convex_Ioo _ _)
    · exact (((continuous_u.comp (continuous_const.add continuous_id)).add
        (continuous_u.comp (continuous_const.sub continuous_id))).add
          ((continuous_const.mul (continuous_id.pow 2)).div_const _)).continuousOn
    · intro t ht
      have ht' : t ∈ D := interior_subset ht
      exact (hasDerivAt_symmetricRemainder hx (abs_lt.mpr ht')).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ D := interior_subset ht
      exact (hasDerivAt_symmetricRemainder' hx (abs_lt.mpr ht')).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ D := interior_subset ht
      have hh := reciprocal_pair_lower hx (abs_lt.mpr ht')
      dsimp only [symmetricRemainder'']
      simp only [div_eq_mul_inv] at hh ⊢
      linarith
  have hm := hconc.2 (abs_lt.mp hr)
    (show -r ∈ D from abs_lt.mp (by simpa only [abs_neg] using hr))
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hz : (1 / 2 : ℝ) • r + (1 / 2 : ℝ) • (-r) = 0 := by simp only [smul_eq_mul]; ring
  rw [hz] at hm
  dsimp only [symmetricRemainder] at hm
  simp only [← sub_eq_add_neg, sub_neg_eq_add, neg_sq, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_div, smul_eq_mul] at hm
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith

end MatrixSpencer.KSCubeEntropy
