import SeamlessKS.ExactEVD
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! An explicit orthonormal parametrization of the hyperplane perpendicular
to a coefficient vector. Reflection is used to prove the Householder formula. -/
open scoped BigOperators
noncomputable section
namespace RadialKS.RadialBasis
abbrev Space (m : ℕ) := EuclideanSpace ℝ (Fin m)
variable {m : ℕ}

def pad (v : Space m) : Space (m + 1) := WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))

@[simp] theorem pad_zero (v : Space m) : pad v 0 = 0 := rfl
@[simp] theorem pad_succ (v : Space m) (i : Fin m) : pad v i.succ = v i := rfl

theorem pad_norm (v : Space m) : ‖pad v‖ = ‖v‖ := by
  have h : ‖pad v‖ ^ 2 = ‖v‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, pad_zero, pad_succ,
      norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
  nlinarith [norm_nonneg (pad v), norm_nonneg v]

def padIsometry : Space m →ₗᵢ[ℝ] Space (m + 1) where
  toFun := pad
  map_add' v w := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [pad]
  map_smul' c v := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [pad]
  norm_map' := pad_norm

def sign (q : Space (m + 1)) : ℝ := if 0 ≤ q 0 then 1 else -1

theorem sign_abs (q : Space (m + 1)) : |sign q| = 1 := by
  unfold sign
  split_ifs <;> norm_num

def target (q : Space (m + 1)) : Space (m + 1) := EuclideanSpace.single 0 (-sign q)

theorem target_norm (q : Space (m + 1)) : ‖target q‖ = 1 := by
  simp only [target, EuclideanSpace.norm_single, norm_neg, Real.norm_eq_abs, sign_abs]

def reflection (q : Space (m + 1)) : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1) :=
  (ℝ ∙ (q - target q))ᗮ.reflection

theorem reflection_q (q : Space (m + 1)) (hq : ‖q‖ = 1) :
    reflection q q = target q := Submodule.reflection_sub (hq.trans (target_norm q).symm)

theorem reflection_involutive (q v : Space (m + 1)) :
    reflection q (reflection q v) = v := Submodule.reflection_reflection _ _

def embedding (q : Space (m + 1)) : Space m →ₗᵢ[ℝ] Space (m + 1) :=
  (reflection q).toLinearIsometry.comp padIsometry

theorem embedding_orthogonal (q : Space (m + 1)) (hq : ‖q‖ = 1) (v : Space m) :
    inner ℝ q (embedding q v) = 0 := by
  have h := (reflection q).inner_map_map q (embedding q v)
  rw [reflection_q q hq] at h
  change inner ℝ (target q) (reflection q (reflection q (pad v))) = _ at h
  rw [reflection_involutive, target, EuclideanSpace.inner_single_left, pad_zero] at h
  simpa only [mul_zero] using h.symm

theorem embedding_surjective_orthogonal (q g : Space (m + 1)) (hq : ‖q‖ = 1)
    (hg : inner ℝ q g = 0) : ∃ v : Space m, embedding q v = g := by
  let w := reflection q g
  have hw : w 0 = 0 := by
    have h := (reflection q).inner_map_map q g
    rw [reflection_q q hq, hg, target, EuclideanSpace.inner_single_left] at h
    have hs : -sign q ≠ 0 := neg_ne_zero.mpr (by
      have hh := sign_abs q
      intro hz
      rw [hz, abs_zero] at hh
      norm_num at hh)
    exact (mul_eq_zero.mp (by simpa only [starRingEnd_apply, star_trivial] using h)).resolve_left hs
  let v : Space m := WithLp.toLp 2 (fun i => w i.succ)
  have hp : pad v = w := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hw.symm
    · rfl
  refine ⟨v, ?_⟩
  change reflection q (pad v) = g
  rw [hp]
  exact reflection_involutive q g

theorem reflection_formula (q v : Space (m + 1)) :
    reflection q v = v - (2 * inner ℝ (q - target q) v / ‖q - target q‖ ^ 2) •
      (q - target q) := by
  rw [reflection, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  ext i
  simp only [PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [RCLike.ofReal_real_eq_id, id_eq, two_smul]
  ring

end RadialKS.RadialBasis
