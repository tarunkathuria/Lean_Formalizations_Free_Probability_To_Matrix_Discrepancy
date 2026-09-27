import MatrixSpencer.KSOptimizerFloor
import Mathlib.Analysis.Complex.Basic

/-!
# The slit-plane domain for products of strictly accretive matrices

Strict accretivity is positivity of the real quadratic form, without any
Hermitian assumption. It passes to the inverse and to invertible congruences.
Products of two such matrices have no spectrum on the nonpositive real axis.
The proof is algebraic: `B - r A⁻¹` remains strictly accretive for `r ≤ 0`.
These are domain facts for an auxiliary analytic extension, not numerical
matrix evaluations used by the walk.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSAccretiveProductDomain

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

/-- Positive real part of every nonzero vector's quadratic form. -/
def StrictAccretive (A : Matrix n n ℂ) : Prop :=
  ∀ v : n → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ (A *ᵥ v)).re

theorem StrictAccretive.isUnit {A : Matrix n n ℂ} (hA : StrictAccretive A) : IsUnit A := by
  by_contra h
  obtain ⟨a, ha, ha2⟩ : ∃ a ≠ 0, A *ᵥ a = 0 := by
    obtain ⟨a, b, hab⟩ := Function.not_injective_iff.mp <| mulVec_injective_iff_isUnit.not.mpr h
    exact ⟨a - b, by simp [sub_eq_zero, hab, mulVec_sub]⟩
  simpa [ha2] using hA a ha

/-- The inverse also has a strictly positive real quadratic form. -/
theorem StrictAccretive.inv {A : Matrix n n ℂ} (hA : StrictAccretive A) :
    StrictAccretive A⁻¹ := by
  intro v hv
  have hunit := hA.isUnit
  have he : A *ᵥ (A⁻¹ *ᵥ v) = v := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ (A.isUnit_iff_isUnit_det.mp hunit), one_mulVec]
  have hw : A⁻¹ *ᵥ v ≠ 0 := by
    intro hz
    rw [hz, mulVec_zero] at he
    exact hv he.symm
  have hp := hA (A⁻¹ *ᵥ v) hw
  rw [he] at hp
  rw [star_dotProduct (v := v), Complex.star_def, Complex.conj_re]
  exact hp

omit [DecidableEq n] in
theorem StrictAccretive.sub_nonpos_smul {A B : Matrix n n ℂ}
    (hA : StrictAccretive A) (hB : StrictAccretive B) {r : ℝ} (hr : r ≤ 0) :
    StrictAccretive (B - (r : ℂ) • A) := by
  intro v hv
  have ha := hA v hv
  have hb := hB v hv
  simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
    Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hr ha.le]

/-- Every nonpositive real scalar is in the resolvent set of the product. -/
theorem product_nonpos_not_mem_spectrum {A B : Matrix n n ℂ}
    (hA : StrictAccretive A) (hB : StrictAccretive B) {r : ℝ} (hr : r ≤ 0) :
    (r : ℂ) ∉ spectrum ℂ (A * B) := by
  have hunit := hA.isUnit.mul (hA.inv.sub_nonpos_smul hB hr).isUnit
  have he : A * (B - (r : ℂ) • A⁻¹) = A * B - (r : ℂ) • (1 : Matrix n n ℂ) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_nonsing_inv _
      (A.isUnit_iff_isUnit_det.mp hA.isUnit)]
  rw [he] at hunit
  apply spectrum.notMem_iff.mpr
  simpa only [Algebra.algebraMap_eq_smul_one, neg_sub] using hunit.neg

/-- The complete complex spectrum lies in the principal square-root slit plane. -/
theorem product_spectrum_subset_slitPlane {A B : Matrix n n ℂ}
    (hA : StrictAccretive A) (hB : StrictAccretive B) :
    spectrum ℂ (A * B) ⊆ Complex.slitPlane := by
  intro z hz
  rw [Complex.mem_slitPlane_iff]
  by_cases hi : z.im = 0
  · left
    by_contra hr
    have hzreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    rw [hzreal] at hz
    exact product_nonpos_not_mem_spectrum hA hB (not_lt.mp hr) hz
  · exact Or.inr hi

/-- Congruence by any invertible matrix preserves strict accretivity. -/
theorem StrictAccretive.conjTranspose_mul_mul {A C : Matrix n n ℂ}
    (hA : StrictAccretive A) (hC : IsUnit C) : StrictAccretive (Cᴴ * A * C) := by
  intro v hv
  have hc : C *ᵥ v ≠ 0 := by
    intro hz
    exact hv ((mulVec_injective_iff_isUnit.mpr hC) (hz.trans (mulVec_zero _).symm))
  simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using hA (C *ᵥ v) hc

/-- The operator norm controls the absolute real quadratic form. -/
theorem abs_quadratic_le (A : Matrix n n ℂ) (v : n → ℂ) :
    |(star v ⬝ᵥ (A *ᵥ v)).re| ≤ ‖A‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 := by
  let w : EuclideanSpace ℂ n := WithLp.toLp 2 v
  have hi := (Complex.abs_re_le_norm (inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) A w))).trans
    (norm_inner_le_norm w (Matrix.toEuclideanCLM (𝕜 := ℂ) A w))
  have hop := (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm w
  have he : inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) A w) = star v ⬝ᵥ (A *ᵥ v) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  rw [he] at hi
  have hh := hi.trans (mul_le_mul_of_nonneg_left hop (norm_nonneg w))
  simpa only [← Matrix.cstar_norm_def, pow_two, mul_left_comm] using hh

/-- A norm-small, possibly non-Hermitian perturbation of the identity is accretive. -/
theorem one_add_strictAccretive {U : Matrix n n ℂ} (hU : ‖U‖ < 1) :
    StrictAccretive (1 + U) := by
  intro v hv
  let w : EuclideanSpace ℂ n := WithLp.toLp 2 v
  have hw : w ≠ 0 := by
    intro hw
    apply hv
    exact congrArg WithLp.ofLp hw
  have hn : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
  have hs : (star v ⬝ᵥ v).re = ‖w‖ ^ 2 := by
    have he : inner ℂ w w = star v ⬝ᵥ v := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rfl
    rw [← he]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) w
  have he := (abs_le.mp (abs_quadratic_le U v)).1
  simp only [add_mulVec, one_mulVec, dotProduct_add, Complex.add_re]
  rw [hs]
  have hlt : ‖U‖ * ‖w‖ ^ 2 < ‖w‖ ^ 2 := by nlinarith
  linarith

/-- The positive reference square root transports the norm ball into the accretive cone. -/
theorem sqrt_sandwich_strictAccretive {A₀ U : Matrix n n ℂ}
    (hA₀ : A₀.PosDef) (hU : ‖U‖ < 1) :
    StrictAccretive (CFC.sqrt A₀ * (1 + U) * CFC.sqrt A₀) := by
  have h := (one_add_strictAccretive hU).conjTranspose_mul_mul hA₀.posDef_sqrt.isUnit
  simpa only [hA₀.posDef_sqrt.isHermitian.eq] using h


theorem sqrt_sandwich_product_spectrum_subset_slitPlane {A₀ B₀ U V : Matrix n n ℂ}
    (hA₀ : A₀.PosDef) (hB₀ : B₀.PosDef) (hU : ‖U‖ < 1) (hV : ‖V‖ < 1) :
    spectrum ℂ ((CFC.sqrt A₀ * (1 + U) * CFC.sqrt A₀) *
      (CFC.sqrt B₀ * (1 + V) * CFC.sqrt B₀)) ⊆ Complex.slitPlane :=
  product_spectrum_subset_slitPlane (sqrt_sandwich_strictAccretive hA₀ hU)
    (sqrt_sandwich_strictAccretive hB₀ hV)

end MatrixSpencer.KSAccretiveProductDomain
