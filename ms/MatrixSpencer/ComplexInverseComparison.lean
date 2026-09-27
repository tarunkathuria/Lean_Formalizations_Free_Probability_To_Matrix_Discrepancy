import MatrixSpencer.QuadraticOrder
import Mathlib.Tactic

/-!
# Complex inverse quadratic forms and coupled domination

The pairing is the real part of the complex Euclidean inner product. All
matrix inequalities use Loewner order. No norm convention is implicit.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section

namespace MatrixSpencer
namespace ComplexInverseComparison

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def pairing (x y : ι → ℂ) : ℝ := RCLike.re (star x ⬝ᵥ y)
def quadratic (A : Matrix ι ι ℂ) (x : ι → ℂ) : ℝ := pairing x (A *ᵥ x)

omit [DecidableEq ι] in
lemma pairing_symm (x y : ι → ℂ) : pairing x y = pairing y x := by
  rw [pairing, star_dotProduct]
  simp only [Complex.star_def, RCLike.re_eq_complex_re, Complex.conj_re]
  rfl

omit [DecidableEq ι] in
lemma quadratic_nonneg {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (x : ι → ℂ) :
    0 ≤ quadratic A x := hA.re_dotProduct_nonneg x

omit [DecidableEq ι] in
lemma quadratic_mono {A B : Matrix ι ι ℂ} (hAB : A ≤ B) (x : ι → ℂ) :
    quadratic A x ≤ quadratic B x := by
  have h := quadratic_nonneg (Matrix.le_iff.mp hAB) x
  simpa only [quadratic, pairing, Matrix.sub_mulVec, dotProduct_sub, map_sub, sub_nonneg] using h

omit [DecidableEq ι] in
lemma le_of_quadratic_le {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ x, quadratic A x ≤ quadratic B x) : A ≤ B := matrix_le_of_real_quadratic_le hA hB h

omit [DecidableEq ι] [DecidableEq κ] in
lemma adjoint_pairing (T : Matrix κ ι ℂ) (f : κ → ℂ) (x : ι → ℂ) :
    pairing f (T *ᵥ x) = pairing (Tᴴ *ᵥ f) x := by
  simp only [pairing, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
    Matrix.dotProduct_mulVec]

omit [DecidableEq ι] in
lemma hermitian_pairing {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x y : ι → ℂ) :
    pairing x (A *ᵥ y) = pairing y (A *ᵥ x) := by
  rw [adjoint_pairing, hA.eq, pairing_symm]

omit [DecidableEq ι] in
lemma quadratic_sub {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x y : ι → ℂ) :
    quadratic A (x - y) = quadratic A x - 2 * pairing x (A *ᵥ y) + quadratic A y := by
  have hs := hermitian_pairing hA y x
  simp only [quadratic, pairing, Matrix.mulVec_sub, star_sub, dotProduct_sub, sub_dotProduct, map_sub]
  simp only [pairing] at hs
  rw [hs]
  ring

lemma posDef_mulVec_inv {A : Matrix ι ι ℂ} (hA : A.PosDef) (f : ι → ℂ) :
    A *ᵥ (A⁻¹ *ᵥ f) = f := by
  letI := hA.isUnit.invertible
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-- The complex inverse variational identity follows by completing an actual square. -/
lemma inverse_completing_square {A : Matrix ι ι ℂ} (hA : A.PosDef) (f x : ι → ℂ) :
    2 * pairing f x - quadratic A x =
      quadratic A⁻¹ f - quadratic A (x - A⁻¹ *ᵥ f) := by
  rw [quadratic_sub hA.isHermitian]
  simp only [quadratic, posDef_mulVec_inv hA]
  rw [pairing_symm x f, pairing_symm (A⁻¹ *ᵥ f) f]
  ring

lemma inverse_variational_le {A : Matrix ι ι ℂ} (hA : A.PosDef) (f x : ι → ℂ) :
    2 * pairing f x - quadratic A x ≤ quadratic A⁻¹ f := by
  rw [inverse_completing_square hA]
  exact sub_le_self _ (quadratic_nonneg hA.posSemidef _)

lemma inverse_variational_attained {A : Matrix ι ι ℂ} (hA : A.PosDef) (f : ι → ℂ) :
    2 * pairing f (A⁻¹ *ᵥ f) - quadratic A (A⁻¹ *ᵥ f) = quadratic A⁻¹ f := by
  rw [inverse_completing_square hA]
  simp only [sub_self, quadratic, pairing, Matrix.mulVec_zero, dotProduct_zero, map_zero, sub_zero]

lemma inverse_variational_isGreatest {A : Matrix ι ι ℂ} (hA : A.PosDef) (f : ι → ℂ) :
    IsGreatest (Set.range (fun x => 2 * pairing f x - quadratic A x)) (quadratic A⁻¹ f) := by
  refine ⟨⟨A⁻¹ *ᵥ f, inverse_variational_attained hA f⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact inverse_variational_le hA f x

/-- Positive-definite inversion reverses complex Loewner order. -/
lemma inverse_antitone {A B : Matrix ι ι ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  apply le_of_quadratic_le hB.inv.isHermitian hA.inv.isHermitian
  intro f
  calc
    quadratic B⁻¹ f = 2 * pairing f (B⁻¹ *ᵥ f) - quadratic B (B⁻¹ *ᵥ f) :=
      (inverse_variational_attained hB f).symm
    _ ≤ 2 * pairing f (B⁻¹ *ᵥ f) - quadratic A (B⁻¹ *ᵥ f) :=
      sub_le_sub_left (quadratic_mono hAB _) _
    _ ≤ _ := inverse_variational_le hA _ _

def coupledOperator (T H : Matrix ι ι ℂ) : Matrix ι ι ℂ := (1 - T)ᴴ * (1 - T) + H

lemma coupledOperator_posDef (T : Matrix ι ι ℂ) {H : Matrix ι ι ℂ} (hH : H.PosDef) :
    (coupledOperator T H).PosDef :=
  Matrix.PosDef.posSemidef_add (Matrix.posSemidef_conjTranspose_mul_self (1 - T)) hH

lemma coupledOperator_ge (T H : Matrix ι ι ℂ) : H ≤ coupledOperator T H :=
  le_add_of_nonneg_left (Matrix.posSemidef_conjTranspose_mul_self (1 - T)).nonneg

lemma coupledOperator_inverse_le (T : Matrix ι ι ℂ) {H : Matrix ι ι ℂ} (hH : H.PosDef) :
    (coupledOperator T H)⁻¹ ≤ H⁻¹ :=
  inverse_antitone hH (coupledOperator_posDef T hH) (coupledOperator_ge T H)

lemma coupledOperator_quadratic (T H : Matrix ι ι ℂ) (x : ι → ℂ) :
    quadratic (coupledOperator T H) x =
      pairing ((1 - T) *ᵥ x) ((1 - T) *ᵥ x) + quadratic H x := by
  simp only [quadratic, coupledOperator, pairing, Matrix.add_mulVec, dotProduct_add, map_add]
  rw [← Matrix.mulVec_mulVec]
  change pairing x ((1 - T)ᴴ *ᵥ ((1 - T) *ᵥ x)) + _ = _
  rw [adjoint_pairing, Matrix.conjTranspose_conjTranspose]
  rfl

/-- The stronger factor-one inverse estimate holds for every complex T. -/
lemma coupled_inverse_quadratic_bound (T : Matrix ι ι ℂ) {H : Matrix ι ι ℂ}
    (hH : H.PosDef) (f : ι → ℂ) :
    quadratic (coupledOperator T H)⁻¹ f ≤ pairing f f + quadratic H⁻¹ (Tᴴ *ᵥ f) := by
  let x := (coupledOperator T H)⁻¹ *ᵥ f
  have h₁ := inverse_variational_le (Matrix.PosDef.one (n := ι) (R := ℂ))
    f ((1 - T) *ᵥ x)
  have h₂ := inverse_variational_le hH (Tᴴ *ᵥ f) x
  have hsplit : pairing f x = pairing f ((1 - T) *ᵥ x) + pairing (Tᴴ *ᵥ f) x := by
    rw [← adjoint_pairing]
    simp only [pairing, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, map_sub]
    ring
  have he := inverse_variational_attained (coupledOperator_posDef T hH) f
  change 2 * pairing f x - quadratic (coupledOperator T H) x = _ at he
  rw [coupledOperator_quadratic, hsplit] at he
  simp only [quadratic, inv_one, Matrix.one_mulVec] at h₁
  linarith

omit [DecidableEq ι] [DecidableEq κ] in
lemma quadratic_congruence (P : Matrix κ ι ℂ) (H : Matrix ι ι ℂ) (f : κ → ℂ) :
    quadratic (P * H * Pᴴ) f = quadratic H (Pᴴ *ᵥ f) := by
  simp only [quadratic, ← Matrix.mulVec_mulVec]
  rw [adjoint_pairing]

/-- Complex Loewner domination with the exact adjoint on the coupling. -/
theorem coupled_inverse_domination (T : Matrix ι ι ℂ) {H : Matrix ι ι ℂ}
    (hH : H.PosDef) : (coupledOperator T H)⁻¹ ≤ 1 + T * H⁻¹ * Tᴴ := by
  apply le_of_quadratic_le (coupledOperator_posDef T hH).inv.isHermitian
    (Matrix.isHermitian_one.add (hH.inv.posSemidef.mul_mul_conjTranspose_same T).isHermitian)
  intro f
  have h := coupled_inverse_quadratic_bound T hH f
  have heq : quadratic (1 + T * H⁻¹ * Tᴴ) f = pairing f f + quadratic H⁻¹ (Tᴴ *ᵥ f) := by
    simp only [quadratic, pairing, Matrix.add_mulVec, dotProduct_add, Matrix.one_mulVec, map_add]
    exact congrArg (fun r => pairing f f + r) (quadratic_congruence T H⁻¹ f)
  rwa [heq]

lemma coupled_inverse_quadratic_bound_two (T : Matrix ι ι ℂ) {H : Matrix ι ι ℂ}
    (hH : H.PosDef) (f : ι → ℂ) :
    quadratic (coupledOperator T H)⁻¹ f ≤ 2 * pairing f f + 2 * quadratic H⁻¹ (Tᴴ *ᵥ f) := by
  have h := coupled_inverse_quadratic_bound T hH f
  have h₁ : 0 ≤ pairing f f := by
    simpa only [quadratic, Matrix.one_mulVec] using quadratic_nonneg (Matrix.PosSemidef.one :
      (1 : Matrix ι ι ℂ).PosSemidef) f
  have h₂ := quadratic_nonneg hH.inv.posSemidef (Tᴴ *ᵥ f)
  linarith

end ComplexInverseComparison
end MatrixSpencer
