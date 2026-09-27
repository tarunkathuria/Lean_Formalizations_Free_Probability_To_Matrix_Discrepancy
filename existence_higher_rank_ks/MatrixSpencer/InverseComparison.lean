import MatrixSpencer.SupportShaving

/-!
# Inverse quadratic forms and domination by completing squares

All matrices are real and their order is Loewner order. Quadratic forms use
coordinate dot products, which are the Euclidean inner product. No norm or
variational principle is assumed.
-/

open scoped BigOperators MatrixOrder
open Matrix

namespace MatrixSpencer
namespace InverseComparison

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def quadratic (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := x ⬝ᵥ (A *ᵥ x)

omit [DecidableEq ι] in
theorem quadratic_nonneg {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (x : ι → ℝ) :
    0 ≤ quadratic A x := by
  simpa only [quadratic, star_trivial] using hA.2 x

omit [DecidableEq ι] in
theorem quadratic_mono {A B : Matrix ι ι ℝ} (hAB : A ≤ B) (x : ι → ℝ) :
    quadratic A x ≤ quadratic B x := by
  have h := quadratic_nonneg (Matrix.le_iff.mp hAB) x
  simpa only [quadratic, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] using h

omit [DecidableEq ι] in
theorem le_of_quadratic_le {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ x, quadratic A x ≤ quadratic B x) : A ≤ B := by
  apply Matrix.le_iff.mpr
  refine ⟨hB.sub hA, fun x => ?_⟩
  simpa only [quadratic, star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] using h x

omit [DecidableEq ι] [DecidableEq κ] in
theorem transpose_pairing (T : Matrix κ ι ℝ) (f : κ → ℝ) (x : ι → ℝ) :
    f ⬝ᵥ (T *ᵥ x) = (Tᵀ *ᵥ f) ⬝ᵥ x := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

omit [DecidableEq ι] in
theorem symmetric_pairing {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (x y : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  have ht : Aᵀ = A := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  rw [transpose_pairing, ht, dotProduct_comm]

omit [DecidableEq ι] in
theorem quadratic_sub {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (x y : ι → ℝ) :
    quadratic A (x - y) = quadratic A x - 2 * (x ⬝ᵥ (A *ᵥ y)) + quadratic A y := by
  simp only [quadratic, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [symmetric_pairing hA y x]
  ring

theorem posDef_mulVec_inv {A : Matrix ι ι ℝ} (hA : A.PosDef) (f : ι → ℝ) :
    A *ᵥ (A⁻¹ *ᵥ f) = f := by
  letI := hA.isUnit.invertible
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-- The exact square-completion identity for the positive inverse. -/
theorem inverse_completing_square {A : Matrix ι ι ℝ} (hA : A.PosDef) (f x : ι → ℝ) :
    2 * (f ⬝ᵥ x) - quadratic A x =
      quadratic A⁻¹ f - quadratic A (x - A⁻¹ *ᵥ f) := by
  rw [quadratic_sub hA.isHermitian]
  simp only [quadratic, posDef_mulVec_inv hA]
  rw [dotProduct_comm x f, dotProduct_comm (A⁻¹ *ᵥ f) f]
  ring

theorem inverse_variational_le {A : Matrix ι ι ℝ} (hA : A.PosDef) (f x : ι → ℝ) :
    2 * (f ⬝ᵥ x) - quadratic A x ≤ quadratic A⁻¹ f := by
  rw [inverse_completing_square hA]
  exact sub_le_self _ (quadratic_nonneg hA.posSemidef _)

theorem inverse_variational_attained {A : Matrix ι ι ℝ} (hA : A.PosDef) (f : ι → ℝ) :
    2 * (f ⬝ᵥ (A⁻¹ *ᵥ f)) - quadratic A (A⁻¹ *ᵥ f) = quadratic A⁻¹ f := by
  rw [inverse_completing_square hA]
  simp only [sub_self, quadratic, Matrix.mulVec_zero, dotProduct_zero, sub_zero]

/-- The inverse quadratic form is an attained maximum, proved directly by completing squares. -/
theorem inverse_variational_isGreatest {A : Matrix ι ι ℝ} (hA : A.PosDef) (f : ι → ℝ) :
    IsGreatest (Set.range (fun x => 2 * (f ⬝ᵥ x) - quadratic A x)) (quadratic A⁻¹ f) := by
  refine ⟨⟨A⁻¹ *ᵥ f, inverse_variational_attained hA f⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact inverse_variational_le hA f x

/-- Inversion reverses positive-definite Loewner order. -/
theorem inverse_antitone {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  apply le_of_quadratic_le hB.inv.isHermitian hA.inv.isHermitian
  intro f
  calc
    quadratic B⁻¹ f = 2 * (f ⬝ᵥ (B⁻¹ *ᵥ f)) - quadratic B (B⁻¹ *ᵥ f) :=
      (inverse_variational_attained hB f).symm
    _ ≤ 2 * (f ⬝ᵥ (B⁻¹ *ᵥ f)) - quadratic A (B⁻¹ *ᵥ f) :=
      sub_le_sub_left (quadratic_mono hAB _) _
    _ ≤ quadratic A⁻¹ f := inverse_variational_le hA _ _

def coupledOperator (T H : Matrix ι ι ℝ) : Matrix ι ι ℝ := (1 - T)ᵀ * (1 - T) + H

theorem coupledOperator_posDef (T : Matrix ι ι ℝ) {H : Matrix ι ι ℝ} (hH : H.PosDef) :
    (coupledOperator T H).PosDef := by
  have hp := Matrix.posSemidef_conjTranspose_mul_self (1 - T)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hp
  exact Matrix.PosDef.posSemidef_add hp hH

theorem coupledOperator_ge (T : Matrix ι ι ℝ) (H : Matrix ι ι ℝ) :
    H ≤ coupledOperator T H := by
  have hp := Matrix.posSemidef_conjTranspose_mul_self (1 - T)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hp
  exact le_add_of_nonneg_left hp.nonneg

theorem coupledOperator_inverse_le (T : Matrix ι ι ℝ) {H : Matrix ι ι ℝ} (hH : H.PosDef) :
    (coupledOperator T H)⁻¹ ≤ H⁻¹ :=
  inverse_antitone hH (coupledOperator_posDef T hH) (coupledOperator_ge T H)

theorem coupledOperator_quadratic (T H : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadratic (coupledOperator T H) x =
      ((1 - T) *ᵥ x) ⬝ᵥ ((1 - T) *ᵥ x) + quadratic H x := by
  simp only [quadratic, coupledOperator, Matrix.add_mulVec, dotProduct_add]
  rw [← Matrix.mulVec_mulVec, transpose_pairing, Matrix.transpose_transpose]

/-- No contraction hypothesis on `T` is needed; the stronger constant-one bound holds. -/
theorem coupled_inverse_quadratic_bound (T : Matrix ι ι ℝ) {H : Matrix ι ι ℝ}
    (hH : H.PosDef) (f : ι → ℝ) :
    quadratic (coupledOperator T H)⁻¹ f ≤
      f ⬝ᵥ f + quadratic H⁻¹ (Tᵀ *ᵥ f) := by
  let x := (coupledOperator T H)⁻¹ *ᵥ f
  have h₁ := inverse_variational_le (Matrix.PosDef.one (n := ι) (R := ℝ))
    f ((1 - T) *ᵥ x)
  have h₂ := inverse_variational_le hH (Tᵀ *ᵥ f) x
  have hsplit : f ⬝ᵥ x = f ⬝ᵥ ((1 - T) *ᵥ x) + (Tᵀ *ᵥ f) ⬝ᵥ x := by
    rw [← transpose_pairing, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
    ring
  have he := inverse_variational_attained (coupledOperator_posDef T hH) f
  change 2 * (f ⬝ᵥ x) - quadratic (coupledOperator T H) x = _ at he
  rw [coupledOperator_quadratic, hsplit] at he
  simp only [quadratic, inv_one, Matrix.one_mulVec] at h₁
  linarith

omit [DecidableEq ι] [DecidableEq κ] in
theorem quadratic_congruence (P : Matrix κ ι ℝ) (H : Matrix ι ι ℝ) (f : κ → ℝ) :
    quadratic (P * H * Pᵀ) f = quadratic H (Pᵀ *ᵥ f) := by
  simp only [quadratic, ← Matrix.mulVec_mulVec]
  rw [transpose_pairing]

omit [DecidableEq ι] [DecidableEq κ] in
theorem real_congruence_posSemidef (P : Matrix κ ι ℝ) {H : Matrix ι ι ℝ}
    (hH : H.PosSemidef) : (P * H * Pᵀ).PosSemidef := by
  have h := hH.mul_mul_conjTranspose_same P
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The exact operator domination retaining all coupling, with constant one. -/
theorem coupled_inverse_domination (T : Matrix ι ι ℝ) {H : Matrix ι ι ℝ}
    (hH : H.PosDef) : (coupledOperator T H)⁻¹ ≤ 1 + T * H⁻¹ * Tᵀ := by
  apply le_of_quadratic_le (coupledOperator_posDef T hH).inv.isHermitian
    (Matrix.isHermitian_one.add (real_congruence_posSemidef T hH.inv.posSemidef).isHermitian)
  intro f
  have h := coupled_inverse_quadratic_bound T hH f
  have heq : quadratic (1 + T * H⁻¹ * Tᵀ) f =
      f ⬝ᵥ f + quadratic H⁻¹ (Tᵀ *ᵥ f) := by
    rw [quadratic, Matrix.add_mulVec, dotProduct_add, Matrix.one_mulVec]
    exact congrArg (fun r => f ⬝ᵥ f + r) (quadratic_congruence T H⁻¹ f)
  rwa [heq]

theorem coupled_inverse_quadratic_bound_two (T : Matrix ι ι ℝ) {H : Matrix ι ι ℝ}
    (hH : H.PosDef) (f : ι → ℝ) :
    quadratic (coupledOperator T H)⁻¹ f ≤
      2 * (f ⬝ᵥ f) + 2 * quadratic H⁻¹ (Tᵀ *ᵥ f) := by
  have h := coupled_inverse_quadratic_bound T hH f
  have h₁ : 0 ≤ f ⬝ᵥ f := Finset.sum_nonneg (fun i _ => mul_self_nonneg (f i))
  have h₂ := quadratic_nonneg hH.inv.posSemidef (Tᵀ *ᵥ f)
  linarith

omit [DecidableEq ι] [DecidableEq κ] in
/-- Surjectivity of the compression implies injectivity of its transpose. -/
theorem transpose_injective_of_surjective (P : Matrix κ ι ℝ)
    (hP : Function.Surjective P.mulVec) : Function.Injective Pᵀ.mulVec := by
  intro y z hyz
  have hz : Pᵀ *ᵥ (y - z) = 0 := by rw [Matrix.mulVec_sub, hyz, sub_self]
  obtain ⟨x, hx⟩ := hP (y - z)
  apply sub_eq_zero.mp
  apply dotProduct_self_eq_zero.mp
  calc
    (y - z) ⬝ᵥ (y - z) = (y - z) ⬝ᵥ (P *ᵥ x) := by rw [hx]
    _ = (Pᵀ *ᵥ (y - z)) ⬝ᵥ x := transpose_pairing _ _ _
    _ = 0 := by rw [hz, zero_dotProduct]

noncomputable def compressedInverse (A : Matrix ι ι ℝ) (P : Matrix κ ι ℝ) : Matrix κ κ ℝ :=
  P * A⁻¹ * Pᵀ

omit [DecidableEq κ] in
theorem compressedInverse_posDef {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (P : Matrix κ ι ℝ) (hP : Function.Surjective P.mulVec) :
    (compressedInverse A P).PosDef := by
  have hi : Function.Injective P.vecMul := by
    intro y z hyz
    apply transpose_injective_of_surjective P hP
    simpa only [Matrix.mulVec_transpose] using hyz
  have h := hA.inv.mul_mul_conjTranspose_same hi
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- Explicit minimizer for a prescribed compressed vector. -/
noncomputable def compressionMinimizer (A : Matrix ι ι ℝ) (P : Matrix κ ι ℝ)
    (y : κ → ℝ) : ι → ℝ := A⁻¹ *ᵥ (Pᵀ *ᵥ ((compressedInverse A P)⁻¹ *ᵥ y))

theorem compressionMinimizer_constraint {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (P : Matrix κ ι ℝ) (hP : Function.Surjective P.mulVec) (y : κ → ℝ) :
    P *ᵥ compressionMinimizer A P y = y := by
  unfold compressionMinimizer
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact posDef_mulVec_inv (compressedInverse_posDef hA P hP) y

theorem compressionMinimizer_normal {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (P : Matrix κ ι ℝ) (y : κ → ℝ) :
    A *ᵥ compressionMinimizer A P y = Pᵀ *ᵥ ((compressedInverse A P)⁻¹ *ᵥ y) :=
  posDef_mulVec_inv hA _

theorem compressionMinimizer_energy {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (P : Matrix κ ι ℝ) (hP : Function.Surjective P.mulVec) (y : κ → ℝ) :
    quadratic A (compressionMinimizer A P y) = quadratic (compressedInverse A P)⁻¹ y := by
  rw [quadratic, compressionMinimizer_normal hA, transpose_pairing,
    Matrix.transpose_transpose, compressionMinimizer_constraint hA P hP]
  rfl

/-- Constrained square completion accounts for every full-space direction. -/
theorem compression_completing_square {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (P : Matrix κ ι ℝ) (hP : Function.Surjective P.mulVec) (y : κ → ℝ)
    {x : ι → ℝ} (hx : P *ᵥ x = y) :
    quadratic A x = quadratic (compressedInverse A P)⁻¹ y +
      quadratic A (x - compressionMinimizer A P y) := by
  rw [quadratic_sub hA.isHermitian, compressionMinimizer_normal hA,
    transpose_pairing, Matrix.transpose_transpose, hx, compressionMinimizer_energy hA P hP]
  unfold quadratic
  ring

theorem compression_energy_lower {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (P : Matrix κ ι ℝ) (hP : Function.Surjective P.mulVec) (x : ι → ℝ) :
    quadratic (compressedInverse A P)⁻¹ (P *ᵥ x) ≤ quadratic A x := by
  rw [compression_completing_square hA P hP (P *ᵥ x) rfl]
  exact le_add_of_nonneg_right (quadratic_nonneg hA.posSemidef _)

/-- The constrained minimum is both a lower bound and explicitly attained. -/
theorem compression_minimum_isLeast {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (P : Matrix κ ι ℝ) (hP : Function.Surjective P.mulVec) (y : κ → ℝ) :
    IsLeast {e : ℝ | ∃ x : ι → ℝ, P *ᵥ x = y ∧ quadratic A x = e}
      (quadratic (compressedInverse A P)⁻¹ y) := by
  refine ⟨⟨compressionMinimizer A P y, compressionMinimizer_constraint hA P hP y,
    compressionMinimizer_energy hA P hP y⟩, ?_⟩
  rintro e ⟨x, hx, rfl⟩
  simpa only [hx] using compression_energy_lower hA P hP x

/-- Domination of full energies gives domination of the observed inverse response. -/
theorem compressed_inverse_le_of_energy {A : Matrix ι ι ℝ} {D : Matrix κ κ ℝ}
    (hA : A.PosDef) (hD : D.PosDef) (P : Matrix κ ι ℝ)
    (henergy : ∀ x : ι → ℝ, quadratic D (P *ᵥ x) ≤ quadratic A x) :
    compressedInverse A P ≤ D⁻¹ := by
  apply le_of_quadratic_le (real_congruence_posSemidef P hA.inv.posSemidef).isHermitian
    hD.inv.isHermitian
  intro f
  change quadratic (P * A⁻¹ * Pᵀ) f ≤ _
  rw [quadratic_congruence]
  let x := A⁻¹ *ᵥ (Pᵀ *ᵥ f)
  calc
    quadratic A⁻¹ (Pᵀ *ᵥ f) = 2 * ((Pᵀ *ᵥ f) ⬝ᵥ x) - quadratic A x :=
      (inverse_variational_attained hA _).symm
    _ ≤ 2 * ((Pᵀ *ᵥ f) ⬝ᵥ x) - quadratic D (P *ᵥ x) :=
      sub_le_sub_left (henergy x) _
    _ = 2 * (f ⬝ᵥ (P *ᵥ x)) - quadratic D (P *ᵥ x) :=
      congrArg (fun z => 2 * z - quadratic D (P *ᵥ x)) (transpose_pairing P f x).symm
    _ ≤ quadratic D⁻¹ f := inverse_variational_le hD _ _

/-- An inverse compression bound is equivalent to the needed lower bound on full energies. -/
theorem energy_lower_of_compressed_inverse_le {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (P : Matrix κ ι ℝ)
    (hP : Function.Surjective P.mulVec) (hcomp : compressedInverse A P ≤ B⁻¹)
    (x : ι → ℝ) : quadratic B (P *ᵥ x) ≤ quadratic A x := by
  have hi := inverse_antitone (compressedInverse_posDef hA P hP) hB.inv hcomp
  letI := hB.isUnit.invertible
  rw [Matrix.inv_inv_of_invertible] at hi
  exact (quadratic_mono hi (P *ᵥ x)).trans (compression_energy_lower hA P hP x)

omit [DecidableEq ι] in
theorem quadratic_add (A B : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadratic (A + B) x = quadratic A x + quadratic B x := by
  simp only [quadratic, Matrix.add_mulVec, dotProduct_add]

/-- The singular-source transfer rule after adding the same PSD free energy on the compressed space.
The full-space directions are retained throughout the quadratic comparison. -/
theorem inverse_compression_add_free {A : Matrix ι ι ℝ} {B E : Matrix κ κ ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hE : E.PosSemidef) (P : Matrix κ ι ℝ)
    (hP : Function.Surjective P.mulVec) (hcomp : compressedInverse A P ≤ B⁻¹) :
    compressedInverse (Pᵀ * E * P + A) P ≤ (E + B)⁻¹ := by
  have hp : (Pᵀ * E * P).PosSemidef := by
    simpa only [Matrix.transpose_transpose] using real_congruence_posSemidef Pᵀ hE
  have hfull : (Pᵀ * E * P + A).PosDef := Matrix.PosDef.posSemidef_add hp hA
  have hsmall : (E + B).PosDef := Matrix.PosDef.posSemidef_add hE hB
  apply compressed_inverse_le_of_energy hfull hsmall P
  intro x
  rw [quadratic_add, quadratic_add]
  have heq : quadratic (Pᵀ * E * P) x = quadratic E (P *ᵥ x) := by
    simpa only [Matrix.transpose_transpose] using quadratic_congruence Pᵀ E x
  rw [heq]
  exact add_le_add_left (energy_lower_of_compressed_inverse_le hA hB P hP hcomp x) _

/-- Restricting the variational problem to a subspace can only decrease inverse response. -/
theorem restricted_inverse_le {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (R : Matrix ι κ ℝ) (hR : Function.Injective R.mulVec) :
    R * (Rᵀ * A * R)⁻¹ * Rᵀ ≤ A⁻¹ := by
  have hc := hA.conjTranspose_mul_mul_same hR
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hc
  apply compressed_inverse_le_of_energy hc hA R
  intro x
  have heq := quadratic_congruence Rᵀ A x
  simpa only [Matrix.transpose_transpose] using heq.symm.le

theorem restricted_inverse_quadratic_le {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (R : Matrix ι κ ℝ) (hR : Function.Injective R.mulVec) (f : ι → ℝ) :
    quadratic (Rᵀ * A * R)⁻¹ (Rᵀ *ᵥ f) ≤ quadratic A⁻¹ f := by
  have h := quadratic_mono (restricted_inverse_le hA R hR) f
  rwa [quadratic_congruence] at h

end InverseComparison
end MatrixSpencer
