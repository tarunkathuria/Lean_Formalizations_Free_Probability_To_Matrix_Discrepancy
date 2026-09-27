import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Algebra for an actual symmetric-elimination PSD separator

The quadratic identities below justify a positive scalar pivot and a
negative witness at a zero pivot with a nonzero off-diagonal entry. They
use only field arithmetic and absolute value; no eigensystem is selected.
-/

open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSFullManuscriptPSDAlgebra

variable {n : ℕ}

def quadratic {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x)

def tail (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A.submatrix Fin.succ Fin.succ

def row (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Fin n → ℝ :=
  fun j => A 0 j.succ

def schur (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0

def lift (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (-(row A ⬝ᵥ x) / A 0 0) x

theorem quadratic_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (j : ι) (s : ℝ) :
    quadratic A (Pi.single j s) = s ^ 2 * A j j := by
  simp [quadratic, dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite]
  ring

theorem quadratic_cons (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.IsSymm) (t : ℝ) (x : Fin n → ℝ) :
    quadratic A (Fin.cons t x) =
      A 0 0 * t ^ 2 + 2 * t * (row A ⬝ᵥ x) + quadratic (tail A) x := by
  have hc : ∀ i : Fin n, A i.succ 0 = A 0 i.succ :=
    fun i => congrFun (congrFun hA 0) i.succ
  simp only [quadratic, dotProduct, Matrix.mulVec, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, tail, Matrix.submatrix_apply, row]
  simp_rw [hc, mul_add, Finset.sum_add_distrib]
  have hs : (∑ i, x i * (A 0 i.succ * t)) = t * ∑ i, A 0 i.succ * x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

theorem schur_isSymm (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.IsSymm) : (schur A).IsSymm := by
  ext i j
  change schur A j i = schur A i j
  have h₁ : A j.succ i.succ = A i.succ j.succ := congrFun (congrFun hA i.succ) j.succ
  have h₂ : A i.succ 0 = A 0 i.succ := congrFun (congrFun hA 0) i.succ
  have h₃ : A j.succ 0 = A 0 j.succ := congrFun (congrFun hA 0) j.succ
  simp only [schur, h₁, h₂, h₃]
  ring

theorem quadratic_schur (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.IsSymm) (x : Fin n → ℝ) :
    quadratic (schur A) x = quadratic (tail A) x - (row A ⬝ᵥ x) ^ 2 / A 0 0 := by
  have hc : ∀ i : Fin n, A i.succ 0 = A 0 i.succ :=
    fun i => congrFun (congrFun hA 0) i.succ
  simp only [quadratic, dotProduct, Matrix.mulVec, schur, tail, Matrix.submatrix_apply, row]
  simp_rw [hc, sub_mul, Finset.sum_sub_distrib, mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [pow_two, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem positive_pivot_identity (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.IsSymm) (ha : A 0 0 ≠ 0) (t : ℝ) (x : Fin n → ℝ) :
    quadratic A (Fin.cons t x) =
      A 0 0 * (t + (row A ⬝ᵥ x) / A 0 0) ^ 2 + quadratic (schur A) x := by
  rw [quadratic_cons A hA, quadratic_schur A hA]
  field_simp
  ring

theorem quadratic_lift (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.IsSymm) (ha : A 0 0 ≠ 0) (x : Fin n → ℝ) :
    quadratic A (lift A x) = quadratic (schur A) x := by
  rw [lift, positive_pivot_identity A hA ha]
  simp only [neg_div, neg_add_cancel, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add]

def zeroPivotScale (b c : ℝ) : ℝ := -b / (|c| + 1)

theorem zeroPivotScale_negative {b c : ℝ} (hb : b ≠ 0) :
    2 * b * zeroPivotScale b c + c * zeroPivotScale b c ^ 2 < 0 := by
  have hd : 0 < |c| + 1 := by positivity
  have he : 2 * b * zeroPivotScale b c + c * zeroPivotScale b c ^ 2 =
      (b ^ 2 / (|c| + 1) ^ 2) * (c - 2 * (|c| + 1)) := by
    unfold zeroPivotScale
    field_simp
    ring
  rw [he]
  exact mul_neg_of_pos_of_neg (div_pos (sq_pos_of_ne_zero hb) (sq_pos_of_pos hd))
    (by linarith [le_abs_self c, abs_nonneg c])

def zeroPivotWitness (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j : Fin n) :
    Fin (n + 1) → ℝ :=
  Fin.cons 1 (Pi.single j (zeroPivotScale (A 0 j.succ) (A j.succ j.succ)))

theorem zeroPivotWitness_negative (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.IsSymm) (ha : A 0 0 = 0) (j : Fin n) (hb : A 0 j.succ ≠ 0) :
    quadratic A (zeroPivotWitness A j) < 0 := by
  rw [zeroPivotWitness, quadratic_cons A hA, quadratic_single]
  simp only [ha, zero_mul, zero_add, mul_one, dotProduct_single, row, tail, Matrix.submatrix_apply]
  have hs := zeroPivotScale_negative (c := A j.succ j.succ) hb
  nlinarith

end MatrixSpencer.KSFullManuscriptPSDAlgebra
