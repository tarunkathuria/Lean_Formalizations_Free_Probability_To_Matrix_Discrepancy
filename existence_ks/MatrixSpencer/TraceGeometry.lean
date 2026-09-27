import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# Real trace geometry for Matrix Spencer

These lemmas use explicit real parts of traces. They do not choose a matrix norm,
so they can be used with both the physical operator norm and Frobenius geometry.
-/

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace MatrixSpencer

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

/-- The unnormalized real trace. -/
def realTrace (A : Matrix n n 𝕜) : ℝ := RCLike.re (Matrix.trace A)

@[simp] theorem realTrace_zero : realTrace (0 : Matrix n n 𝕜) = 0 := by
  simp [realTrace]

@[simp] theorem realTrace_add (A B : Matrix n n 𝕜) :
    realTrace (A + B) = realTrace A + realTrace B := by
  simp [realTrace]

@[simp] theorem realTrace_sub (A B : Matrix n n 𝕜) :
    realTrace (A - B) = realTrace A - realTrace B := by
  simp [realTrace]

@[simp] theorem realTrace_neg (A : Matrix n n 𝕜) :
    realTrace (-A) = -realTrace A := by
  simp [realTrace]

@[simp] theorem realTrace_smul (r : ℝ) (A : Matrix n n 𝕜) :
    realTrace (r • A) = r * realTrace A := by
  simp [realTrace, RCLike.smul_re]

@[simp] theorem realTrace_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix n n 𝕜) :
    realTrace (∑ i ∈ s, A i) = ∑ i ∈ s, realTrace (A i) := by
  simp [realTrace]

theorem realTrace_mul_comm (A B : Matrix n n 𝕜) :
    realTrace (A * B) = realTrace (B * A) := by
  exact congrArg RCLike.re (Matrix.trace_mul_comm A B)

theorem realTrace_mul_cycle (A B C : Matrix n n 𝕜) :
    realTrace (A * B * C) = realTrace (C * A * B) := by
  exact congrArg RCLike.re (Matrix.trace_mul_cycle A B C)

theorem realTrace_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    0 ≤ realTrace A :=
  (RCLike.nonneg_iff.mp hA.trace_nonneg).1

theorem realTrace_conjTranspose_mul_self_nonneg (A : Matrix n n 𝕜) :
    0 ≤ realTrace (Aᴴ * A) :=
  realTrace_nonneg (Matrix.posSemidef_conjTranspose_mul_self A)

theorem realTrace_conjTranspose_mul_self_eq_zero_iff (A : Matrix n n 𝕜) :
    realTrace (Aᴴ * A) = 0 ↔ A = 0 := by
  constructor
  · intro h
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    apply RCLike.ext
    · simpa only [realTrace, map_zero] using h
    · simpa only [map_zero] using
        (RCLike.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self A).trace_nonneg).2
  · rintro rfl
    simp

variable [DecidableEq n]

/-- The trace pairing of positive matrices is nonnegative, without commutation. -/
theorem realTrace_mul_nonneg {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ realTrace (A * B) := by
  have hs : (CFC.sqrt A).IsHermitian := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have h := realTrace_nonneg (hB.mul_mul_conjTranspose_same (CFC.sqrt A))
  rw [hs.eq, realTrace_mul_cycle, CFC.sqrt_mul_sqrt_self A hA.nonneg] at h
  exact h

/-- Order comparison is used only after pairing with a positive matrix. -/
theorem realTrace_mul_mono {X A B : Matrix n n 𝕜}
    (hX : X.PosSemidef) (hAB : A ≤ B) :
    realTrace (X * A) ≤ realTrace (X * B) := by
  have h := realTrace_mul_nonneg hX (Matrix.le_iff.mp hAB)
  rw [Matrix.mul_sub, realTrace_sub] at h
  linarith

omit [DecidableEq n] in
/-- The exact squared-commutator identity behind the balanced square-root budget. -/
theorem realTrace_commutator_identity {X Y : Matrix n n 𝕜}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    realTrace ((X * Y - Y * X)ᴴ * (X * Y - Y * X)) =
      2 * (realTrace (X * X * Y * Y) - realTrace (X * Y * X * Y)) := by
  have h₁ : realTrace (Y * X * (X * Y)) = realTrace (X * X * Y * Y) := by
    simpa only [Matrix.mul_assoc] using realTrace_mul_comm Y (X * X * Y)
  have h₂ : realTrace (X * Y * (Y * X)) = realTrace (X * X * Y * Y) := by
    simpa only [Matrix.mul_assoc] using realTrace_mul_cycle X (Y * Y) X
  have h₃ : realTrace (Y * X * (Y * X)) = realTrace (X * Y * X * Y) := by
    simpa only [Matrix.mul_assoc] using realTrace_mul_comm Y (X * Y * X)
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    hX.eq, hY.eq]
  simp only [Matrix.sub_mul, Matrix.mul_sub, realTrace_sub]
  rw [h₁, h₂, h₃]
  simp only [Matrix.mul_assoc]
  ring

omit [DecidableEq n] in
/-- A noncommutative trace inequality; neither factor has to be positive. -/
theorem realTrace_mul_mul_mul_le {X Y : Matrix n n 𝕜}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    realTrace (X * Y * X * Y) ≤ realTrace (X * X * Y * Y) := by
  have h := realTrace_conjTranspose_mul_self_nonneg (X * Y - Y * X)
  rw [realTrace_commutator_identity hX hY] at h
  linarith

/-- The square-root version used to control the physical balanced response. -/
theorem realTrace_sqrt_cross_le {W S : Matrix n n 𝕜}
    (hW : W.IsHermitian) (hS : S.PosSemidef) :
    realTrace (W * CFC.sqrt S * W * CFC.sqrt S) ≤ realTrace (W * W * S) := by
  have h := realTrace_mul_mul_mul_le hW (CFC.sqrt_nonneg S).posSemidef.isHermitian
  simpa only [Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self S hS.nonneg] using h

/-- Congruencing a positive square root gives the trace-square budget used for `R`.
There is no commutation assumption between the congruence matrix and the density. -/
theorem realTrace_balanced_square_le {V S : Matrix n n 𝕜}
    (hV : V.IsHermitian) (hS : S.PosSemidef) :
    realTrace ((V * CFC.sqrt S * V) * (V * CFC.sqrt S * V)) ≤
      realTrace ((V * V) * S * (V * V)) := by
  have hVV : (V * V).IsHermitian := by
    simpa only [pow_two] using hV.pow 2
  calc
    realTrace ((V * CFC.sqrt S * V) * (V * CFC.sqrt S * V)) =
        realTrace ((V * V) * CFC.sqrt S * (V * V) * CFC.sqrt S) := by
      simpa only [Matrix.mul_assoc] using
        realTrace_mul_comm (V * CFC.sqrt S * V * V * CFC.sqrt S) V
    _ ≤ realTrace ((V * V) * (V * V) * S) := realTrace_sqrt_cross_le hVV hS
    _ = realTrace ((V * V) * S * (V * V)) :=
      (realTrace_mul_cycle (V * V) S (V * V)).symm

omit [DecidableEq n] in
/-- The source trace is the pairing of the density with the Kraus square sum. -/
theorem realTrace_kraus_sum {ι : Type*} [Fintype ι]
    (B : ι → Matrix n n 𝕜) (S : Matrix n n 𝕜) :
    realTrace (∑ i, B i * S * B i) = realTrace (S * ∑ i, B i * B i) := by
  simp only [Matrix.mul_sum, realTrace, Matrix.trace_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.trace_mul_cycle]
  rw [Matrix.trace_mul_comm (B i * B i) S]

/-- A source trace budget with all positivity assumptions explicit. -/
theorem realTrace_kraus_sum_le {ι : Type*} [Fintype ι]
    (B : ι → Matrix n n 𝕜) {S : Matrix n n 𝕜} (hS : S.PosSemidef)
    {κ : ℝ} (hB : (∑ i, B i * B i) ≤ κ • (1 : Matrix n n 𝕜)) :
    realTrace (∑ i, B i * S * B i) ≤ κ * realTrace S := by
  rw [realTrace_kraus_sum]
  have h := realTrace_mul_mono hS hB
  simpa only [mul_smul_comm, Matrix.mul_one, realTrace_smul] using h

end MatrixSpencer
