import MatrixSpencer.SqrtDerivative
import MatrixSpencer.SqrtContinuity
import MatrixSpencer.SqrtCompression

/-! Actual dyadic matrix roots, built only from the verified positive square
root. Their smoothness and compression properties require no additional
matrix-power calculus premise. -/

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
namespace MatrixSpencer
noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance dyadicRootCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicRootPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def dyadicRoot : ℕ → Matrix n n ℂ → Matrix n n ℂ
  | 0, S => S
  | m + 1, S => CFC.sqrt (dyadicRoot m S)

@[simp] theorem dyadicRoot_zero (S : Matrix n n ℂ) : dyadicRoot 0 S = S := rfl
@[simp] theorem dyadicRoot_succ (m : ℕ) (S : Matrix n n ℂ) :
    dyadicRoot (m + 1) S = CFC.sqrt (dyadicRoot m S) := rfl

theorem dyadicRoot_posSemidef (m : ℕ) {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    (dyadicRoot m S).PosSemidef := by
  cases m with
  | zero => exact hS
  | succ m => exact (CFC.sqrt_nonneg _).posSemidef

theorem dyadicRoot_posDef (m : ℕ) {S : Matrix n n ℂ} (hS : S.PosDef) :
    (dyadicRoot m S).PosDef := by
  induction m with
  | zero => exact hS
  | succ m ih => exact ih.posDef_sqrt

theorem dyadicRoot_mono (m : ℕ) {S T : Matrix n n ℂ} (hST : S ≤ T) :
    dyadicRoot m S ≤ dyadicRoot m T := by
  induction m with
  | zero => exact hST
  | succ m ih => exact CFC.sqrt_le_sqrt _ _ ih

theorem dyadicRoot_succ_square (m : ℕ) {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    dyadicRoot (m + 1) S ^ 2 = dyadicRoot m S := by
  rw [dyadicRoot_succ, pow_two]
  exact CFC.sqrt_mul_sqrt_self _ (dyadicRoot_posSemidef m hS).nonneg

/-- Repeated roots give the actual positive 2^m-th root. -/
theorem dyadicRoot_pow (m : ℕ) {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    dyadicRoot m S ^ (2 ^ m) = S := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2, pow_mul, dyadicRoot_succ_square m hS, ih]

theorem dyadicRoot_commute (m : ℕ) {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    Commute (dyadicRoot m S) S := by
  conv_rhs => rw [← dyadicRoot_pow m hS]
  exact Commute.self_pow _ _

theorem continuous_dyadicRoot_of_psd {X : Type*} [TopologicalSpace X]
    {S : X → Matrix n n ℂ} (hS : Continuous S) (hpos : ∀ x, (S x).PosSemidef) (m : ℕ) :
    Continuous (fun x => dyadicRoot m (S x)) := by
  induction m with
  | zero => exact hS
  | succ m ih => exact continuous_matrix_sqrt_of_psd ih (fun x => dyadicRoot_posSemidef m (hpos x))

/-- Compression uses only square-root compression and monotonicity at each level. -/
theorem dyadicRoot_compression_le {k : Type*} [Fintype k] [DecidableEq k]
    (m : ℕ) {S : Matrix n n ℂ} (hS : S.PosSemidef)
    (V : Matrix n k ℂ) (hV : V * Vᴴ ≤ 1) :
    Vᴴ * dyadicRoot m S * V ≤ dyadicRoot m (Vᴴ * S * V) := by
  letI : CStarAlgebra (Matrix k k ℂ) := {}
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    exact (sqrt_compression_le (dyadicRoot_posSemidef m hS) V hV).trans
      (CFC.sqrt_le_sqrt _ _ ih)

theorem dyadicRoot_isometry_compression_le {k : Type*} [Fintype k] [DecidableEq k]
    (m : ℕ) {S : Matrix n n ℂ} (hS : S.PosSemidef)
    (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) :
    Vᴴ * dyadicRoot m S * V ≤ dyadicRoot m (Vᴴ * S * V) := by
  have hP : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
    calc
      _ = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]
  exact dyadicRoot_compression_le m hS V
    (isHermitian_idempotent_le_one (Matrix.posSemidef_self_mul_conjTranspose V).isHermitian hP)

def hermitianDyadicRoot : ℕ → selfAdjoint (Matrix n n ℂ) → selfAdjoint (Matrix n n ℂ)
  | 0, S => S
  | m + 1, S => hermitianSqrt (hermitianDyadicRoot m S)

@[simp] theorem hermitianDyadicRoot_coe (m : ℕ) (S : selfAdjoint (Matrix n n ℂ)) :
    (hermitianDyadicRoot m S : Matrix n n ℂ) = dyadicRoot m (S : Matrix n n ℂ) := by
  induction m with
  | zero => rfl
  | succ m ih => simpa only [hermitianDyadicRoot, hermitianSqrt_coe, dyadicRoot_succ] using congrArg CFC.sqrt ih

theorem hermitianDyadicRoot_posDef (m : ℕ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    (hermitianDyadicRoot m S : Matrix n n ℂ).PosDef := by
  rw [hermitianDyadicRoot_coe]
  exact dyadicRoot_posDef m hS

theorem contDiffAt_hermitianDyadicRoot (m : ℕ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) : ContDiffAt ℝ ∞ (hermitianDyadicRoot m) S := by
  induction m with
  | zero => exact contDiffAt_id
  | succ m ih =>
    exact (contDiffAt_hermitianSqrt _ (hermitianDyadicRoot_posDef m S hS)).comp S ih

end
end MatrixSpencer
