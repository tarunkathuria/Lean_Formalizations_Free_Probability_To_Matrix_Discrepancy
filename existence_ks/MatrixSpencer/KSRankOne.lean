import MatrixSpencer.Statement
import MatrixSpencer.TraceGeometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Physical complex rank-one atoms for the Kadison--Singer routes

These are physical atoms `v v*`, not rank-one coefficient covariances.
The sandwich identity holds for every complex matrix, and the real-trace
version holds for Hermitian inputs. Every norm statement uses the Euclidean
operator norm explicitly or the `L2Operator` matrix norm scope.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer.KSRankOne

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The physical positive semidefinite atom with entries `v i * conj (v j)`. -/
def atom (v : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec v (star v)

@[simp] theorem atom_apply (v : n → ℂ) (i j : n) :
    atom v i j = v i * star (v j) := rfl

theorem atom_posSemidef (v : n → ℂ) : (atom v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

theorem atom_isHermitian (v : n → ℂ) : (atom v).IsHermitian :=
  (atom_posSemidef v).isHermitian

@[simp] theorem atom_zero : atom (0 : n → ℂ) = 0 := by
  ext i j
  simp [atom]

theorem trace_atom (v : n → ℂ) :
    Matrix.trace (atom v) = ∑ i, (Complex.normSq (v i) : ℂ) := by
  simp only [atom, Matrix.trace_vecMulVec, dotProduct, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact Complex.mul_conj (v i)

theorem realTrace_atom (v : n → ℂ) :
    realTrace (atom v) = ∑ i, Complex.normSq (v i) := by
  simp [realTrace, trace_atom]

theorem realTrace_atom_eq_norm_sq (v : n → ℂ) :
    realTrace (atom v) = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 := by
  rw [realTrace_atom, EuclideanSpace.norm_sq_eq]
  simp only [Complex.normSq_eq_norm_sq]
  rfl

theorem atom_realTrace_pos {v : n → ℂ} (hv : v ≠ 0) :
    0 < realTrace (atom v) := by
  rw [realTrace_atom_eq_norm_sq]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro h
  apply hv
  exact congrArg WithLp.ofLp h

theorem atom_eq_zero_iff (v : n → ℂ) : atom v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    have hp := atom_realTrace_pos hv
    simpa only [h, realTrace_zero, lt_self_iff_false] using hp
  · rintro rfl
    exact atom_zero

/-- Rank-one congruence equals the trace-and-prepare source, without a
Hermitian hypothesis on the argument. -/
theorem atom_sandwich (v : n → ℂ) (X : Matrix n n ℂ) :
    atom v * X * atom v = Matrix.trace (atom v * X) • atom v := by
  unfold atom
  rw [Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.trace_vecMulVec]
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [dotProduct_comm v]
  ring

theorem trace_eq_realTrace_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Matrix.trace A = (realTrace A : ℂ) := by
  symm
  apply Complex.conj_eq_iff_re.mp
  change star (Matrix.trace A) = Matrix.trace A
  rw [← Matrix.trace_conjTranspose, hA.eq]

theorem trace_mul_eq_realTrace {A X : Matrix n n ℂ}
    (hA : A.IsHermitian) (hX : X.IsHermitian) :
    Matrix.trace (A * X) = (realTrace (A * X) : ℂ) := by
  symm
  apply Complex.conj_eq_iff_re.mp
  change star (Matrix.trace (A * X)) = Matrix.trace (A * X)
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hX.eq,
    Matrix.trace_mul_comm]

theorem atom_sandwich_real (v : n → ℂ) {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    atom v * X * atom v = realTrace (atom v * X) • atom v := by
  rw [atom_sandwich, trace_mul_eq_realTrace (atom_isHermitian v) hX]
  rfl

theorem atom_sq (v : n → ℂ) : atom v * atom v = Matrix.trace (atom v) • atom v := by
  simpa only [Matrix.mul_one] using atom_sandwich v (1 : Matrix n n ℂ)

theorem atom_sq_real (v : n → ℂ) : atom v * atom v = realTrace (atom v) • atom v := by
  rw [atom_sq, trace_eq_realTrace_of_isHermitian (atom_isHermitian v)]
  rfl

/-- The Euclidean operator norm of a physical rank-one atom equals its trace. -/
theorem atom_norm (v : n → ℂ) : ‖atom v‖ = realTrace (atom v) := by
  letI : CStarAlgebra (Matrix n n ℂ) := {}
  by_cases hA : atom v = 0
  · simp [hA]
  · have hp : 0 < ‖atom v‖ := norm_pos_iff.mpr hA
    have ht : 0 ≤ realTrace (atom v) := realTrace_nonneg (atom_posSemidef v)
    have hn := (show IsSelfAdjoint (atom v) from atom_isHermitian v).norm_mul_self
    rw [atom_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hn
    nlinarith

theorem atom_operatorNorm (v : n → ℂ) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (atom v)‖ = realTrace (atom v) :=
  atom_norm v

theorem atom_spectralNorm {d : ℕ} (v : Fin d → ℂ) :
    spectralNorm (atom v) = realTrace (atom v) :=
  atom_operatorNorm v

/-- The rank-one Kraus channel and its trace-and-prepare expression agree. -/
theorem sum_atom_sandwich {ι : Type*} [Fintype ι]
    (v : ι → n → ℂ) (X : Matrix n n ℂ) :
    (∑ i, atom (v i) * X * atom (v i)) =
      ∑ i, Matrix.trace (atom (v i) * X) • atom (v i) := by
  exact Finset.sum_congr rfl (fun i _ => atom_sandwich (v i) X)

theorem sum_atom_sandwich_real {ι : Type*} [Fintype ι]
    (v : ι → n → ℂ) {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    (∑ i, atom (v i) * X * atom (v i)) =
      ∑ i, realTrace (atom (v i) * X) • atom (v i) := by
  exact Finset.sum_congr rfl (fun i _ => atom_sandwich_real (v i) hX)

theorem fixedPoint_iff_tracePrepare {ι : Type*} [Fintype ι]
    (v : ι → n → ℂ) {P : Matrix n n ℂ} (hP : P.IsHermitian) :
    (∑ i, atom (v i) * P * atom (v i)) = P ↔
      (∑ i, realTrace (P * atom (v i)) • atom (v i)) = P := by
  rw [sum_atom_sandwich_real v hP]
  simp only [realTrace_mul_comm (atom _) P]

end MatrixSpencer.KSRankOne
