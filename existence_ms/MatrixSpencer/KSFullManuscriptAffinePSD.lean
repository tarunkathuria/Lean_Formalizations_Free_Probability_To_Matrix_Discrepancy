import MatrixSpencer.KSFullManuscriptPSDSeparation
import MatrixSpencer.KSFullManuscriptEllipsoidRun
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A computed separator for affine real matrix inequalities

The matrix pencil and its separating normal are finite sums of input entries.
The actual symmetric-elimination report supplies either a PSD certificate or
a negative quadratic vector. A known feasible point proves that a returned
normal cannot vanish. Thus the ellipsoid separator contract is discharged
for the specified affine matrix data, without a PSD or eigenvector oracle.

The full-cube density SDP still has to be translated into these affine data
and its concrete inner/outer radius certificates supplied.
-/

open Matrix
open scoped BigOperators InnerProductSpace
noncomputable section
namespace MatrixSpencer.KSFullManuscriptAffinePSD

open KSFullManuscriptPSDAlgebra KSFullManuscriptEllipsoidRun
variable {ℓ n : ℕ}
abbrev Space (ℓ : ℕ) := EuclideanSpace ℝ (Fin ℓ)

structure Data (ℓ n : ℕ) where
  constant : Matrix (Fin n) (Fin n) ℝ
  coefficient : Fin ℓ → Matrix (Fin n) (Fin n) ℝ
  constant_symmetric : constant.IsSymm
  coefficient_symmetric : ∀ i, (coefficient i).IsSymm

def matrixAt (D : Data ℓ n) (x : Space ℓ) : Matrix (Fin n) (Fin n) ℝ :=
  D.constant + ∑ i, x i • D.coefficient i

def target (D : Data ℓ n) : Set (Space ℓ) := {x | (matrixAt D x).PosSemidef}

theorem matrixAt_isSymm (D : Data ℓ n) (x : Space ℓ) : (matrixAt D x).IsSymm := by
  unfold matrixAt
  apply D.constant_symmetric.add
  change (∑ i, x i • D.coefficient i)ᵀ = ∑ i, x i • D.coefficient i
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (D.coefficient_symmetric i).smul (x i)

theorem quadratic_matrixAt (D : Data ℓ n) (x : Space ℓ) (v : Fin n → ℝ) :
    quadratic (matrixAt D x) v = quadratic D.constant v +
      ∑ i, x i * quadratic (D.coefficient i) v := by
  simp only [matrixAt, quadratic, Matrix.add_mulVec, dotProduct_add,
    Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

def normal (D : Data ℓ n) (v : Fin n → ℝ) : Space ℓ :=
  WithLp.toLp 2 (fun i => -quadratic (D.coefficient i) v)

theorem normal_inner (D : Data ℓ n) (v : Fin n → ℝ) (x y : Space ℓ) :
    ⟪normal D v, y - x⟫_ℝ = quadratic (matrixAt D x) v - quadratic (matrixAt D y) v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, quadratic_matrixAt, quadratic_matrixAt]
  simp only [star_trivial, normal, dotProduct]
  calc
    _ = ∑ i, (x i * quadratic (D.coefficient i) v - y i * quadratic (D.coefficient i) v) := by
      apply Finset.sum_congr rfl
      intro i _
      change (y i - x i) * (-quadratic (D.coefficient i) v) = _
      ring
    _ = _ := by rw [Finset.sum_sub_distrib]; ring

/-- Compute the PSD report and, when needed, its finite-entry separating normal. -/
def query (D : Data ℓ n) (x : Space ℓ) : Option (Space ℓ) :=
  (KSFullManuscriptPSDSeparation.report n (matrixAt D x)).map (normal D)

theorem query_none_iff (D : Data ℓ n) (x : Space ℓ) : query D x = none ↔ x ∈ target D := by
  rw [query, Option.map_eq_none_iff]
  exact KSFullManuscriptPSDSeparation.report_none_iff _ (matrixAt_isSymm D x)

theorem negative_separates (D : Data ℓ n) (x : Space ℓ) {v : Fin n → ℝ}
    (hv : quadratic (matrixAt D x) v < 0) (y : Space ℓ) (hy : y ∈ target D) :
    ⟪normal D v, y - x⟫_ℝ < 0 := by
  rw [normal_inner]
  have hpos : 0 ≤ quadratic (matrixAt D y) v := by simpa only [star_trivial] using hy.2 v
  linarith

theorem negative_normal_nonzero (D : Data ℓ n) (x : Space ℓ) {v : Fin n → ℝ}
    (hv : quadratic (matrixAt D x) v < 0) (z : Space ℓ) (hz : z ∈ target D) :
    normal D v ≠ 0 := by
  intro hn
  have hh := negative_separates D x hv z hz
  simp only [hn, inner_zero_left, lt_self_iff_false] at hh

/-- The separating routine is the actual finite symmetric-elimination
computation. The feasible point is used only to certify its nonzero normals. -/
def procedure (D : Data ℓ n) (z : Space ℓ) (hz : z ∈ target D) :
    SeparationProcedure (target D) where
  query := query D
  feasible := fun x hx => (query_none_iff D x).mp hx
  separates := by
    intro x g hg
    unfold query at hg
    cases hr : KSFullManuscriptPSDSeparation.report n (matrixAt D x) with
    | none => simp [hr] at hg
    | some v =>
      simp only [hr, Option.map_some, Option.some.injEq] at hg
      have hv := KSFullManuscriptPSDSeparation.report_some_negative _ (matrixAt_isSymm D x) hr
      subst g
      exact ⟨negative_normal_nonzero D x hv z hz,
        fun y hy => (negative_separates D x hv y hy).le⟩

end MatrixSpencer.KSFullManuscriptAffinePSD
