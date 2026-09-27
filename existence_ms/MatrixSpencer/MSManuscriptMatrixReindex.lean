import MatrixSpencer.KSOwnerReindex
import MatrixSpencer.PhaseRestriction

/-!
# Physical matrix-index permutation for the numerical MS epoch

The permutation is an actual finite input relabeling. It preserves the complex
Euclidean operator norm, Hermitian offsets, epoch centers, and owner potential.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptMatrixReindex
variable {ι n m : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def reindexVector (e : m ≃ n) (v : EuclideanSpace ℂ n) : EuclideanSpace ℂ m :=
  WithLp.toLp 2 (fun i => v (e i))

theorem reindexVector_norm (e : m ≃ n) (v : EuclideanSpace ℂ n) :
    ‖reindexVector e v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2,reindexVector,PiLp.toLp_apply]
  exact e.sum_comp (fun i => ‖v i‖^2)

theorem reindexVector_surjective (e : m ≃ n) : Function.Surjective (reindexVector e) := by
  intro w
  refine ⟨WithLp.toLp 2 (fun i => w (e.symm i)),?_⟩
  ext i
  change w (e.symm (e i)) = w i
  exact congrArg w (e.symm_apply_apply i)

theorem reindexVector_action (e : m ≃ n) (A : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    reindexVector e (Matrix.toEuclideanCLM (𝕜 := ℂ) A v) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (A.submatrix e e) (reindexVector e v) := by
  ext i
  change (∑ j,A (e i) j*v j) = ∑ j,A (e i) (e j)*v (e j)
  exact (e.sum_comp (fun j => A (e i) j*v j)).symm

/-- Exact complex operator-norm invariance, including zero dimension. -/
theorem norm_reindex (e : m ≃ n) (A : Matrix n n ℂ) : ‖A.submatrix e e‖ = ‖A‖ := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A.submatrix e e)‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro w
    obtain ⟨v,rfl⟩ := reindexVector_surjective e w
    rw [← reindexVector_action,reindexVector_norm,reindexVector_norm]
    exact (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm v
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    have h := (Matrix.toEuclideanCLM (𝕜 := ℂ) (A.submatrix e e)).le_opNorm (reindexVector e v)
    rw [← reindexVector_action,reindexVector_norm,reindexVector_norm] at h
    exact h

theorem reindex_isHermitian (e : m ≃ n) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A.submatrix e e).IsHermitian := hA.submatrix e

theorem reindex_contraction (e : m ≃ n) {A : Matrix n n ℂ} (hA : ‖A‖ ≤ 1) :
    ‖A.submatrix e e‖ ≤ 1 := by rwa [norm_reindex]

/-- The same physical index permutation on a stored Hermitian offset. -/
def selfAdjointReindex (e : m ≃ n) (H : selfAdjoint (Matrix n n ℂ)) : selfAdjoint (Matrix m m ℂ) :=
  ⟨(H:Matrix n n ℂ).submatrix e e,(show (H:Matrix n n ℂ).IsHermitian from H.property).submatrix e⟩

@[simp] theorem selfAdjointReindex_coe (e : m ≃ n) (H : selfAdjoint (Matrix n n ℂ)) :
    (selfAdjointReindex e H : Matrix m m ℂ) = (H:Matrix n n ℂ).submatrix e e := rfl

theorem selfAdjointReindex_norm (e : m ≃ n) (H : selfAdjoint (Matrix n n ℂ)) :
    ‖selfAdjointReindex e H‖ = ‖H‖ := norm_reindex e H.val

/-- Reindexing does not change the actual full physical center. -/
theorem epochCenter_reindex (e : m ≃ n) (H : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i,(A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    (epochCenter (selfAdjointReindex e H) (fun i => (A i).submatrix e e)
      (fun i => (hA i).submatrix e) x : Matrix m m ℂ) =
      (epochCenter H A hA x : Matrix n n ℂ).submatrix e e := by
  ext i j
  simp [epochCenter,hermitianMatrixFamily,selfAdjointReindex,Matrix.sum_apply,Matrix.smul_apply]

theorem ownerPotential_reindex (e : m ≃ n) (H : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i,(A i).IsHermitian) {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) (θ : ℝ) (x : EuclideanSpace ℝ ι) :
    ownerPotential (epochCenter (selfAdjointReindex e H) (fun i => (A i).submatrix e e)
      (fun i => (hA i).submatrix e) x) (fun i => (A i).submatrix e e) C θ =
      ownerPotential (epochCenter H A hA x) A C θ := by
  rw [epochCenter_reindex]
  exact KSOwnerReindex.ownerPotential_reindex _ A hA hC θ e

/-- The remaining live-family potential is invariant under the same
physical permutation; coefficient labels and the actual point stay fixed. -/
theorem remainingPotential_reindex (e : m ≃ n) (H : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i,(A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    PhaseRestriction.remainingPotential (selfAdjointReindex e H)
      (fun i => (A i).submatrix e e) (fun i => (hA i).submatrix e) x =
      PhaseRestriction.remainingPotential H A hA x := by
  unfold PhaseRestriction.remainingPotential
  rw [epochCenter_reindex]
  exact KSOwnerReindex.ownerPotential_reindex _ (PhaseRestriction.restrictedFamily A x)
    (PhaseRestriction.restrictedFamily_hermitian A hA x) Matrix.PosSemidef.one 1 e

end MatrixSpencer.MSManuscriptMatrixReindex
