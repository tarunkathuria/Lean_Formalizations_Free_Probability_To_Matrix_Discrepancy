import SimpleMS.FlatCovariance
import MatrixSpencer.CovarianceSampler

/-! A subspace frame selected by an eigendecomposition of its orthogonal
projection. Only the eigenvectors with nonzero eigenvalue are retained. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace SimpleMS.SpectralFrame
open MatrixSpencer
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hermitian (W : Submodule ℝ (EuclideanSpace ℝ ι)) :=
  (euclideanProjectionMatrix_posSemidef W).isHermitian

abbrev Index (W : Submodule ℝ (EuclideanSpace ℝ ι)) :=
  {j : ι // (hermitian W).eigenvalues j ≠ 0}

def vector (W : Submodule ℝ (EuclideanSpace ℝ ι)) (j : Index W) : EuclideanSpace ℝ ι :=
  (hermitian W).eigenvectorBasis j.val

lemma eigenvalue_zero_or_one (W : Submodule ℝ (EuclideanSpace ℝ ι)) (j : ι) :
    (hermitian W).eigenvalues j = 0 ∨ (hermitian W).eigenvalues j = 1 := by
  let P := euclideanProjectionMatrix W
  let u := (hermitian W).eigenvectorBasis j
  let e := (hermitian W).eigenvalues j
  have hid : P * P = P := (euclideanProjectionMatrix_isStarProjection W).isIdempotentElem.eq
  have he : Matrix.toEuclideanCLM (𝕜 := ℝ) P u = e • u := by
    apply (WithLp.equiv 2 (ι → ℝ)).injective
    exact (hermitian W).mulVec_eigenvectorBasis j
  have hh : e • (e • u) = e • u := by
    calc
      _ = Matrix.toEuclideanCLM (𝕜 := ℝ) P (Matrix.toEuclideanCLM (𝕜 := ℝ) P u) := by rw [he,map_smul,he]
      _ = Matrix.toEuclideanCLM (𝕜 := ℝ) (P*P) u := by rw [map_mul]; rfl
      _ = e • u := by rw [hid,he]
  have hn : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq,(hermitian W).eigenvectorBasis.orthonormal.norm_eq_one j]
    norm_num
  have hs := congrArg (fun v => inner ℝ u v) hh
  simp only [inner_smul_right,hn,mul_one] at hs
  have hpoly : e*(e-1)=0 := by nlinarith
  rcases mul_eq_zero.mp hpoly with hz | hz
  · exact Or.inl hz
  · exact Or.inr (by linarith)

lemma eigenvalue_eq_one (W : Submodule ℝ (EuclideanSpace ℝ ι)) (j : Index W) :
    (hermitian W).eigenvalues j.val = 1 :=
  (eigenvalue_zero_or_one W j.val).resolve_left j.property

lemma vector_mem (W : Submodule ℝ (EuclideanSpace ℝ ι)) (j : Index W) : vector W j ∈ W := by
  obtain ⟨v,hv⟩ := covarianceEigenvector_mem_range (hermitian W) j.property
  unfold vector
  rw [←hv]
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanProjectionMatrix W) v ∈ W
  rw [toEuclideanCLM_projectionMatrix]
  exact W.starProjection_apply_mem v

lemma vector_norm (W : Submodule ℝ (EuclideanSpace ℝ ι)) (j : Index W) : ‖vector W j‖=1 :=
  (hermitian W).eigenvectorBasis.orthonormal.norm_eq_one _

lemma card_index (W : Submodule ℝ (EuclideanSpace ℝ ι)) :
    Fintype.card (Index W) = Module.finrank ℝ W := by
  have hh : (Fintype.card (Index W) : ℝ) = realTrace (euclideanProjectionMatrix W) := by
    rw [realTrace_real_eq_sum_eigenvalues (hermitian W)]
    change (Fintype.card {j : ι // (hermitian W).eigenvalues j ≠ 0} : ℝ) = _
    rw [Fintype.card_subtype, ←Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro j _
    rcases eigenvalue_zero_or_one W j with hz | ho
    · simp [hz]
    · simp [ho]
  rw [euclideanProjectionMatrix_trace] at hh
  exact_mod_cast hh

lemma rankOne_sum (W : Submodule ℝ (EuclideanSpace ℝ ι)) :
    (∑j : Index W,realRankOne (WithLp.ofLp (vector W j))) = euclideanProjectionMatrix W := by
  have hs := sum_eigenvalue_rankOne (hermitian W)
  apply Eq.trans _ hs
  classical
  have hh := Fintype.sum_subtype_add_sum_subtype (fun j => (hermitian W).eigenvalues j ≠ 0)
    (fun j => (hermitian W).eigenvalues j • realRankOne (WithLp.ofLp ((hermitian W).eigenvectorBasis j)))
  have hz : (∑j : {j : ι // ¬(hermitian W).eigenvalues j ≠ 0},
      (hermitian W).eigenvalues j.val • realRankOne (WithLp.ofLp ((hermitian W).eigenvectorBasis j.val))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp only [not_not.mp j.property,zero_smul]
  rw [hz,add_zero] at hh
  apply Eq.trans _ hh
  apply Finset.sum_congr rfl
  intro j _
  simp only [eigenvalue_eq_one,one_smul,vector]

end SimpleMS.SpectralFrame
