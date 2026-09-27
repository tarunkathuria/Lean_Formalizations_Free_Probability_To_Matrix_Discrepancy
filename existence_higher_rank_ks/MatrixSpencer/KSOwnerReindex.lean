import MatrixSpencer.OwnerPotential

/-!
# Reindexing invariance of the full owner density optimization

A finite equivalence only relabels matrix coordinates. The density-domain
bijection, covariance source, positive square roots, fidelity, objective and
optimized potential are all preserved. No restriction of the density domain
or assumption about an optimizer is used.
-/

open Matrix Set
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace MatrixSpencer.KSOwnerReindex

variable {ι n m : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

omit [DecidableEq n] [DecidableEq m] in
theorem realTrace_reindex (A : Matrix n n ℂ) (e : m ≃ n) :
    realTrace (A.submatrix e e) = realTrace A := by
  have ht : Matrix.trace (A.submatrix e e) = Matrix.trace A :=
    e.sum_comp (fun i => A i i)
  simp only [realTrace, ht]

theorem sqrt_reindex (A : Matrix n n ℂ) (hA : A.PosSemidef) (e : m ≃ n) :
    CFC.sqrt (A.submatrix e e) = (CFC.sqrt A).submatrix e e := by
  apply CFC.sqrt_unique
  · rw [Matrix.submatrix_mul_equiv, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact ((CFC.sqrt_nonneg A).posSemidef.submatrix e).nonneg

omit [DecidableEq n] [DecidableEq m] in
theorem density_reindex (S : Matrix n n ℂ) (e : m ≃ n) (hS : S ∈ densitySet) :
    S.submatrix e e ∈ densitySet :=
  ⟨hS.1.submatrix e, (realTrace_reindex S e).trans hS.2⟩

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem reindex_inverse (S : Matrix n n ℂ) (e : m ≃ n) :
    (S.submatrix e e).submatrix e.symm e.symm = S := by
  ext i j
  change S (e (e.symm i)) (e (e.symm j)) = S i j
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

omit [DecidableEq n] [DecidableEq m] in
theorem density_reindex_iff (S : Matrix n n ℂ) (e : m ≃ n) :
    S.submatrix e e ∈ densitySet ↔ S ∈ densitySet := by
  refine ⟨fun h => ?_, density_reindex S e⟩
  simpa only [reindex_inverse] using density_reindex (S.submatrix e e) e.symm h

omit [DecidableEq n] [DecidableEq m] in
/-- Every density on the relabelled matrix space comes from one original density. -/
theorem density_reindex_surjective (e : m ≃ n) (T : Matrix m m ℂ) (hT : T ∈ densitySet) :
    ∃ S ∈ densitySet, S.submatrix e e = T := by
  refine ⟨T.submatrix e.symm e.symm, density_reindex T e.symm hT, ?_⟩
  simpa only [Equiv.symm_symm] using reindex_inverse T e.symm

omit [DecidableEq ι] [DecidableEq n] [DecidableEq m] in
theorem covarianceSource_reindex (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ)
    (S : Matrix n n ℂ) (e : m ≃ n) :
    covarianceSource (fun i => (A i).submatrix e e) C (S.submatrix e e) =
      (covarianceSource A C S).submatrix e e := by
  simp only [covarianceSource, Matrix.submatrix_mul_equiv]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply]

theorem fidelity_reindex (S M : Matrix n n ℂ) (hS : S.PosSemidef) (hM : M.PosSemidef)
    (e : m ≃ n) : fidelity (S.submatrix e e) (M.submatrix e e) = fidelity S M := by
  have hG : (CFC.sqrt S * M * CFC.sqrt S).PosSemidef := by
    simpa only [(CFC.sqrt_nonneg S).posSemidef.isHermitian.eq] using
      hM.mul_mul_conjTranspose_same (CFC.sqrt S)
  simp only [fidelity, fidelityCore, sqrt_reindex S hS e, Matrix.submatrix_mul_equiv]
  rw [sqrt_reindex _ hG, realTrace_reindex]

theorem ownerObjective_reindex (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (θ : ℝ) (S : Matrix n n ℂ) (hS : S.PosSemidef) (e : m ≃ n) :
    ownerObjective (H.submatrix e e) (fun i => (A i).submatrix e e) C θ (S.submatrix e e) =
      ownerObjective H A C θ S := by
  simp only [ownerObjective, Matrix.submatrix_mul_equiv, realTrace_reindex,
    covarianceSource_reindex, sqrt_reindex S hS e]
  rw [fidelity_reindex S _ hS (covarianceSource_posSemidef A hA hC hS)]

/-- The image of all density values is unchanged, not merely the chosen maximizer. -/
theorem ownerObjective_image_reindex (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (θ : ℝ) (e : m ≃ n) :
    ownerObjective (H.submatrix e e) (fun i => (A i).submatrix e e) C θ '' densitySet =
      ownerObjective H A C θ '' densitySet := by
  ext r
  constructor
  · rintro ⟨T, hT, hr⟩
    obtain ⟨S, hS, rfl⟩ := density_reindex_surjective e T hT
    exact ⟨S, hS, (ownerObjective_reindex H A hA hC θ S hS.1 e).symm.trans hr⟩
  · rintro ⟨S, hS, hr⟩
    exact ⟨S.submatrix e e, density_reindex S e hS,
      (ownerObjective_reindex H A hA hC θ S hS.1 e).trans hr⟩

theorem ownerPotential_reindex (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (θ : ℝ) (e : m ≃ n) :
    ownerPotential (H.submatrix e e) (fun i => (A i).submatrix e e) C θ = ownerPotential H A C θ := by
  unfold ownerPotential
  rw [ownerObjective_image_reindex H A hA hC θ e]

end MatrixSpencer.KSOwnerReindex
