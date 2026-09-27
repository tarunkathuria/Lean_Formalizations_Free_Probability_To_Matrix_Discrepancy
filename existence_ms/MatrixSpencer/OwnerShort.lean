import MatrixSpencer.TraceGeometry
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic

/-!
# Positive owner shorting

The construction uses a preimage subspace under a square root; it never inverts
the owner, so singular owners are included.
-/

open scoped MatrixOrder
open Matrix

namespace MatrixSpencer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Congruence of a positive contraction by an owner's positive square root. -/
noncomputable def ownerCompression (C P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  CFC.sqrt C * P * CFC.sqrt C

theorem ownerCompression_posSemidef (C : Matrix ι ι ℝ)
    {P : Matrix ι ι ℝ} (hP : P.PosSemidef) :
    (ownerCompression C P).PosSemidef := by
  have hs := (CFC.sqrt_nonneg C).posSemidef.isHermitian
  simpa only [ownerCompression, hs.eq] using hP.mul_mul_conjTranspose_same (CFC.sqrt C)

theorem ownerCompression_sub {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (P : Matrix ι ι ℝ) :
    C - ownerCompression C P = ownerCompression C (1 - P) := by
  simp only [ownerCompression, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    CFC.sqrt_mul_sqrt_self C hC.nonneg]

theorem ownerCompression_le {C P : Matrix ι ι ℝ}
    (hC : C.PosSemidef) (hP : P ≤ 1) : ownerCompression C P ≤ C := by
  apply Matrix.le_iff.mpr
  rw [ownerCompression_sub hC]
  exact ownerCompression_posSemidef C (Matrix.le_iff.mp hP)

theorem ownerCompression_trace_loss {C P : Matrix ι ι ℝ}
    (hC : C.PosSemidef) (hC1 : C ≤ 1) (hP : P ≤ 1) :
    realTrace (C - ownerCompression C P) ≤ realTrace (1 - P) := by
  rw [ownerCompression_sub hC, ownerCompression, realTrace_mul_cycle,
    CFC.sqrt_mul_sqrt_self C hC.nonneg, realTrace_mul_comm]
  simpa only [Matrix.mul_one] using realTrace_mul_mono (Matrix.le_iff.mp hP) hC1

/-- Orthogonal projection represented in the Euclidean coordinate basis. -/
noncomputable def euclideanProjectionMatrix
    (U : Submodule ℝ (EuclideanSpace ℝ ι)) : Matrix ι ι ℝ :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).symm U.starProjection

@[simp] theorem toEuclideanCLM_projectionMatrix
    (U : Submodule ℝ (EuclideanSpace ℝ ι)) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (euclideanProjectionMatrix U) =
      U.starProjection := by
  exact (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).apply_symm_apply _

theorem euclideanProjectionMatrix_isStarProjection
    (U : Submodule ℝ (EuclideanSpace ℝ ι)) :
    IsStarProjection (euclideanProjectionMatrix U) := by
  rw [isStarProjection_iff']
  constructor
  · have h := congrArg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).symm
      U.isIdempotentElem_starProjection.eq
    simpa only [map_mul, euclideanProjectionMatrix] using h
  · have h := congrArg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).symm
      (isSelfAdjoint_starProjection U).star_eq
    simpa only [map_star, euclideanProjectionMatrix] using h

theorem euclideanProjectionMatrix_posSemidef
    (U : Submodule ℝ (EuclideanSpace ℝ ι)) :
    (euclideanProjectionMatrix U).PosSemidef :=
  (euclideanProjectionMatrix_isStarProjection U).nonneg.posSemidef

theorem euclideanProjectionMatrix_le_one
    (U : Submodule ℝ (EuclideanSpace ℝ ι)) :
    euclideanProjectionMatrix U ≤ 1 :=
  (euclideanProjectionMatrix_isStarProjection U).le_one

theorem euclideanProjectionMatrix_trace
    (U : Submodule ℝ (EuclideanSpace ℝ ι)) :
    realTrace (euclideanProjectionMatrix U) = (Module.finrank ℝ U : ℝ) := by
  have ht (A : Matrix ι ι ℝ) :
      LinearMap.trace ℝ (EuclideanSpace ℝ ι)
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A).toLinearMap = realTrace A := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
      Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]
    rfl
  rw [← ht, toEuclideanCLM_projectionMatrix]
  apply LinearMap.IsProj.trace
  exact ⟨U.starProjection_apply_mem, fun x hx => U.starProjection_eq_self_iff.mpr hx⟩

theorem euclideanProjectionMatrix_orthogonal
    (U : Submodule ℝ (EuclideanSpace ℝ ι)) :
    euclideanProjectionMatrix Uᗮ = 1 - euclideanProjectionMatrix U := by
  have h := congrArg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).symm
    U.starProjection_orthogonal'
  simpa only [map_sub, map_one, euclideanProjectionMatrix] using h

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The allowed preimages under the square root, including its kernel. -/
noncomputable def ownerShortSubspace (C : Matrix ι ι ℝ)
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] E) : Submodule ℝ (EuclideanSpace ℝ ι) :=
  LinearMap.ker (T.comp
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (CFC.sqrt C)).toLinearMap)

/-- The short used for frozen-coordinate and radial constraints. -/
noncomputable def ownerShort (C : Matrix ι ι ℝ)
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] E) : Matrix ι ι ℝ :=
  ownerCompression C (euclideanProjectionMatrix (ownerShortSubspace C T))

theorem ownerShort_posSemidef (C : Matrix ι ι ℝ)
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] E) : (ownerShort C T).PosSemidef :=
  ownerCompression_posSemidef C (euclideanProjectionMatrix_posSemidef _)

theorem ownerShort_le {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] E) : ownerShort C T ≤ C :=
  ownerCompression_le hC (euclideanProjectionMatrix_le_one _)

/-- Every movement produced by the short obeys all constraints encoded in `T`. -/
theorem ownerShort_constraint (C : Matrix ι ι ℝ)
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] E) (x : EuclideanSpace ℝ ι) :
    T (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (ownerShort C T) x) = 0 := by
  have h := (ownerShortSubspace C T).starProjection_apply_mem
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (CFC.sqrt C) x)
  change T ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (CFC.sqrt C))
    ((ownerShortSubspace C T).starProjection
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (CFC.sqrt C) x))) = 0 at h
  unfold ownerShort ownerCompression
  rw [map_mul, map_mul]
  change T ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (CFC.sqrt C))
    ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
      (euclideanProjectionMatrix (ownerShortSubspace C T)))
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (CFC.sqrt C) x))) = 0
  rw [toEuclideanCLM_projectionMatrix]
  exact h

theorem ownerShort_range_le_ker (C : Matrix ι ι ℝ)
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] E) :
    LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
      (ownerShort C T)).toLinearMap ≤ LinearMap.ker T := by
  rintro _ ⟨x, rfl⟩
  exact ownerShort_constraint C T x

theorem ownerShortSubspace_codim_le [FiniteDimensional ℝ E]
    (C : Matrix ι ι ℝ) (T : EuclideanSpace ℝ ι →ₗ[ℝ] E) :
    Module.finrank ℝ (ownerShortSubspace C T)ᗮ ≤ Module.finrank ℝ (LinearMap.range T) := by
  have hn := (T.comp
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (CFC.sqrt C)).toLinearMap).finrank_range_add_finrank_ker
  have ho := (ownerShortSubspace C T).finrank_add_finrank_orthogonal
  have hr : Module.finrank ℝ (LinearMap.range (T.comp
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (CFC.sqrt C)).toLinearMap)) ≤
      Module.finrank ℝ (LinearMap.range T) :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (CFC.sqrt C)).toLinearMap T)
  change Module.finrank ℝ (LinearMap.range (T.comp
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (CFC.sqrt C)).toLinearMap)) +
    Module.finrank ℝ (ownerShortSubspace C T) = _ at hn
  omega

/-- Shorting loses at most one unit of trace per independent linear constraint. -/
theorem ownerShort_trace_loss [FiniteDimensional ℝ E]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] E) :
    realTrace (C - ownerShort C T) ≤ (Module.finrank ℝ (LinearMap.range T) : ℝ) := by
  calc
    realTrace (C - ownerShort C T) ≤
        realTrace (1 - euclideanProjectionMatrix (ownerShortSubspace C T)) :=
      ownerCompression_trace_loss hC hC1 (euclideanProjectionMatrix_le_one _)
    _ = (Module.finrank ℝ (ownerShortSubspace C T)ᗮ : ℝ) := by
      rw [← euclideanProjectionMatrix_orthogonal, euclideanProjectionMatrix_trace]
    _ ≤ (Module.finrank ℝ (LinearMap.range T) : ℝ) := by
      exact_mod_cast ownerShortSubspace_codim_le C T

theorem ownerShort_trace_lower [FiniteDimensional ℝ E]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] E) :
    realTrace C - (Module.finrank ℝ (LinearMap.range T) : ℝ) ≤
      realTrace (ownerShort C T) := by
  have h := ownerShort_trace_loss hC hC1 T
  rw [realTrace_sub] at h
  linarith

theorem ownerShort_trace_loss_le_dim [FiniteDimensional ℝ E]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] E) :
    realTrace (C - ownerShort C T) ≤ (Module.finrank ℝ E : ℝ) := by
  exact (ownerShort_trace_loss hC hC1 T).trans
    (by exact_mod_cast (LinearMap.range T).finrank_le)

/-- The original subspace formulation follows by recording its orthogonal projection. -/
theorem exists_ownerShort_subspace {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) (hC1 : C ≤ 1)
    (V : Submodule ℝ (EuclideanSpace ℝ ι)) :
    ∃ Q : Matrix ι ι ℝ, Q.PosSemidef ∧ Q ≤ C ∧
      LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) Q).toLinearMap ≤ V ∧
      realTrace (C - Q) ≤ (Module.finrank ℝ Vᗮ : ℝ) := by
  refine ⟨ownerShort C Vᗮ.starProjection.toLinearMap, ownerShort_posSemidef _ _,
    ownerShort_le hC _, ?_, ?_⟩
  · have hk : LinearMap.ker Vᗮ.starProjection.toLinearMap = V :=
      (Submodule.ker_starProjection Vᗮ).trans V.orthogonal_orthogonal
    exact (ownerShort_range_le_ker C Vᗮ.starProjection.toLinearMap).trans_eq hk
  · have hr : LinearMap.range Vᗮ.starProjection.toLinearMap = Vᗮ :=
      Submodule.range_starProjection Vᗮ
    have h := ownerShort_trace_loss hC hC1 Vᗮ.starProjection.toLinearMap
    rwa [hr] at h

/-- A natural-number trace budget with codimension written as a dimension difference. -/
theorem exists_ownerShort_codim {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) (hC1 : C ≤ 1)
    (V : Submodule ℝ (EuclideanSpace ℝ ι)) :
    ∃ Q : Matrix ι ι ℝ, Q.PosSemidef ∧ Q ≤ C ∧
      LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) Q).toLinearMap ≤ V ∧
      realTrace (C - Q) ≤
        ((Module.finrank ℝ (EuclideanSpace ℝ ι) - Module.finrank ℝ V : ℕ) : ℝ) := by
  have hd : Module.finrank ℝ Vᗮ =
      Module.finrank ℝ (EuclideanSpace ℝ ι) - Module.finrank ℝ V := by
    have h := V.finrank_add_finrank_orthogonal
    omega
  simpa only [hd] using exists_ownerShort_subspace hC hC1 V

end MatrixSpencer
