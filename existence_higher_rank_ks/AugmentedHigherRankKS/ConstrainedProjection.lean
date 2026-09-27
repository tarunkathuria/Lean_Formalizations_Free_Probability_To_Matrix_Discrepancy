import MatrixSpencer.KSWeightedProjection

/-! The legal-pair projection with one additional scalar constraint on its
second component. The constraint costs at most one unit of trace. -/

open Matrix MatrixSpencer MatrixSpencer.KSWeightedProjection
open scoped BigOperators MatrixOrder

noncomputable section
namespace AugmentedHigherRankKS.ConstrainedProjection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def constraint (E F : Matrix ι ι ℝ) (z : ι → ℝ) :
    Matrix (ι ⊕ Unit) (ι ⊕ ι) ℝ :=
  Sum.elim (constraintMatrix E F) (fun _ => Sum.elim (fun _ => 0) z)

def constraintLin (E F : Matrix ι ι ℝ) (z : ι → ℝ) :
    EuclideanSpace ℝ (ι ⊕ ι) →ₗ[ℝ] EuclideanSpace ℝ (ι ⊕ Unit) :=
  Matrix.toEuclideanLin (constraint E F z)

def projection (E F : Matrix ι ι ℝ) (z : ι → ℝ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  euclideanProjectionMatrix (LinearMap.ker (constraintLin E F z))

theorem isStarProjection (E F : Matrix ι ι ℝ) (z : ι → ℝ) :
    IsStarProjection (projection E F z) :=
  euclideanProjectionMatrix_isStarProjection _

theorem trace_lower (E F : Matrix ι ι ℝ) (z : ι → ℝ) :
    (Fintype.card ι : ℝ) - 1 ≤ realTrace (projection E F z) := by
  rw [projection, euclideanProjectionMatrix_trace]
  have h := (constraintLin E F z).finrank_range_add_finrank_ker
  have hb := (LinearMap.range (constraintLin E F z)).finrank_le
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (ι ⊕ ι)) = 2 * Fintype.card ι := by
    simp [Fintype.card_sum, two_mul]
  have hc : Module.finrank ℝ (EuclideanSpace ℝ (ι ⊕ Unit)) = Fintype.card ι + 1 := by
    simp
  rw [hd] at h
  rw [hc] at hb
  have hn : Fintype.card ι ≤
      Module.finrank ℝ (LinearMap.ker (constraintLin E F z)) + 1 := by omega
  have hr : (Fintype.card ι : ℝ) ≤
      (Module.finrank ℝ (LinearMap.ker (constraintLin E F z)) : ℝ) + 1 := by
    exact_mod_cast hn
  linarith

theorem constraint_mul (E F : Matrix ι ι ℝ) (z : ι → ℝ) :
    constraint E F z * projection E F z = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
  have h := (LinearMap.ker (constraintLin E F z)).starProjection_apply_mem
    (WithLp.toLp 2 (Pi.single j 1))
  change constraintLin E F z
    ((LinearMap.ker (constraintLin E F z)).starProjection
      (WithLp.toLp 2 (Pi.single j 1))) = 0 at h
  rw [← toEuclideanCLM_projectionMatrix] at h
  have he := congrArg WithLp.ofLp h
  simpa only [constraintLin, projection, Matrix.ofLp_toEuclideanLin_apply,
    Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, WithLp.ofLp_zero,
    WithLp.ofLp_toLp] using he

theorem legal (E F : Matrix ι ι ℝ) (z : ι → ℝ) :
    (topProjection - rowPerturbation E F) * projection E F z = 0 := by
  ext (i | i) j
  · have h := congrArg (fun A => A (Sum.inl i) j) (constraint_mul E F z)
    simpa [Matrix.mul_apply, constraint, topProjection, rowPerturbation,
      constraintMatrix, Fintype.sum_sum_type] using h
  · simp [Matrix.mul_apply, topProjection, rowPerturbation, Fintype.sum_sum_type]

theorem scalar_constraint (E F : Matrix ι ι ℝ) (z : ι → ℝ) (j : ι ⊕ ι) :
    ∑ i, z i * projection E F z (Sum.inr i) j = 0 := by
  have h := congrArg (fun A => A (Sum.inr ()) j) (constraint_mul E F z)
  simpa [Matrix.mul_apply, constraint, Fintype.sum_sum_type] using h

theorem estimates (E F : Matrix ι ι ℝ) (z : ι → ℝ) :
    let P := projection E F z
    let W := topProjection (ι := ι)
    let α := hsSq E + hsSq F
    realTrace (W * P) ≤ α ∧
    realTrace ((1 - W) * (1 - P)) ≤ 1 + α ∧
    hsSq (W * P * (1 - W)) ≤ α ∧
    hsSq ((1 - W) * (1 - P) * (1 - W)) ≤ 1 + α := by
  dsimp only
  have hp := isStarProjection E F z
  have hw := topProjection_isStarProjection (ι := ι)
  have htop : realTrace (topProjection * projection E F z) ≤ hsSq E + hsSq F := by
    simpa only [hsSq_rowPerturbation] using
      trace_projection_le_perturbation hw hp (legal E F z)
  have hrank := trace_lower E F z
  have hbottom : realTrace ((1 - topProjection) * (1 - projection E F z)) ≤
      1 + realTrace (topProjection * projection E F z) := by
    have ht := realTrace_one_sub_topProjection (ι := ι)
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      realTrace_sub] at ht ⊢
    linarith
  exact ⟨htop, hbottom.trans (by linarith),
    (cross_hsSq_le hw hp).trans htop,
    (complementary_hsSq_le hw hp).trans (hbottom.trans (by linarith))⟩

theorem block_estimates (E F : Matrix ι ι ℝ) (z : ι → ℝ) :
    let P := projection E F z
    let α := hsSq E + hsSq F
    realTrace P.toBlocks₁₁ ≤ α ∧
    realTrace (1 - P.toBlocks₂₂) ≤ 1 + α ∧
    hsSq P.toBlocks₁₂ ≤ α ∧
    hsSq (1 - P.toBlocks₂₂) ≤ 1 + α := by
  have h := estimates E F z
  dsimp only at h ⊢
  have hp := Matrix.fromBlocks_toBlocks (projection E F z)
  rw [← hp, one_sub_topProjection] at h
  simpa [topProjection, one_sub_fromBlocks, Matrix.fromBlocks_multiply,
    realTrace_fromBlocks, hsSq_fromBlocks] using h

end AugmentedHigherRankKS.ConstrainedProjection
