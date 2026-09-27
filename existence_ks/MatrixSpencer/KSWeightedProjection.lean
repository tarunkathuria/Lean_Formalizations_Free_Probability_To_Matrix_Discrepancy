import MatrixSpencer.OwnerShort

/-!
# The joint projection estimate for the full-cube Kadison–Singer proof

The estimates use an actual orthogonal projection and its exact linear
constraint. No invertibility, spectral gap, or operator-norm smallness of
the perturbation is assumed.
-/

open Matrix
open scoped BigOperators MatrixOrder

noncomputable section
namespace MatrixSpencer
namespace KSWeightedProjection

variable {ι : Type*} [Fintype ι]

/-- Squared Hilbert–Schmidt norm, independent of the ambient matrix norm instance. -/
def hsSq (A : Matrix ι ι ℝ) : ℝ := realTrace (Aᵀ * A)

@[simp] theorem hsSq_zero : hsSq (0 : Matrix ι ι ℝ) = 0 := by simp [hsSq]

theorem hsSq_nonneg (A : Matrix ι ι ℝ) : 0 ≤ hsSq A := by
  simpa only [hsSq, Matrix.conjTranspose_eq_transpose_of_trivial] using
    realTrace_conjTranspose_mul_self_nonneg A

theorem hsSq_transpose (A : Matrix ι ι ℝ) : hsSq Aᵀ = hsSq A := by
  simpa only [hsSq, Matrix.transpose_transpose] using realTrace_mul_comm A Aᵀ

theorem projection_transpose {P : Matrix ι ι ℝ} (hP : IsStarProjection P) : Pᵀ = P := by
  simpa only [star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hP.isSelfAdjoint.star_eq

theorem projection_mul_self {P : Matrix ι ι ℝ} (hP : IsStarProjection P) : P * P = P :=
  hP.isIdempotentElem.eq

variable [DecidableEq ι]

/-- Multiplication on the right by an orthogonal projection contracts squared HS norm. -/
theorem hsSq_mul_projection_le (A : Matrix ι ι ℝ) {P : Matrix ι ι ℝ}
    (hP : IsStarProjection P) : hsSq (A * P) ≤ hsSq A := by
  have ht := realTrace_mul_mono (Matrix.posSemidef_conjTranspose_mul_self A) hP.le_one
  have hp := projection_transpose hP
  have hpp := projection_mul_self hP
  have he : realTrace ((A * P)ᵀ * (A * P)) = realTrace ((Aᵀ * A) * P) := by
    rw [Matrix.transpose_mul, hp]
    calc
      realTrace (P * Aᵀ * (A * P)) = realTrace ((Aᵀ * A) * P * P) := by
        simpa only [Matrix.mul_assoc] using realTrace_mul_comm P (Aᵀ * A * P)
      _ = realTrace ((Aᵀ * A) * P) := by rw [Matrix.mul_assoc, hpp]
  rw [hsSq, he]
  simpa only [hsSq, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_one] using ht

/-- Multiplication on the left by an orthogonal projection contracts squared HS norm. -/
theorem hsSq_projection_mul_le (A : Matrix ι ι ℝ) {P : Matrix ι ι ℝ}
    (hP : IsStarProjection P) : hsSq (P * A) ≤ hsSq A := by
  have h := hsSq_mul_projection_le Aᵀ hP
  rw [← hsSq_transpose (P * A), Matrix.transpose_mul, projection_transpose hP]
  simpa only [hsSq_transpose] using h

omit [DecidableEq ι] in
/-- Two projections pair to the squared HS norm of their product. -/
theorem hsSq_projection_mul_projection {P Q : Matrix ι ι ℝ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    hsSq (P * Q) = realTrace (P * Q) := by
  rw [hsSq, Matrix.transpose_mul, projection_transpose hP, projection_transpose hQ]
  calc
    realTrace (Q * P * (P * Q)) = realTrace (P * P * Q * Q) := by
      simpa only [Matrix.mul_assoc] using realTrace_mul_comm Q (P * P * Q)
    _ = realTrace (P * Q) := by rw [projection_mul_self hP, Matrix.mul_assoc,
      projection_mul_self hQ]

/-- The top-block trace is paid by the squared HS perturbation in the legal equation. -/
theorem trace_projection_le_perturbation {W P D : Matrix ι ι ℝ}
    (hW : IsStarProjection W) (hP : IsStarProjection P)
    (hlegal : (W - D) * P = 0) : realTrace (W * P) ≤ hsSq D := by
  have he : W * P = D * P := by
    rw [Matrix.sub_mul, sub_eq_zero] at hlegal
    exact hlegal
  rw [← hsSq_projection_mul_projection hW hP, he]
  exact hsSq_mul_projection_le D hP

/-- Trace loss from the complementary baseline is bounded by top-block trace
whenever the actual projection has at least the baseline rank. -/
theorem complementary_trace_loss_le {W P : Matrix ι ι ℝ}
    (hrank : realTrace (1 - W) ≤ realTrace P) :
    realTrace ((1 - W) * (1 - P)) ≤ realTrace (W * P) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    realTrace_sub] at *
  linarith

/-- The off-diagonal block has squared HS norm at most the top-block trace. -/
theorem cross_hsSq_le {W P : Matrix ι ι ℝ}
    (hW : IsStarProjection W) (hP : IsStarProjection P) :
    hsSq (W * P * (1 - W)) ≤ realTrace (W * P) := by
  calc
    hsSq (W * P * (1 - W)) ≤ hsSq (W * P) :=
      hsSq_mul_projection_le _ hW.one_sub
    _ = realTrace (W * P) := hsSq_projection_mul_projection hW hP

/-- The complementary diagonal defect has squared HS norm at most its trace. -/
theorem complementary_hsSq_le {W P : Matrix ι ι ℝ}
    (hW : IsStarProjection W) (hP : IsStarProjection P) :
    hsSq ((1 - W) * (1 - P) * (1 - W)) ≤ realTrace ((1 - W) * (1 - P)) := by
  calc
    hsSq ((1 - W) * (1 - P) * (1 - W)) ≤ hsSq ((1 - W) * (1 - P)) :=
      hsSq_mul_projection_le _ hW.one_sub
    _ = realTrace ((1 - W) * (1 - P)) :=
      hsSq_projection_mul_projection hW.one_sub hP.one_sub


theorem joint_projection_estimates {W P D : Matrix ι ι ℝ}
    (hW : IsStarProjection W) (hP : IsStarProjection P)
    (hlegal : (W - D) * P = 0)
    (hrank : realTrace (1 - W) ≤ realTrace P) :
    realTrace (W * P) ≤ hsSq D ∧
    realTrace ((1 - W) * (1 - P)) ≤ hsSq D ∧
    hsSq (W * P * (1 - W)) ≤ hsSq D ∧
    hsSq ((1 - W) * (1 - P) * (1 - W)) ≤ hsSq D := by
  have htop := trace_projection_le_perturbation hW hP hlegal
  have hbottom := (complementary_trace_loss_le hrank).trans htop
  exact ⟨htop, hbottom, (cross_hsSq_le hW hP).trans htop,
    (complementary_hsSq_le hW hP).trans hbottom⟩

/-- The upper coordinate projection in the order `(w,v)`. -/
def topProjection : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks 1 0 0 0

/-- The perturbation of `[I,0]` by `[E,F]`, padded by a zero lower row. -/
def rowPerturbation (E F : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks E F 0 0

theorem topProjection_isStarProjection : IsStarProjection (topProjection (ι := ι)) := by
  rw [isStarProjection_iff']
  constructor
  · simp [topProjection, Matrix.fromBlocks_multiply]
  · ext (i | i) (j | j) <;> simp [topProjection, Matrix.one_apply, eq_comm]

omit [DecidableEq ι] in
theorem realTrace_fromBlocks (A B C D : Matrix ι ι ℝ) :
    realTrace (Matrix.fromBlocks A B C D) = realTrace A + realTrace D := by
  simp [realTrace, Matrix.trace, Fintype.sum_sum_type]

omit [DecidableEq ι] in
theorem hsSq_rowPerturbation (E F : Matrix ι ι ℝ) :
    hsSq (rowPerturbation E F) = hsSq E + hsSq F := by
  simp [hsSq, rowPerturbation, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    realTrace_fromBlocks]

/-- The actual rectangular constraint matrix `[I-E,-F]`. -/
def constraintMatrix (E F : Matrix ι ι ℝ) : Matrix ι (ι ⊕ ι) ℝ :=
  fun i j => Sum.elim ((1 - E) i) ((-F) i) j

def constraintMap (E F : Matrix ι ι ℝ) :
    EuclideanSpace ℝ (ι ⊕ ι) →ₗ[ℝ] EuclideanSpace ℝ ι :=
  Matrix.toEuclideanLin (constraintMatrix E F)

def kernelProjection (E F : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  euclideanProjectionMatrix (LinearMap.ker (constraintMap E F))

theorem kernelProjection_isStarProjection (E F : Matrix ι ι ℝ) :
    IsStarProjection (kernelProjection E F) :=
  euclideanProjectionMatrix_isStarProjection _

theorem kernelProjection_trace_lower (E F : Matrix ι ι ℝ) :
    (Fintype.card ι : ℝ) ≤ realTrace (kernelProjection E F) := by
  rw [kernelProjection, euclideanProjectionMatrix_trace]
  have h := (constraintMap E F).finrank_range_add_finrank_ker
  have hb := (LinearMap.range (constraintMap E F)).finrank_le
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (ι ⊕ ι)) = 2 * Fintype.card ι := by
    simp [Fintype.card_sum, two_mul]
  have hc : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := by simp
  rw [hd] at h
  rw [hc] at hb
  exact_mod_cast (show Fintype.card ι ≤ Module.finrank ℝ
    (LinearMap.ker (constraintMap E F)) by omega)

theorem kernelProjection_constraint (E F : Matrix ι ι ℝ) :
    constraintMatrix E F * kernelProjection E F = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
  have h := (LinearMap.ker (constraintMap E F)).starProjection_apply_mem
    (WithLp.toLp 2 (Pi.single j 1))
  change constraintMap E F
    ((LinearMap.ker (constraintMap E F)).starProjection
      (WithLp.toLp 2 (Pi.single j 1))) = 0 at h
  rw [← toEuclideanCLM_projectionMatrix] at h
  have he := congrArg WithLp.ofLp h
  simpa only [constraintMap, kernelProjection, Matrix.ofLp_toEuclideanLin_apply,
    Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, WithLp.ofLp_zero,
    WithLp.ofLp_toLp] using he

theorem kernelProjection_legal (E F : Matrix ι ι ℝ) :
    (topProjection - rowPerturbation E F) * kernelProjection E F = 0 := by
  ext (i | i) j
  · have h := congrArg (fun A => A i j) (kernelProjection_constraint E F)
    simpa [Matrix.mul_apply, topProjection, rowPerturbation, constraintMatrix,
      Fintype.sum_sum_type] using h
  · simp [Matrix.mul_apply, topProjection, rowPerturbation, Fintype.sum_sum_type]

omit [Fintype ι] in
theorem one_sub_topProjection : (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) - topProjection =
    Matrix.fromBlocks 0 0 0 1 := by
  ext (i | i) (j | j) <;> simp [topProjection, Matrix.one_apply]

theorem realTrace_one_sub_topProjection :
    realTrace ((1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) - topProjection) =
      (Fintype.card ι : ℝ) := by
  rw [one_sub_topProjection, realTrace_fromBlocks]
  simp [realTrace, Matrix.trace]

/-- The actual joint kernel projection satisfies all four gap-free bounds. -/
theorem kernel_projection_estimates (E F : Matrix ι ι ℝ) :
    let P := kernelProjection E F
    let W := topProjection (ι := ι)
    let α := hsSq E + hsSq F
    realTrace (W * P) ≤ α ∧
    realTrace ((1 - W) * (1 - P)) ≤ α ∧
    hsSq (W * P * (1 - W)) ≤ α ∧
    hsSq ((1 - W) * (1 - P) * (1 - W)) ≤ α := by
  have hrank : realTrace ((1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) - topProjection) ≤
      realTrace (kernelProjection E F) := by
    rw [realTrace_one_sub_topProjection]
    exact kernelProjection_trace_lower E F
  simpa only [hsSq_rowPerturbation] using joint_projection_estimates
    topProjection_isStarProjection (kernelProjection_isStarProjection E F)
    (kernelProjection_legal E F) hrank

omit [DecidableEq ι] in
theorem hsSq_fromBlocks (A B C D : Matrix ι ι ℝ) :
    hsSq (Matrix.fromBlocks A B C D) = hsSq A + hsSq B + hsSq C + hsSq D := by
  simp only [hsSq, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    realTrace_fromBlocks, realTrace_add]
  ring

omit [Fintype ι] in
theorem one_sub_fromBlocks (A B C D : Matrix ι ι ℝ) :
    (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) - Matrix.fromBlocks A B C D =
      Matrix.fromBlocks (1 - A) (-B) (-C) (1 - D) := by
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]


theorem kernel_projection_block_estimates (E F : Matrix ι ι ℝ) :
    let P := kernelProjection E F
    let α := hsSq E + hsSq F
    realTrace P.toBlocks₁₁ ≤ α ∧
    realTrace (1 - P.toBlocks₂₂) ≤ α ∧
    hsSq P.toBlocks₁₂ ≤ α ∧
    hsSq (1 - P.toBlocks₂₂) ≤ α := by
  have h := kernel_projection_estimates E F
  dsimp only at h ⊢
  have hp := Matrix.fromBlocks_toBlocks (kernelProjection E F)
  rw [← hp, one_sub_topProjection] at h
  simpa [topProjection, one_sub_fromBlocks, Matrix.fromBlocks_multiply,
    realTrace_fromBlocks, hsSq_fromBlocks] using h

end KSWeightedProjection
end MatrixSpencer
