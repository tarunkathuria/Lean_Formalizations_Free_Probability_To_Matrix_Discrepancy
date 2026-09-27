import MatrixSpencer.CovarianceSupport

/-!
# Coordinates on coefficient covariance faces

The rectangular mixing identity preserves the actual source. The mixed family
is not assumed to consist of contractions. Its coordinate dimension does not
replace the number of original retained labels in any discrepancy budget.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MatrixSpencer

noncomputable section

variable {ι κ n : Type*} [Fintype ι] [Fintype κ] [Fintype n]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq n]

/-- Rectangular real mixing of the original physical matrix family. -/
def mixFamily (A : ι → Matrix n n ℂ) (U : Matrix ι κ ℝ) (a : κ) : Matrix n n ℂ :=
  ∑ i, U i a • A i

omit [Fintype κ] [Fintype n] [DecidableEq ι] [DecidableEq κ] [DecidableEq n] in
theorem mixFamily_isHermitian (A : ι → Matrix n n ℂ) (U : Matrix ι κ ℝ)
    (hA : ∀ i, (A i).IsHermitian) (a : κ) : (mixFamily A U a).IsHermitian := by
  unfold mixFamily Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.conjTranspose_smul, star_trivial, (hA i).eq]

/-- The actual covariance in ambient retained-label coordinates. -/
def covarianceLift (U : Matrix ι κ ℝ) (K : Matrix κ κ ℝ) : Matrix ι ι ℝ := U * K * Uᵀ

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq n] in
theorem covarianceSource_rectangular_mixing (A : ι → Matrix n n ℂ) (U : Matrix ι κ ℝ)
    (K : Matrix κ κ ℝ) (S : Matrix n n ℂ) :
    covarianceSource A (covarianceLift U K) S = covarianceSource (mixFamily A U) K S := by
  simp only [covarianceSource, covarianceLift, mixFamily, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul, Finset.sum_mul]
  calc
    _ = ∑ i, ∑ j, ∑ a, ∑ b, (U i a * K a b * U j b) • (A i * S * A j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ j, ∑ b, (U i a * K a b * U j b) • (A i * S * A j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, ∑ b, (U i a * K a b * U j b) • (A i * S * A j) :=
      Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ j, (U i a * K a b * U j b) • (A i * S * A j) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i, ∑ j, (U i a * K a b * U j b) • (A i * S * A j) := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem covarianceLift_posSemidef (U : Matrix ι κ ℝ) {K : Matrix κ κ ℝ}
    (hK : K.PosSemidef) : (covarianceLift U K).PosSemidef := by
  simpa only [covarianceLift, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hK.mul_mul_conjTranspose_same U

omit [DecidableEq ι] in
theorem covarianceLift_compress (U : Matrix ι κ ℝ) (hU : Uᵀ * U = 1)
    (K : Matrix κ κ ℝ) : Uᵀ * covarianceLift U K * U = K := by
  simp only [covarianceLift, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [Matrix.mul_assoc, hU, Matrix.mul_one]

omit [DecidableEq ι] in
theorem covarianceLift_posSemidef_iff (U : Matrix ι κ ℝ) (hU : Uᵀ * U = 1)
    (K : Matrix κ κ ℝ) : (covarianceLift U K).PosSemidef ↔ K.PosSemidef := by
  constructor
  · intro h
    have hc := h.conjTranspose_mul_mul_same U
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, covarianceLift_compress U hU] using hc
  · exact covarianceLift_posSemidef U

omit [DecidableEq ι] [DecidableEq κ] in
theorem covarianceLift_mono (U : Matrix ι κ ℝ) {K L : Matrix κ κ ℝ} (hKL : K ≤ L) :
    covarianceLift U K ≤ covarianceLift U L := by
  have hp := covarianceLift_posSemidef U (sub_nonneg.mpr hKL).posSemidef
  simpa only [covarianceLift, Matrix.mul_sub, Matrix.sub_mul, sub_nonneg] using hp.nonneg

theorem covarianceIsometry_projection_le_one (U : Matrix ι κ ℝ) (hU : Uᵀ * U = 1) :
    U * Uᵀ ≤ (1 : Matrix ι ι ℝ) := by
  have hp := Matrix.posSemidef_conjTranspose_mul_self (1 - U * Uᵀ)
  have he : (1 - U * Uᵀ)ᴴ * (1 - U * Uᵀ) = 1 - U * Uᵀ := by
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_assoc U Uᵀ (U * Uᵀ), ← Matrix.mul_assoc Uᵀ U Uᵀ, hU,
      Matrix.one_mul]
    abel
  rw [he] at hp
  exact sub_nonneg.mp hp.nonneg

theorem covarianceLift_le_one (U : Matrix ι κ ℝ) (hU : Uᵀ * U = 1)
    {K : Matrix κ κ ℝ} (hK : K ≤ (1 : Matrix κ κ ℝ)) :
    covarianceLift U K ≤ (1 : Matrix ι ι ℝ) := by
  calc
    _ ≤ covarianceLift U (1 : Matrix κ κ ℝ) := covarianceLift_mono U hK
    _ = U * Uᵀ := by simp [covarianceLift]
    _ ≤ _ := covarianceIsometry_projection_le_one U hU

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- A supported rank-one shave has exactly the corresponding reduced coordinates. -/
theorem covarianceLift_shave (U : Matrix ι κ ℝ) (K : Matrix κ κ ℝ) (v : κ → ℝ) (h : ℝ) :
    covarianceLift U (K - h • Matrix.vecMulVec v v) =
      covarianceLift U K - h • Matrix.vecMulVec (U *ᵥ v) (U *ᵥ v) := by
  simp only [covarianceLift, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

theorem covarianceLift_le_one_iff (U : Matrix ι κ ℝ) (hU : Uᵀ * U = 1)
    (K : Matrix κ κ ℝ) :
    covarianceLift U K ≤ (1 : Matrix ι ι ℝ) ↔ K ≤ (1 : Matrix κ κ ℝ) := by
  constructor
  · intro h
    have hp := (sub_nonneg.mpr h).posSemidef.conjTranspose_mul_mul_same U
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, covarianceLift_compress U hU, hU] at hp
    exact sub_nonneg.mp hp.nonneg
  · exact covarianceLift_le_one U hU

omit [DecidableEq ι] in
theorem covarianceIsometry_mulVec_injective (U : Matrix ι κ ℝ) (hU : Uᵀ * U = 1) :
    Function.Injective U.mulVec := by
  intro x y h
  have hh := congrArg Uᵀ.mulVec h
  simpa only [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec] using hh

omit [DecidableEq ι] in
/-- A positive definite reduced matrix has exactly the range specified by its embedding. -/
theorem covarianceLift_range_of_posDef (U : Matrix ι κ ℝ) (hU : Uᵀ * U = 1)
    {K : Matrix κ κ ℝ} (hK : K.PosDef) :
    LinearMap.range (covarianceLift U K).mulVecLin = LinearMap.range U.mulVecLin := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨K *ᵥ (Uᵀ *ᵥ y), ?_⟩
    simp only [Matrix.mulVecLin_apply, covarianceLift, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · rintro ⟨z, rfl⟩
    refine ⟨U *ᵥ (K⁻¹ *ᵥ z), ?_⟩
    change covarianceLift U K *ᵥ (U *ᵥ (K⁻¹ *ᵥ z)) = U *ᵥ z
    calc
      _ = (U * K * (Uᵀ * U) * K⁻¹) *ᵥ z := by
        simp only [covarianceLift, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = _ := by
        rw [hU, Matrix.mul_one, Matrix.mul_assoc,
          Matrix.mul_nonsing_inv K ((Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit), Matrix.mul_one]

/-- The positive spectral coordinates are the constructed range coordinates of a PSD covariance. -/
abbrev covarianceRangeIndex (C : Matrix ι ι ℝ) (hC : C.PosSemidef) :=
  {i : ι // 0 < hC.isHermitian.eigenvalues i}

/-- Columns are precisely the positive-eigenvalue orthonormal eigenvectors. -/
def covarianceRangeEmbedding (C : Matrix ι ι ℝ) (hC : C.PosSemidef) :
    Matrix ι (covarianceRangeIndex C hC) ℝ :=
  fun i j => (hC.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) i j.val

/-- The actual faithful matrix on the constructed range, including the empty range. -/
def covarianceRangeMatrix (C : Matrix ι ι ℝ) (hC : C.PosSemidef) :
    Matrix (covarianceRangeIndex C hC) (covarianceRangeIndex C hC) ℝ :=
  Matrix.diagonal (fun i => hC.isHermitian.eigenvalues i.val)

theorem covarianceRangeEmbedding_isometry (C : Matrix ι ι ℝ) (hC : C.PosSemidef) :
    (covarianceRangeEmbedding C hC)ᵀ * covarianceRangeEmbedding C hC = 1 := by
  have hu : (hC.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ)ᵀ *
      (hC.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) = 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      unitary.coe_star_mul_self hC.isHermitian.eigenvectorUnitary
  ext i j
  have he := congrArg (fun M : Matrix ι ι ℝ => M i.val j.val) hu
  by_cases hij : i = j
  · subst j
    simpa only [covarianceRangeEmbedding, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.one_apply, if_pos rfl] using he
  · have hv : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    simpa only [covarianceRangeEmbedding, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.one_apply, if_neg hij, if_neg hv] using he

theorem covarianceRangeMatrix_posDef (C : Matrix ι ι ℝ) (hC : C.PosSemidef) :
    (covarianceRangeMatrix C hC).PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  exact i.property

theorem covarianceRange_reconstruct (C : Matrix ι ι ℝ) (hC : C.PosSemidef) :
    covarianceLift (covarianceRangeEmbedding C hC) (covarianceRangeMatrix C hC) = C := by
  classical
  conv_rhs => rw [hC.isHermitian.spectral_theorem]
  change covarianceRangeEmbedding C hC * covarianceRangeMatrix C hC *
      (covarianceRangeEmbedding C hC)ᵀ =
    (hC.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) * Matrix.diagonal hC.isHermitian.eigenvalues *
      (hC.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ)ᵀ
  unfold covarianceRangeMatrix
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, covarianceRangeEmbedding, Matrix.transpose_apply]
  symm
  apply Finset.sum_congr_set {a : ι | 0 < hC.isHermitian.eigenvalues a}
  · intro a ha
    rfl
  · intro a ha
    have hz : hC.isHermitian.eigenvalues a = 0 :=
      le_antisymm (le_of_not_gt ha) (hC.eigenvalues_nonneg a)
    simp only [hz, mul_zero, zero_mul]

theorem covarianceRange_compress (C : Matrix ι ι ℝ) (hC : C.PosSemidef) :
    (covarianceRangeEmbedding C hC)ᵀ * C * covarianceRangeEmbedding C hC =
      covarianceRangeMatrix C hC := by
  have h := covarianceLift_compress (covarianceRangeEmbedding C hC)
    (covarianceRangeEmbedding_isometry C hC) (covarianceRangeMatrix C hC)
  simpa only [covarianceRange_reconstruct] using h

theorem covarianceRange_range (C : Matrix ι ι ℝ) (hC : C.PosSemidef) :
    LinearMap.range C.mulVecLin = LinearMap.range (covarianceRangeEmbedding C hC).mulVecLin := by
  have h := covarianceLift_range_of_posDef (covarianceRangeEmbedding C hC)
    (covarianceRangeEmbedding_isometry C hC) (covarianceRangeMatrix_posDef C hC)
  simpa only [covarianceRange_reconstruct] using h

theorem covarianceRangeMatrix_le_one (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (hcap : C ≤ (1 : Matrix ι ι ℝ)) : covarianceRangeMatrix C hC ≤ 1 := by
  apply (covarianceLift_le_one_iff (covarianceRangeEmbedding C hC)
    (covarianceRangeEmbedding_isometry C hC) (covarianceRangeMatrix C hC)).mp
  simpa only [covarianceRange_reconstruct] using hcap

omit [DecidableEq n] in
/-- The exact source in the constructed coordinates of an arbitrary PSD covariance. -/
theorem covarianceSource_range_coordinates (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (S : Matrix n n ℂ) :
    covarianceSource A C S =
      covarianceSource (mixFamily A (covarianceRangeEmbedding C hC)) (covarianceRangeMatrix C hC) S := by
  have h := covarianceSource_rectangular_mixing A (covarianceRangeEmbedding C hC)
    (covarianceRangeMatrix C hC) S
  simpa only [covarianceRange_reconstruct] using h

omit [DecidableEq ι] in
theorem covarianceIsometry_range_projection (U : Matrix ι κ ℝ) (hU : Uᵀ * U = 1)
    {u : ι → ℝ} (hu : u ∈ LinearMap.range U.mulVecLin) : U *ᵥ (Uᵀ *ᵥ u) = u := by
  obtain ⟨v, rfl⟩ := hu
  change U *ᵥ (Uᵀ *ᵥ (U *ᵥ v)) = U *ᵥ v
  rw [Matrix.mulVec_mulVec v Uᵀ U, hU, Matrix.one_mulVec]

omit [DecidableEq ι] in
/-- Every supported ambient shave is exactly a shave in its canonical range coordinates. -/
theorem covarianceLift_supported_shave (U : Matrix ι κ ℝ) (hU : Uᵀ * U = 1)
    (K : Matrix κ κ ℝ) {u : ι → ℝ} (hu : u ∈ LinearMap.range U.mulVecLin) (h : ℝ) :
    covarianceLift U (K - h • Matrix.vecMulVec (Uᵀ *ᵥ u) (Uᵀ *ᵥ u)) =
      covarianceLift U K - h • Matrix.vecMulVec u u := by
  rw [covarianceLift_shave, covarianceIsometry_range_projection U hU hu]

end
end MatrixSpencer
