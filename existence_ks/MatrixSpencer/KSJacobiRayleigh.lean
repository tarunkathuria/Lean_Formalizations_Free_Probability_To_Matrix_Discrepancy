import MatrixSpencer.KSJacobiIteration
import MatrixSpencer.KSRayleighAccuracy

/-!
# Approximate minimum-Rayleigh vector constructed by the finite Jacobi run

The output is the accumulated-basis column selected by a finite comparison
scan of the final diagonal. The approximation follows from the actual
off-diagonal residual. No spectral vector or numerical minimizer is assumed.
-/

open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSJacobiRayleigh

open KSRayleighAccuracy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem frobeniusEnergy_nonneg (K : Matrix ι ι ℝ) : 0 ≤ KSJacobiStep.frobeniusEnergy K := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- The Euclidean operator norm is bounded by the actual squared-entry sum. -/
theorem operatorNorm_le_frobenius (K : Matrix ι ι ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) K‖ ≤ Real.sqrt (KSJacobiStep.frobeniusEnergy K) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg v))).mp
  rw [mul_pow, Real.sq_sqrt (frobeniusEnergy_nonneg K)]
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  change (∑ i, (∑ j, K i j * v j) ^ 2) ≤
    KSJacobiStep.frobeniusEnergy K * ∑ j, v j ^ 2
  calc
    _ ≤ ∑ i, (∑ j, K i j ^ 2) * (∑ j, v j ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (K i) (WithLp.ofLp v)
    _ = _ := by rw [← Finset.sum_mul]; rfl

def diagonalPart (K : Matrix ι ι ℝ) : Matrix ι ι ℝ := Matrix.diagonal (fun i => K i i)

theorem residual_frobeniusEnergy (K : Matrix ι ι ℝ) :
    KSJacobiStep.frobeniusEnergy (K - diagonalPart K) = KSJacobiStep.offDiagonalEnergy K := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j <;> simp [diagonalPart, hij]

theorem residual_operatorNorm (K : Matrix ι ι ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (K - diagonalPart K)‖ ≤
      Real.sqrt (KSJacobiStep.offDiagonalEnergy K) := by
  simpa only [residual_frobeniusEnergy] using operatorNorm_le_frobenius (K - diagonalPart K)

theorem realRayleigh_one (v : EuclideanSpace ℝ ι) : realRayleigh 1 v = ‖v‖ ^ 2 := by
  simp [realRayleigh, real_inner_self_eq_norm_sq]

theorem realRayleigh_conjugation (K U : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) :
    realRayleigh (Uᵀ * K * U) v =
      realRayleigh K (Matrix.toEuclideanCLM (𝕜 := ℝ) U v) := by
  simp only [realRayleigh_eq_quadratic, Matrix.ofLp_toEuclideanCLM]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem orthogonal_preserves_norm (U : Matrix ι ι ℝ) (hU : Uᵀ * U = 1)
    (v : EuclideanSpace ℝ ι) : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) U v‖ = ‖v‖ := by
  have h := realRayleigh_conjugation 1 U v
  simp only [Matrix.mul_one, hU, realRayleigh_one] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h.symm

theorem realRayleigh_single (K : Matrix ι ι ℝ) (i : ι) :
    realRayleigh K (EuclideanSpace.single i 1) = K i i := by
  rw [realRayleigh_eq_quadratic, EuclideanSpace.ofLp_single, single_dotProduct,
    Matrix.mulVec_single_one, one_mul]
  rfl

theorem diagonalRayleigh_lower (K : Matrix ι ι ℝ) (i : ι)
    (hmin : ∀ j, K i i ≤ K j j) (v : EuclideanSpace ℝ ι) (hv : ‖v‖ = 1) :
    K i i ≤ realRayleigh (diagonalPart K) v := by
  have hsq : (∑ j, v j ^ 2) = 1 := by
    have h := EuclideanSpace.norm_sq_eq v
    simpa only [hv, one_pow, Real.norm_eq_abs, sq_abs] using h.symm
  rw [realRayleigh_eq_quadratic]
  change K i i ≤ ∑ j, v j * (Matrix.diagonal (fun k => K k k) *ᵥ WithLp.ofLp v) j
  simp only [Matrix.mulVec_diagonal]
  calc
    K i i = ∑ j, K i i * v j ^ 2 := by rw [← Finset.mul_sum, hsq, mul_one]
    _ ≤ ∑ j, K j j * v j ^ 2 :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hmin j) (sq_nonneg _))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      change K j j * v j ^ 2 = v j * (K j j * v j)
      ring

/-- A smallest diagonal entry is within the residual norm of every Rayleigh value.
There is only one residual error, because the selected coordinate has zero residual diagonal. -/
theorem minimum_diagonal_accuracy (K : Matrix ι ι ℝ) (i : ι)
    (hmin : ∀ j, K i i ≤ K j j) {τ : ℝ}
    (herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (K - diagonalPart K)‖ ≤ τ)
    (v : EuclideanSpace ℝ ι) (hv : ‖v‖ = 1) :
    K i i ≤ realRayleigh K v + τ := by
  have hd := diagonalRayleigh_lower K i hmin v hv
  have he := abs_le.mp (realRayleigh_error K (diagonalPart K) herr v hv)
  linarith

def basisColumn (U : Matrix ι ι ℝ) (i : ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun j => U j i)

theorem basisColumn_eq_apply (U : Matrix ι ι ℝ) (i : ι) :
    basisColumn U i = Matrix.toEuclideanCLM (𝕜 := ℝ) U (EuclideanSpace.single i 1) := by
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  change (fun j => U j i) = U *ᵥ Pi.single i 1
  exact (Matrix.mulVec_single_one U i).symm

theorem basisColumn_norm (U : Matrix ι ι ℝ) (hU : Uᵀ * U = 1) (i : ι) :
    ‖basisColumn U i‖ = 1 := by
  rw [basisColumn_eq_apply, orthogonal_preserves_norm U hU, EuclideanSpace.norm_single]
  norm_num

theorem basisColumn_Rayleigh (K U : Matrix ι ι ℝ) (i : ι) :
    realRayleigh K (basisColumn U i) = (Uᵀ * K * U) i i := by
  rw [basisColumn_eq_apply, ← realRayleigh_conjugation, realRayleigh_single]

variable {d : ℕ}

def minimumDiagonal (K : Matrix (Fin d) (Fin d) ℝ) (hd : 0 < d) : Fin d :=
  (KSJacobiIteration.maxScan (fun i => -K i i) (List.finRange d)).getD ⟨0, hd⟩

theorem minimumDiagonal_le (K : Matrix (Fin d) (Fin d) ℝ) (hd : 0 < d) (j : Fin d) :
    K (minimumDiagonal K hd) (minimumDiagonal K hd) ≤ K j j := by
  cases hs : KSJacobiIteration.maxScan (fun i => -K i i) (List.finRange d) with
  | none =>
    have hnil := (KSJacobiIteration.maxScan_none_iff _ _).mp hs
    have hlen := congrArg List.length hnil
    simp only [List.length_finRange, List.length_nil] at hlen
    omega
  | some i =>
    have hm := KSJacobiIteration.maxScan_maximal (fun i => -K i i)
      (List.finRange d) hs (List.mem_finRange j)
    simp only [minimumDiagonal, hs, Option.getD_some]
    linarith

def finalMatrix (K : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  KSJacobiIteration.run K (KSJacobiIteration.iterationCount K τ)

def finalBasis (K : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  KSJacobiIteration.accumulatedBasis K (KSJacobiIteration.iterationCount K τ)

/-- The actual returned vector: a concretely selected column of the computed basis. -/
def outputVector (K : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (hd : 0 < d) : EuclideanSpace ℝ (Fin d) :=
  basisColumn (finalBasis K τ) (minimumDiagonal (finalMatrix K τ) hd)

theorem outputVector_norm (K : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (hd : 0 < d) :
    ‖outputVector K τ hd‖ = 1 :=
  basisColumn_norm _ (KSJacobiIteration.accumulatedBasis_transpose_mul K _) _

theorem outputVector_Rayleigh (K : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (hd : 0 < d) :
    realRayleigh K (outputVector K τ hd) =
      finalMatrix K τ (minimumDiagonal (finalMatrix K τ) hd) (minimumDiagonal (finalMatrix K τ) hd) := by
  rw [outputVector, basisColumn_Rayleigh]
  exact congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A
    (minimumDiagonal (finalMatrix K τ) hd) (minimumDiagonal (finalMatrix K τ) hd))
      (KSJacobiIteration.run_eq_conjugation K _).symm

/-- Every unit competitor is pulled back by the computed orthogonal basis. -/
theorem outputVector_competitor_accuracy (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsSymm)
    {τ : ℝ} (hτ : 0 < τ) (hd : 0 < d) (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) :
    realRayleigh K (outputVector K τ hd) ≤ realRayleigh K v + τ := by
  let U := finalBasis K τ
  let w := Matrix.toEuclideanCLM (𝕜 := ℝ) Uᵀ v
  have hU : U * Uᵀ = 1 := KSJacobiIteration.accumulatedBasis_mul_transpose K _
  have hw : ‖w‖ = 1 := by
    rw [show w = Matrix.toEuclideanCLM (𝕜 := ℝ) Uᵀ v from rfl,
      orthogonal_preserves_norm Uᵀ (by simpa only [Matrix.transpose_transpose] using hU), hv]
  have hUw : Matrix.toEuclideanCLM (𝕜 := ℝ) U w = v := by
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) U * Matrix.toEuclideanCLM (𝕜 := ℝ) Uᵀ) v = v
    rw [← map_mul, hU, map_one, ContinuousLinearMap.one_apply]
  have hconj : finalMatrix K τ = Uᵀ * K * U := KSJacobiIteration.run_eq_conjugation K _
  have hq : realRayleigh (finalMatrix K τ) w = realRayleigh K v := by
    rw [hconj, realRayleigh_conjugation, hUw]
  have herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (finalMatrix K τ - diagonalPart (finalMatrix K τ))‖ ≤ τ :=
    (residual_operatorNorm _).trans (KSJacobiIteration.run_offDiagonalFrobenius_accuracy K hK hτ)
  have ha := minimum_diagonal_accuracy (finalMatrix K τ)
    (minimumDiagonal (finalMatrix K τ) hd) (minimumDiagonal_le _ hd) herr w hw
  rwa [← outputVector_Rayleigh, hq] at ha

/-- No approximate-minimizer oracle remains: the explicitly constructed vector
meets the tolerance used by the existing Rayleigh error-propagation interface. -/
theorem outputVector_accuracy (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsSymm)
    {τ : ℝ} (hτ : 0 < τ) (hd : 0 < d) :
    realRayleigh K (outputVector K τ hd) ≤ leastRayleigh K + τ := by
  apply (sub_le_iff_le_add).mp
  apply le_csInf (show (unitRayleighValues K).Nonempty from
    ⟨_, outputVector K τ hd, outputVector_norm K τ hd, rfl⟩)
  rintro t ⟨v, hv, rfl⟩
  have h := outputVector_competitor_accuracy K hK hτ hd v hv
  linarith

/-- Running Jacobi on the reported symmetric matrix discharges the approximate
minimizer premise of the earlier numerical error-propagation theorem. -/
theorem outputVector_accuracy_of_matrix_error
    (K Khat : Matrix (Fin d) (Fin d) ℝ) (hKhat : Khat.IsSymm)
    {κ : ℝ} (hκ : 0 < κ) (hd : 0 < d)
    (herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (K - Khat)‖ ≤ κ) :
    ‖outputVector Khat κ hd‖ = 1 ∧
      realRayleigh K (outputVector Khat κ hd) ≤ leastRayleigh K + 3 * κ := by
  refine ⟨outputVector_norm Khat κ hd, ?_⟩
  exact approximate_minimum_Rayleigh_accuracy K Khat herr
    (outputVector Khat κ hd) (outputVector_norm Khat κ hd)
      (outputVector_accuracy Khat hKhat hκ hd)

theorem outputVector_nonpositive_accuracy_of_matrix_error
    (K Khat : Matrix (Fin d) (Fin d) ℝ) (hKhat : Khat.IsSymm)
    {κ : ℝ} (hκ : 0 < κ) (hd : 0 < d)
    (herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (K - Khat)‖ ≤ κ)
    (hneg : leastRayleigh K ≤ 0) :
    realRayleigh K (outputVector Khat κ hd) ≤ 3 * κ := by
  have h := (outputVector_accuracy_of_matrix_error K Khat hKhat hκ hd herr).2
  linarith

/-- Empty dimension has the identity basis and unchanged matrix; it supplies no unit vector. -/
theorem empty_dimension_identity (K : Matrix (Fin 0) (Fin 0) ℝ) (τ : ℝ) :
    finalMatrix K τ = K ∧ finalBasis K τ = 1 := by
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

theorem empty_dimension_no_unit (v : EuclideanSpace ℝ (Fin 0)) : ‖v‖ ≠ 1 := by
  have hv : v = 0 := Subsingleton.elim _ _
  simp [hv]

end MatrixSpencer.KSJacobiRayleigh
