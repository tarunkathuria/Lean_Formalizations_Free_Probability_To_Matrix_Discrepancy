import MatrixSpencer.Main
import MatrixSpencer.RectangularMain
import MatrixSpencer.ComplexGram



open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace MatrixSpencer.OriginalConjecture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realPart (x : EuclideanSpace ℂ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => (x i).re)

def imagPart (x : EuclideanSpace ℂ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => (x i).im)

def ofRealVector (x : EuclideanSpace ℝ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => (x i : ℂ))

omit [DecidableEq ι] in
theorem norm_sq_split (x : EuclideanSpace ℂ ι) :
    ‖x‖ ^ 2 = ‖realPart x‖ ^ 2 + ‖imagPart x‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, realPart, imagPart, PiLp.toLp_apply,
    Real.norm_eq_abs, sq_abs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

omit [DecidableEq ι] in
@[simp] theorem ofRealVector_norm (x : EuclideanSpace ℝ ι) :
    ‖ofRealVector x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [PiLp.norm_sq_eq_of_L2, ofRealVector]

theorem realPart_action (A : Matrix ι ι ℝ) (x : EuclideanSpace ℂ ι) :
    realPart (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (realMatrixEmbedding A) x) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A (realPart x) := by
  ext i
  change ((realMatrixEmbedding A *ᵥ WithLp.ofLp x) i).re =
    (A *ᵥ (fun j => (x j).re)) i
  simp [Matrix.mulVec, dotProduct, realMatrixEmbedding]

theorem imagPart_action (A : Matrix ι ι ℝ) (x : EuclideanSpace ℂ ι) :
    imagPart (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (realMatrixEmbedding A) x) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A (imagPart x) := by
  ext i
  change ((realMatrixEmbedding A *ᵥ WithLp.ofLp x) i).im =
    (A *ᵥ (fun j => (x j).im)) i
  simp [Matrix.mulVec, dotProduct, realMatrixEmbedding]

theorem ofRealVector_action (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    ofRealVector (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A x) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (realMatrixEmbedding A) (ofRealVector x) := by
  ext i
  change ((A *ᵥ WithLp.ofLp x) i : ℂ) =
    (realMatrixEmbedding A *ᵥ (fun j => (x j : ℂ))) i
  simp [Matrix.mulVec, dotProduct, realMatrixEmbedding]

/-- Entrywise complexification preserves the real Euclidean operator norm exactly. -/
theorem realMatrixEmbedding_norm (A : Matrix ι ι ℝ) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (realMatrixEmbedding A)‖ = ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have hr := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A).le_opNorm (realPart x)
    have hi := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A).le_opNorm (imagPart x)
    have hr2 := pow_le_pow_left₀ (norm_nonneg _) hr 2
    have hi2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
    have hs := norm_sq_split (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (realMatrixEmbedding A) x)
    rw [realPart_action, imagPart_action] at hs
    have hx := norm_sq_split x
    have hsq : ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (realMatrixEmbedding A) x‖ ^ 2 ≤
        (‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A‖ * ‖x‖) ^ 2 := by
      rw [hs, mul_pow, hx, mul_add]
      exact add_le_add (by simpa only [mul_pow] using hr2) (by simpa only [mul_pow] using hi2)
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hsq
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (realMatrixEmbedding A)).le_opNorm (ofRealVector x)
    rw [← ofRealVector_action, ofRealVector_norm, ofRealVector_norm] at h
    exact h

theorem embedding_hermitian_of_symmetric (A : Matrix ι ι ℝ) (hA : Aᵀ = A) :
    (realMatrixEmbedding A).IsHermitian := by
  have hr : A.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  exact hr.map (fun x : ℝ => (x : ℂ)) (by intro x; simp)

@[simp] theorem embedding_real_smul (c : ℝ) (A : Matrix ι ι ℝ) :
    realMatrixEmbedding (c • A) = (c : ℂ) • realMatrixEmbedding A := by
  ext i j
  simp [realMatrixEmbedding]

theorem sqrt_log_two_mul_le (x : ℝ) (hx : 1 ≤ x) :
    Real.sqrt (Real.log (2 * x)) ≤ 2 * max 1 (Real.sqrt (Real.log x)) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hl2 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hlog := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxpos.ne'
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hM1 : 1 ≤ max 1 (Real.sqrt (Real.log x)) := le_max_left _ _
  have hMz : Real.sqrt (Real.log x) ≤ max 1 (Real.sqrt (Real.log x)) := le_max_right _ _
  have hM0 : 0 ≤ max 1 (Real.sqrt (Real.log x)) := le_trans zero_le_one hM1
  have hMsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hMz 2
  have hs := Real.sq_sqrt hl
  have hs2 := Real.sq_sqrt hl2
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) hM0)).mp
  nlinarith

/-- A numerical constant chosen before either dimension or the input family. -/
def originalConstant : ℝ := matrixSpencerSquareConstant + 2 * matrixSpencerRectangularConstant

theorem originalConstant_eq : originalConstant = 17938533 := by
  norm_num [originalConstant, matrixSpencerSquareConstant_eq, matrixSpencerRectangularConstant_eq]

theorem originalConstant_pos : 0 < originalConstant := by
  rw [originalConstant_eq]
  norm_num

/-- The complex endpoint implies the single original aspect-ratio formula in every regime. -/
theorem complex_original_bound (N d : ℕ) (A : Fin N → CMatrix d)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, spectralNorm (A i) ≤ 1) :
    ∃ ε : Fin N → ℝ, IsFullSigning ε ∧
      spectralNorm (signedSum A ε) ≤
        originalConstant * Real.sqrt (N : ℝ) *
          max 1 (Real.sqrt (Real.log ((d : ℝ) / (N : ℝ)))) := by
  by_cases hzero : N = 0
  · subst N
    refine ⟨fun _ => 1, isFullSigning_one 0, ?_⟩
    simp
  have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hzero
  have hs : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hM1 : 1 ≤ max 1 (Real.sqrt (Real.log ((d : ℝ) / (N : ℝ)))) := le_max_left _ _
  have hM0 : 0 ≤ max 1 (Real.sqrt (Real.log ((d : ℝ) / (N : ℝ)))) :=
    le_trans zero_le_one hM1
  by_cases hdim : d ≤ N
  · obtain ⟨ε, hε, hb⟩ := matrix_spencer_square_with_constant N d hdim A hA hN
    refine ⟨ε, hε, hb.trans ?_⟩
    have hC : matrixSpencerSquareConstant ≤ originalConstant := by
      unfold originalConstant
      linarith [matrixSpencerRectangularConstant_pos]
    calc
      _ ≤ originalConstant * Real.sqrt (N : ℝ) := mul_le_mul_of_nonneg_right hC hs
      _ = (originalConstant * Real.sqrt (N : ℝ)) * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hM1 (mul_nonneg originalConstant_pos.le hs)
  · have hND : N ≤ d := Nat.le_of_lt (Nat.lt_of_not_ge hdim)
    obtain ⟨ε, hε, hb⟩ := matrix_spencer_rectangular_with_constant N d hNpos hND A hA hN
    refine ⟨ε, hε, hb.trans ?_⟩
    have hnreal : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero)
    have hratio : 1 ≤ (d : ℝ) / (N : ℝ) := by
      apply (le_div_iff₀ hnreal).mpr
      simpa using (Nat.cast_le.mpr hND : (N : ℝ) ≤ d)
    have hl := sqrt_log_two_mul_le ((d : ℝ) / (N : ℝ)) hratio
    have hlog : rectangularLog N d = Real.log (2 * ((d : ℝ) / (N : ℝ))) := by
      unfold rectangularLog
      congr 1
      ring
    have hscale : Real.sqrt ((N : ℝ) * rectangularLog N d) ≤
        2 * Real.sqrt (N : ℝ) * max 1 (Real.sqrt (Real.log ((d : ℝ) / (N : ℝ)))) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), hlog]
      calc
        _ ≤ Real.sqrt (N : ℝ) * (2 * max 1 (Real.sqrt (Real.log ((d : ℝ) / (N : ℝ))))) :=
          mul_le_mul_of_nonneg_left hl hs
        _ = _ := by ring
    have hC : 2 * matrixSpencerRectangularConstant ≤ originalConstant := by
      unfold originalConstant
      linarith [matrixSpencerSquareConstant_pos]
    calc
      _ ≤ matrixSpencerRectangularConstant *
          (2 * Real.sqrt (N : ℝ) * max 1 (Real.sqrt (Real.log ((d : ℝ) / (N : ℝ))))) :=
        mul_le_mul_of_nonneg_left hscale matrixSpencerRectangularConstant_pos.le
      _ = (2 * matrixSpencerRectangularConstant) * Real.sqrt (N : ℝ) *
          max 1 (Real.sqrt (Real.log ((d : ℝ) / (N : ℝ)))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hs) hM0


theorem matrix_spencer_original :
    ∃ C : ℝ, 0 < C ∧ ∀ (N d : ℕ) (A : Fin N → Matrix (Fin d) (Fin d) ℝ),
      (∀ i, (A i)ᵀ = A i) →
      (∀ i, ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (A i)‖ ≤ 1) →
      ∃ ε : Fin N → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (∑ i, ε i • A i)‖ ≤
          C * Real.sqrt (N : ℝ) * max 1 (Real.sqrt (Real.log ((d : ℝ) / (N : ℝ)))) := by
  refine ⟨originalConstant, originalConstant_pos, ?_⟩
  intro N d A hA hN
  have hcomplex : ∀ i, spectralNorm (realMatrixEmbedding (A i)) ≤ 1 := by
    intro i
    rw [spectralNorm, realMatrixEmbedding_norm]
    exact hN i
  obtain ⟨ε, hε, hb⟩ := complex_original_bound N d (fun i => realMatrixEmbedding (A i))
    (fun i => embedding_hermitian_of_symmetric (A i) (hA i)) hcomplex
  refine ⟨ε, hε, ?_⟩
  have heq : signedSum (fun i => realMatrixEmbedding (A i)) ε =
      realMatrixEmbedding (∑ i, ε i • A i) := by
    simp only [signedSum, map_sum, embedding_real_smul]
  rw [heq, spectralNorm, realMatrixEmbedding_norm] at hb
  exact hb

end MatrixSpencer.OriginalConjecture
