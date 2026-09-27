import MatrixSpencer.ComplexGram
import MatrixSpencer.Statement
import ExistenceMS.FrozenStatement

/-! The real-to-complex input bridge, without importing either old Matrix
Spencer endpoint. The Euclidean norm identities are the elementary split
of a complex vector into real and imaginary parts. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace ExistenceMS.RealInput
open MatrixSpencer

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

theorem signing_bound_of_complex {N d : ℕ}
    (A : Fin N → Matrix (Fin d) (Fin d) ℝ) (B : ℝ)
    (h : ∃ s : Fin N → ℝ, IsFullSigning s ∧
      spectralNorm (signedSum (fun i => realMatrixEmbedding (A i)) s) ≤ B) :
    ∃ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ i, s i • A i)‖ ≤ B := by
  obtain ⟨s,hs,hbound⟩ := h
  refine ⟨s,hs,?_⟩
  have heq : signedSum (fun i => realMatrixEmbedding (A i)) s =
      realMatrixEmbedding (∑ i, s i • A i) := by
    simp only [signedSum, map_sum, embedding_real_smul]
  rw [heq, spectralNorm, realMatrixEmbedding_norm] at hbound
  exact hbound

end ExistenceMS.RealInput
