import MatrixSpencer.KSEighthActualState
import MatrixSpencer.KSSupportedCenterCurve

/-! The common doubled physical support for the two-sign construction. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthFullSupport
open KSEighthBlocks KSEighthActualState

variable {ι n m : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

theorem doubledRect_compress_blockDiag (V : Matrix n m ℂ) (A B : Matrix n n ℂ) :
    (doubledRect V)ᴴ * blockDiag A B * doubledRect V = blockDiag (Vᴴ * A * V) (Vᴴ * B * V) := by
  rw [doubledRect_compression]
  simp only [KSEighthBlocks.blockDiag, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, Matrix.mul_zero, Matrix.zero_mul]

theorem source_compressed (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0) (c : ι → ℝ)
    {X : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hX : X.IsHermitian) :
    (doubledRect (KSEighthSupport.embedding v))ᴴ *
      covarianceSource (KSIndependentSource.family (fun i => KSRankOne.atom (v i)))
        (KSIndependentSource.coefficientCovariance c) X * doubledRect (KSEighthSupport.embedding v) =
    blockDiag
      (KSBalancedSpin.source (fun i => KSRankOne.atom (KSEighthSupport.compressedVector v i)) c
        ((KSEighthSupport.embedding v)ᴴ * X.toBlocks₁₁ * KSEighthSupport.embedding v))
      (KSBalancedSpin.source (fun i => KSRankOne.atom (KSEighthSupport.compressedVector v i)) c
        ((KSEighthSupport.embedding v)ᴴ * X.toBlocks₂₂ * KSEighthSupport.embedding v)) := by
  rw [independent_rankOne_source_blocks v c hX, doubledRect_compress_blockDiag,
    KSEighthSupport.source_compress v hv, KSEighthSupport.source_compress v hv]

theorem source_reconstruct (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0) (c : ι → ℝ)
    {X : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hX : X.IsHermitian) :
    let V := doubledRect (KSEighthSupport.embedding v)
    let M := covarianceSource (KSIndependentSource.family (fun i => KSRankOne.atom (v i)))
      (KSIndependentSource.coefficientCovariance c) X
    V * (Vᴴ * M * V) * Vᴴ = M := by
  dsimp only
  rw [source_compressed v hv c hX, doubledRect_congruence,
    ← KSEighthSupport.source_reconstruct v hv, ← KSEighthSupport.source_reconstruct v hv,
    independent_rankOne_source_blocks v c hX]

variable [Nonempty n]

abbrev supportIndex (v : ι → n → ℂ) := Fin (Module.finrank ℂ (krausSupport (fun i => KSRankOne.atom (v i))))

theorem independent_atom_reconstruct (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0) (j : ι × Bool) :
    fullEmbedding v * KSIndependentSource.family
      (fun i => KSRankOne.atom (KSEighthSupport.compressedVector v i)) j * (fullEmbedding v)ᴴ =
      family v j := by
  have he (i : ι) : KSEighthSupport.embedding v *
      KSRankOne.atom (KSEighthSupport.compressedVector v i) * (KSEighthSupport.embedding v)ᴴ =
      KSRankOne.atom (v i) := by
    rw [← KSEighthSupport.compressed_atom]
    exact KSEighthSupport.atom_supported v hv i
  rcases j with ⟨i, b⟩
  cases b <;> change doubledRect _ * KSEighthBlocks.blockDiag _ _ * (doubledRect _)ᴴ = KSEighthBlocks.blockDiag _ _
  · rw [doubledRect_congruence, he, Matrix.mul_zero, Matrix.zero_mul]
  · rw [doubledRect_congruence, he, Matrix.mul_zero, Matrix.zero_mul]

theorem independent_probe (v : ι → n → ℂ)
    (Z : Matrix (supportIndex v ⊕ supportIndex v) (supportIndex v ⊕ supportIndex v) ℂ)
    (j : ι × Bool) :
    realTrace (family v j * (fullEmbedding v * Z * (fullEmbedding v)ᴴ)) =
      realTrace (KSIndependentSource.family
        (fun i => KSRankOne.atom (KSEighthSupport.compressedVector v i)) j * Z) := by
  rw [realTrace_mul_comm, KSSafeRetirement.realTrace_embedded_mul, realTrace_mul_comm]
  apply congrArg (fun M => realTrace (M * Z))
  rcases j with ⟨i, b⟩
  cases b <;> change (doubledRect _)ᴴ * KSEighthBlocks.blockDiag _ _ * doubledRect _ = KSEighthBlocks.blockDiag _ _
  · rw [doubledRect_compress_blockDiag, KSEighthSupport.compressed_atom, Matrix.mul_zero, Matrix.zero_mul]
  · rw [doubledRect_compress_blockDiag, KSEighthSupport.compressed_atom, Matrix.mul_zero, Matrix.zero_mul]

theorem actual_density_compressed (H : Matrix n n ℂ) (v : ι → n → ℂ) (x : ι → ℝ)
    (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) {θ : ℝ} (hθ : 0 < θ) :
    (fullEmbedding v)ᴴ * (fullDensity H v x θ : Matrix (n ⊕ n) (n ⊕ n) ℂ) * fullEmbedding v =
      blockDiag (supportDensity H v x θ true) (supportDensity H v x θ false) := by
  rw [fullDensity_blockDiagonal H v x hx hθ]
  exact doubledRect_compress_blockDiag _ _ _

theorem actual_source_compressed (H : Matrix n n ℂ) (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (θ : ℝ) :
    (fullEmbedding v)ᴴ * covarianceSource (family v) (covariance x) (fullDensity H v x θ) * fullEmbedding v =
      blockDiag (supportSource H v x θ true) (supportSource H v x θ false) :=
  source_compressed v hv (KSEighthBalanced.owner x) (fullDensity H v x θ).property

theorem actual_source_posDef (H : Matrix n n ℂ) (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) {θ : ℝ} (hθ : 0 < θ) :
    ((fullEmbedding v)ᴴ * covarianceSource (family v) (covariance x) (fullDensity H v x θ) *
      fullEmbedding v).PosDef := by
  rw [actual_source_compressed H v hv x θ]
  exact blockDiag_posDef (supportSource_posDef H v hv x hx hθ true)
    (supportSource_posDef H v hv x hx hθ false)

theorem actual_transport_solve (H : Matrix n n ℂ) (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) {θ : ℝ} (hθ : 0 < θ) :
    fullTransport H v x θ *
      ((fullEmbedding v)ᴴ * covarianceSource (family v) (covariance x) (fullDensity H v x θ) *
        fullEmbedding v) * fullTransport H v x θ =
      (fullEmbedding v)ᴴ * (fullDensity H v x θ : Matrix (n ⊕ n) (n ⊕ n) ℂ) * fullEmbedding v := by
  rw [actual_source_compressed H v hv x θ, actual_density_compressed H v x hx hθ]
  unfold fullTransport
  rw [blockDiag_mul, blockDiag_mul, transport_solve H v hv x hx hθ true,
    transport_solve H v hv x hx hθ false]

end MatrixSpencer.KSEighthFullSupport
