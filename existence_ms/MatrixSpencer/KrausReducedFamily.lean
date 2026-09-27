import MatrixSpencer.KrausCompressionBridge

/-!
# The actual Kraus family on its fixed physical support

Each original Hermitian Kraus matrix is supported on the constructed source
range. Compression therefore gives a genuine reduced Kraus source depending
only on the compressed density, including at zero support.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

def krausSupportProjection (B : ι → Matrix n n ℂ) : Matrix n n ℂ :=
  krausSupportEmbedding B * (krausSupportEmbedding B)ᴴ

theorem krausSupportProjection_isHermitian (B : ι → Matrix n n ℂ) :
    (krausSupportProjection B).IsHermitian :=
  (Matrix.posSemidef_self_mul_conjTranspose (krausSupportEmbedding B)).isHermitian

theorem kraus_identity_source_projection (B : ι → Matrix n n ℂ) :
    krausChannel B 1 * krausSupportProjection B = krausChannel B 1 := by
  have hi := krausSupportEmbedding_isometry B
  conv_lhs => lhs; rw [← krausCompressedSource_reconstruct B Matrix.PosSemidef.one]
  rw [krausSupportProjection]
  calc
    _ = krausSupportEmbedding B * krausCompressedSource B 1 *
        ((krausSupportEmbedding B)ᴴ * krausSupportEmbedding B) * (krausSupportEmbedding B)ᴴ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hi, Matrix.mul_one, krausCompressedSource_reconstruct B Matrix.PosSemidef.one]

/-- Every adjoint Kraus matrix annihilates the orthogonal complement of the actual source range. -/
theorem kraus_adjoint_complement_zero (B : ι → Matrix n n ℂ) (a : ι) :
    (B a)ᴴ * (1 - krausSupportProjection B) = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  have hx : krausChannel B 1 *ᵥ ((1 - krausSupportProjection B) *ᵥ Pi.single j 1) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, kraus_identity_source_projection,
      sub_self, Matrix.zero_mulVec]
  have h := (krausChannel_mulVec_eq_zero_iff B Matrix.PosDef.one _).mp hx a
  simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using h

theorem kraus_projection_right (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian) (a : ι) :
    B a * krausSupportProjection B = B a := by
  have h := kraus_adjoint_complement_zero B a
  rw [(hB a).eq, Matrix.mul_sub, Matrix.mul_one] at h
  exact (sub_eq_zero.mp h).symm

theorem kraus_projection_left (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian) (a : ι) :
    krausSupportProjection B * B a = B a := by
  have h := congrArg Matrix.conjTranspose (kraus_projection_right B hB a)
  simpa only [Matrix.conjTranspose_mul, (krausSupportProjection_isHermitian B).eq, (hB a).eq] using h

def krausReducedFamily (B : ι → Matrix n n ℂ) (a : ι) :
    Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ :=
  (krausSupportEmbedding B)ᴴ * B a * krausSupportEmbedding B

theorem krausReducedFamily_isHermitian (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (a : ι) : (krausReducedFamily B a).IsHermitian := by
  rw [Matrix.IsHermitian, krausReducedFamily, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, (hB a).eq]
  simp only [Matrix.mul_assoc]

/-- Reconstruction holds for every individual Hermitian force, not only for the source sum. -/
theorem krausReducedFamily_reconstruct (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (a : ι) :
    krausSupportEmbedding B * krausReducedFamily B a * (krausSupportEmbedding B)ᴴ = B a := by
  calc
    _ = krausSupportProjection B * B a * krausSupportProjection B := by
      simp only [krausReducedFamily, krausSupportProjection, Matrix.mul_assoc]
    _ = _ := by rw [kraus_projection_left B hB, kraus_projection_right B hB]

/-- The compressed source is exactly the Kraus channel of the reduced family at the compressed density. -/
theorem krausReducedFamily_channel (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) (S : Matrix n n ℂ) :
    krausChannel (krausReducedFamily B) (krausCompressedDensity B S) = krausCompressedSource B S := by
  rw [krausCompressedSource_eq_compression]
  simp only [krausChannel, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [(krausReducedFamily_isHermitian B hB a).eq, (hB a).eq]
  calc
    _ = (krausSupportEmbedding B)ᴴ * (B a * krausSupportProjection B) * S *
      (krausSupportProjection B * B a) * krausSupportEmbedding B := by
      simp only [krausReducedFamily, krausCompressedDensity, krausSupportProjection, Matrix.mul_assoc]
    _ = _ := by rw [kraus_projection_right B hB, kraus_projection_left B hB]; simp only [Matrix.mul_assoc]

theorem krausReducedFamily_source_posDef (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) {S : Matrix n n ℂ} (hS : S.PosDef) :
    (krausChannel (krausReducedFamily B) (krausCompressedDensity B S)).PosDef := by
  rw [krausReducedFamily_channel B hB]
  exact krausCompressedSource_posDef B hS

/-- Exact full-to-reduced fidelity identity with the actual reduced Kraus family. -/
theorem fidelity_krausReducedFamily (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    fidelity S (krausChannel B S) =
      fidelity (krausCompressedDensity B S)
        (krausChannel (krausReducedFamily B) (krausCompressedDensity B S)) := by
  rw [krausReducedFamily_channel B hB]
  exact fidelity_kraus_support_compression B hS

end MatrixSpencer
