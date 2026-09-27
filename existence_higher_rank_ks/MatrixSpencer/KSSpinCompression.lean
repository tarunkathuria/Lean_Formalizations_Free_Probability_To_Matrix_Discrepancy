import MatrixSpencer.KSSupportSymmetry
import MatrixSpencer.KSSafeRetirement
import MatrixSpencer.CovarianceSupport

/-! The concrete full Pauli source compressed to its fixed physical support. -/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer.KSSpinCompression

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

open KSSpinSource KSSupportSymmetry KSSignSymmetry

abbrev supportIndex (A : ι → Matrix n n ℂ) := Fin (Module.finrank ℂ (krausSupport (family A)))

def embedding (A : ι → Matrix n n ℂ) : Matrix (n ⊕ n) (supportIndex A) ℂ :=
  krausSupportEmbedding (family A)

def compressedAtom (A : ι → Matrix n n ℂ) (i : ι) : Matrix (supportIndex A) (supportIndex A) ℂ :=
  compress (embedding A) (doubled (A i))

def compressedSign (A : ι → Matrix n n ℂ) : Matrix (supportIndex A) (supportIndex A) ℂ :=
  compress (embedding A) signMatrix

theorem embedding_isometry (A : ι → Matrix n n ℂ) : (embedding A)ᴴ * embedding A = 1 :=
  krausSupportEmbedding_isometry (family A)

theorem identity_source (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) :
    krausChannel (family A) 1 = (4 : ℝ) • doubled (∑ i, A i * A i) := by
  have hc : coefficientCovariance (fun _ : ι => (2 : ℝ)) = 1 := by
    ext i j
    simp [coefficientCovariance, Matrix.diagonal_apply, Matrix.one_apply]
  have h := source_identity_constant A 2
  rw [hc, covarianceSource_one_one] at h
  have he : krausChannel (family A) 1 = ∑ j, family A j * family A j := by
    simp only [krausChannel, Matrix.mul_one, fun j => (family_isHermitian A hA j).eq]
  rw [he]
  norm_num at h
  exact h

theorem projection_commute_sign (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) :
    Commute (embedding A * (embedding A)ᴴ) (signMatrix (n := n)) := by
  apply supportProjection_commute (family A) signMatrix_isHermitian
  rw [identity_source A hA]
  change signMatrix * ((4 : ℝ) • doubled _) = ((4 : ℝ) • doubled _) * signMatrix
  rw [Matrix.mul_smul, Matrix.smul_mul, (signMatrix_commute_doubled _).eq]

theorem compressedSign_isHermitian (A : ι → Matrix n n ℂ) : (compressedSign A).IsHermitian :=
  compress_isHermitian (embedding A) signMatrix_isHermitian

theorem compressedSign_sq (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) :
    compressedSign A * compressedSign A = 1 :=
  compressed_involution (embedding A) (embedding_isometry A) signMatrix_sq (projection_commute_sign A hA)

theorem compressedAtom_reconstruct (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (i : ι) :
    embedding A * compressedAtom A i * (embedding A)ᴴ = doubled (A i) := by
  exact krausReducedFamily_reconstruct (family A) (family_isHermitian A hA) (i, 0)

theorem compressedAtom_posSemidef (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (i : ι) : (compressedAtom A i).PosSemidef :=
  compress_posSemidef (embedding A) (doubled_posSemidef (hA i))

theorem compressedAtom_ne_zero (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (i : ι) (hi : A i ≠ 0) : compressedAtom A i ≠ 0 := by
  apply compression_nonzero (embedding A) _ (compressedAtom_reconstruct A hA i)
  intro hz
  have h := congrArg Matrix.toBlocks₁₁ hz
  apply hi
  simpa only [doubled, Matrix.toBlocks_fromBlocks₁₁] using h

theorem compressedSign_commute_atom (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (i : ι) : Commute (compressedSign A) (compressedAtom A i) :=
  compressed_commute (embedding A) (embedding_isometry A) signMatrix_isHermitian
    (projection_commute_sign A hA) (signMatrix_commute_doubled (A i))

theorem compressedSign_commute_density (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {S : Matrix (n ⊕ n) (n ⊕ n) ℂ}
    (hS : conjugate signMatrix S = S) :
    Commute (compressedSign A) (compress (embedding A) S) :=
  compressed_commute (embedding A) (embedding_isometry A) signMatrix_isHermitian
    (projection_commute_sign A hA) (commute_of_conjugate_fixed signMatrix_sq hS)

theorem compressed_probe (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (i : ι) :
    realTrace (doubled (A i) * S) = realTrace (compressedAtom A i * compress (embedding A) S) := by
  conv_lhs => arg 1; lhs; rw [← compressedAtom_reconstruct A hA i]
  exact KSSafeRetirement.realTrace_embedded_mul (embedding A) (compressedAtom A i) S

/-- Exact compressed trace-and-prepare identity; the full density may have
components outside the live source support. -/
theorem compressed_source (v : ι → n → ℂ) (c : ι → ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.IsHermitian) :
    covarianceCompressedSource (family (fun i => KSRankOne.atom (v i))) (coefficientCovariance c) S =
      ∑ i, (c i * realTrace (compressedAtom (fun j => KSRankOne.atom (v j)) i *
        compress (embedding (fun j => KSRankOne.atom (v j))) S)) •
          compressedAtom (fun j => KSRankOne.atom (v j)) i := by
  rw [covarianceCompressedSource, source_eq_tracePrepare_real v c hS]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [compressed_probe _ (fun _ => KSRankOne.atom_isHermitian _) S i]
  rfl

theorem coefficientCovariance_posDef {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    (coefficientCovariance c).PosDef :=
  Matrix.posDef_diagonal_iff.mpr (fun j => div_pos (hc j.1) (by norm_num))

theorem compressed_source_posDef (v : ι → n → ℂ) {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) :
    (covarianceCompressedSource (family (fun i => KSRankOne.atom (v i))) (coefficientCovariance c) S).PosDef :=
  covarianceCompressedSource_posDef _ (family_isHermitian _ (fun _ => KSRankOne.atom_isHermitian _))
    (coefficientCovariance_posDef hc) hS

theorem source_reconstruct (v : ι → n → ℂ) (c : ι → ℝ)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    embedding (fun i => KSRankOne.atom (v i)) *
      covarianceCompressedSource (family (fun i => KSRankOne.atom (v i))) (coefficientCovariance c) X *
        (embedding (fun i => KSRankOne.atom (v i)))ᴴ =
    covarianceSource (family (fun i => KSRankOne.atom (v i))) (coefficientCovariance c) X := by
  rw [covarianceCompressedSource, source_eq_tracePrepare v c X]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact compressedAtom_reconstruct _ (fun _ => KSRankOne.atom_isHermitian _) i

theorem compressedSign_commute_source (v : ι → n → ℂ) (c : ι → ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    Commute (compressedSign (fun i => KSRankOne.atom (v i)))
      (covarianceCompressedSource (family (fun i => KSRankOne.atom (v i))) (coefficientCovariance c) S) :=
  compressed_commute _ (embedding_isometry _) signMatrix_isHermitian
    (projection_commute_sign _ (fun _ => KSRankOne.atom_isHermitian _))
    (commute_of_conjugate_fixed signMatrix_sq (KSSpinSymmetry.source_sign_output v c hS))

theorem compressedSign_commute_transport (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef)
    (hJS : conjugate signMatrix S = S) :
    Commute (compressedSign (fun i => KSRankOne.atom (v i)))
      (transportOptimizer (compress (embedding (fun i => KSRankOne.atom (v i))) S)
        (covarianceCompressedSource (family (fun i => KSRankOne.atom (v i))) (coefficientCovariance c) S)) :=
  commute_transport (compressedSign_isHermitian _) (compressedSign_sq _ (fun _ => KSRankOne.atom_isHermitian _))
    (compress_posDef _ (embedding_isometry _) hS) (compressed_source_posDef v hc hS)
    (compressedSign_commute_density _ (fun _ => KSRankOne.atom_isHermitian _) hJS)
    (compressedSign_commute_source v c hS.posSemidef)

theorem transport_probe (A : ι → Matrix n n ℂ) (Z : Matrix (supportIndex A) (supportIndex A) ℂ) (i : ι) :
    realTrace (doubled (A i) * (embedding A * Z * (embedding A)ᴴ)) =
      realTrace (compressedAtom A i * Z) := by
  rw [realTrace_mul_comm, KSSafeRetirement.realTrace_embedded_mul, realTrace_mul_comm]
  rfl

end MatrixSpencer.KSSpinCompression
