import HigherRankKS.SourceCompression
import HigherRankKS.SpinSymmetry
import MatrixSpencer.KSSupportSymmetry
import MatrixSpencer.KSOwnerRetirement

/-! The sign involution and actual transport on the live source support. -/

open Matrix MatrixSpencer MatrixSpencer.KSSignSymmetry MatrixSpencer.KSSupportSymmetry
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS.SupportedSpin

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

def probe (A : ι → Matrix n n ℂ) (i : ι) :
    Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ :=
  compress (sourceEmbedding A) (spinAtom (A i))

def involution (A : ι → Matrix n n ℂ) :
    Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ :=
  compress (sourceEmbedding A) signMatrix

def density (A : ι → Matrix n n ℂ) (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ := compress (sourceEmbedding A) S

def transport (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ :=
  transportOptimizer (density A S) (compressedSource A β c S)

def term (A : ι → Matrix n n ℂ) (β : ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (i : ι) :
    Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ :=
  compress (sourceEmbedding A) (sourceTerm β (A i) S)

theorem embedding_isometry (A : ι → Matrix n n ℂ) :
    (sourceEmbedding A)ᴴ * sourceEmbedding A = 1 := krausSupportEmbedding_isometry _

theorem projection_commute (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) :
    Commute (sourceEmbedding A * (sourceEmbedding A)ᴴ) signMatrix := by
  apply supportProjection_commute (fun i => spinAtom (A i)) signMatrix_isHermitian
  change signMatrix * krausChannel (fun i => spinAtom (A i)) 1 =
    krausChannel (fun i => spinAtom (A i)) 1 * signMatrix
  simp only [krausChannel, Matrix.mul_one, Matrix.mul_sum, Matrix.sum_mul,
    fun i => (spinAtom_posSemidef (hA i)).isHermitian.eq]
  apply Finset.sum_congr rfl
  intro i _
  exact ((signMatrix_commute_doubled (A i)).mul_right
    (signMatrix_commute_doubled (A i))).eq

theorem involution_isHermitian (A : ι → Matrix n n ℂ) : (involution A).IsHermitian :=
  compress_isHermitian (sourceEmbedding A) signMatrix_isHermitian

theorem involution_sq (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) :
    involution A * involution A = 1 :=
  compressed_involution (sourceEmbedding A) (embedding_isometry A) signMatrix_sq
    (projection_commute A hA)

theorem probe_posSemidef (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (i : ι) :
    (probe A i).PosSemidef := compress_posSemidef _ (spinAtom_posSemidef (hA i))

theorem probe_reconstruct (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (i : ι) :
    sourceEmbedding A * probe A i * (sourceEmbedding A)ᴴ = spinAtom (A i) :=
  krausReducedFamily_reconstruct (fun i => spinAtom (A i))
    (fun i => (spinAtom_posSemidef (hA i)).isHermitian) i

theorem probe_ne_zero (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (i : ι) (hi : A i ≠ 0) : probe A i ≠ 0 := by
  apply compression_nonzero (sourceEmbedding A) _ (probe_reconstruct A hA i)
  intro hz
  have hh := congrArg Matrix.toBlocks₁₁ hz
  exact hi (by simpa only [spinAtom, Matrix.toBlocks_fromBlocks₁₁] using hh)

theorem involution_commute_probe (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (i : ι) : Commute (involution A) (probe A i) :=
  compressed_commute (sourceEmbedding A) (embedding_isometry A) signMatrix_isHermitian
    (projection_commute A hA) (signMatrix_commute_doubled (A i))

theorem density_posDef (A : ι → Matrix n n ℂ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) : (density A S).PosDef :=
  compress_posDef (sourceEmbedding A) (embedding_isometry A) hS

theorem involution_commute_density (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) {S : Matrix (n ⊕ n) (n ⊕ n) ℂ}
    (hfixed : conjugate signMatrix S = S) : Commute (involution A) (density A S) :=
  compressed_commute (sourceEmbedding A) (embedding_isometry A) signMatrix_isHermitian
    (projection_commute A hA) (commute_of_conjugate_fixed signMatrix_sq hfixed)

theorem involution_commute_source (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    Commute (involution A) (compressedSource A β c S) :=
  compressed_commute (sourceEmbedding A) (embedding_isometry A) signMatrix_isHermitian
    (projection_commute A hA)
    (commute_of_conjugate_fixed signMatrix_sq (HigherRankKS.source_sign_output A β c S))

theorem transport_posDef (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) :
    (transport A ((1 : ℝ) / 2 ^ k) c S).PosDef :=
  transportOptimizer_posDef (density_posDef A hS) (compressedSource_posDef A hA hc hS k hk)

theorem transport_equation (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) :
    transport A ((1 : ℝ) / 2 ^ k) c S * compressedSource A ((1 : ℝ) / 2 ^ k) c S *
      transport A ((1 : ℝ) / 2 ^ k) c S = density A S :=
  transportOptimizer_solve (density_posDef A hS) (compressedSource_posDef A hA hc hS k hk)

theorem involution_commute_transport (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef)
    (hfixed : conjugate signMatrix S = S) (k : ℕ) (hk : 1 ≤ k) :
    Commute (involution A) (transport A ((1 : ℝ) / 2 ^ k) c S) :=
  commute_transport (involution_isHermitian A) (involution_sq A hA)
    (density_posDef A hS) (compressedSource_posDef A hA hc hS k hk)
    (involution_commute_density A hA hfixed) (involution_commute_source A hA _ c S)

theorem term_posSemidef (A : ι → Matrix n n ℂ) (β : ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) (i : ι) :
    (term A β S i).PosSemidef := compress_posSemidef _ (sourceTerm_posSemidef β (A i) hS)

theorem term_reconstruct (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) (i : ι) :
    sourceEmbedding A * term A ((1 : ℝ) / 2 ^ k) S i * (sourceEmbedding A)ᴴ =
      sourceTerm ((1 : ℝ) / 2 ^ k) (A i) S := by
  classical
  apply KSOwnerRetirement.support_reconstruct_of_le (sourceEmbedding A) (embedding_isometry A)
    (compressedSource A ((1 : ℝ) / 2 ^ k) (fun _ => 1) S)
    (sourceTerm_posSemidef _ _ hS.posSemidef)
  rw [compressedSource_reconstruct A hA (fun _ => zero_lt_one) hS k hk]
  simpa only [source, one_smul] using Finset.single_le_sum
    (fun j _ => (sourceTerm_posSemidef ((1 : ℝ) / 2 ^ k) (A j) hS.posSemidef).nonneg)
    (Finset.mem_univ i)

theorem term_ne_zero (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k)
    (i : ι) (hi : A i ≠ 0) : term A ((1 : ℝ) / 2 ^ k) S i ≠ 0 := by
  apply compression_nonzero (sourceEmbedding A) _ (term_reconstruct A hA hS k hk i)
  intro hz
  have ha : spinAtom (A i) = 0 := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [Matrix.zero_mulVec]
    exact (sourceTerm_mulVec_eq_zero_iff (hA i) hS k hk _).mp (by
      rw [hz, Matrix.zero_mulVec])
  have hh := congrArg Matrix.toBlocks₁₁ ha
  exact hi (by simpa only [spinAtom, Matrix.toBlocks_fromBlocks₁₁] using hh)

theorem compressedSource_eq_sum (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    compressedSource A β c S = ∑ i, c i • term A β S i := by
  simp only [compressedSource, source, term, compress, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem probe_pairing (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (i : ι) :
    realTrace (density A S * probe A i) = realTrace (spinAtom (A i) * S) := by
  rw [realTrace_mul_comm]
  have ht := KSSafeRetirement.realTrace_embedded_mul (sourceEmbedding A) (probe A i) S
  rw [probe_reconstruct A hA i] at ht
  exact ht.symm

theorem term_pairing (A : ι → Matrix n n ℂ) (β : ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (i : ι) :
    realTrace (Z * term A β S i) =
      realTrace ((sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) * sourceTerm β (A i) S) :=
  (KSSafeRetirement.realTrace_embedded_mul (sourceEmbedding A) Z _).symm

end HigherRankKS.SupportedSpin
