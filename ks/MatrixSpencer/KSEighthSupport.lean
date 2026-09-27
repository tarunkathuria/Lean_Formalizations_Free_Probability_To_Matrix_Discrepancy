import MatrixSpencer.KSEighthBalanced
import MatrixSpencer.KSEndpointRetirement
import MatrixSpencer.KSSupportSymmetry

/-! Fixed live-atom support for the two-sign construction, with literal rank-one compression. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthSupport

variable {ι n m : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]
local instance supportCStar {s : Type*} [Fintype s] [DecidableEq s] : CStarAlgebra (Matrix s s ℂ) := {}

def embedding (v : ι → n → ℂ) := krausSupportEmbedding (fun i => KSRankOne.atom (v i))

theorem atom_supported (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0) (i : ι) :
    embedding v * ((embedding v)ᴴ * KSRankOne.atom (v i) * embedding v) * (embedding v)ᴴ =
      KSRankOne.atom (v i) := by
  let A := fun i => KSRankOne.atom (v i)
  have ha := KSRankOne.atom_posSemidef (v i)
  have hAH (j : ι) : (A j).IsHermitian := KSRankOne.atom_isHermitian (v j)
  have hle : A i * A i ≤ krausChannel A 1 := by
    have hs := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
      (Matrix.posSemidef_self_mul_conjTranspose (A j)).nonneg) (Finset.mem_univ i)
    simpa only [krausChannel, Matrix.mul_one, (hAH _).eq] using hs
  rw [← krausCompressedSource_reconstruct A Matrix.PosSemidef.one] at hle
  have hQ : (A i * A i).PosSemidef := by
    simpa only [(hAH i).eq] using
      Matrix.posSemidef_self_mul_conjTranspose (A i)
  have hr := KSOwnerRetirement.support_reconstruct_of_le (embedding v)
    (krausSupportEmbedding_isometry A) (krausCompressedSource A 1) hQ hle
  change embedding v * ((embedding v)ᴴ * (KSRankOne.atom (v i) * KSRankOne.atom (v i)) *
    embedding v) * (embedding v)ᴴ = KSRankOne.atom (v i) * KSRankOne.atom (v i) at hr
  rw [KSRankOne.atom_sq_real] at hr
  simp only [Matrix.mul_smul, Matrix.smul_mul] at hr
  exact smul_right_injective (Matrix n n ℂ) (KSRankOne.atom_realTrace_pos (hv i)).ne' hr

def compressedVector (v : ι → n → ℂ) (i : ι) := (embedding v)ᴴ *ᵥ v i

theorem compressed_atom (v : ι → n → ℂ) (i : ι) :
    (embedding v)ᴴ * KSRankOne.atom (v i) * embedding v =
      KSRankOne.atom (compressedVector v i) := by
  simpa only [Matrix.conjTranspose_conjTranspose] using
    KSEighthBalanced.atom_congruence (embedding v)ᴴ (v i)

theorem compressedVector_ne_zero (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0) (i : ι) :
    compressedVector v i ≠ 0 := by
  intro hz
  have he := compressed_atom v i
  rw [hz, KSRankOne.atom_zero] at he
  have hr := atom_supported v hv i
  rw [he, Matrix.mul_zero, Matrix.zero_mul] at hr
  exact (KSRankOne.atom_eq_zero_iff (v i)).not.mpr (hv i) hr.symm

/-- Trace-and-prepare sources commute with arbitrary support embeddings. -/
theorem source_lift (V : Matrix n m ℂ) (B : ι → Matrix m m ℂ)
    (c : ι → ℝ) (X : Matrix n n ℂ) :
    KSBalancedSpin.source (fun i => V * B i * Vᴴ) c X =
      V * KSBalancedSpin.source B c (Vᴴ * X * V) * Vᴴ := by
  simp only [KSBalancedSpin.source, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [KSSafeRetirement.realTrace_embedded_mul]

/-- The fixed live support contains every owner source, including coefficients
that vanish and arbitrary positive semidefinite test densities. -/
theorem source_reconstruct (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (c : ι → ℝ) (X : Matrix n n ℂ) :
    KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) c X =
      embedding v * KSBalancedSpin.source (fun i => KSRankOne.atom (compressedVector v i))
        c ((embedding v)ᴴ * X * embedding v) * (embedding v)ᴴ := by
  have hA : (fun i => KSRankOne.atom (v i)) =
      (fun i => embedding v * KSRankOne.atom (compressedVector v i) * (embedding v)ᴴ) := by
    funext i
    rw [← compressed_atom]
    exact (atom_supported v hv i).symm
  exact (congrArg (fun A : ι → Matrix n n ℂ => KSBalancedSpin.source A c X) hA).trans
    (source_lift (embedding v) (fun i => KSRankOne.atom (compressedVector v i)) c X)

theorem source_compress (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (c : ι → ℝ) (X : Matrix n n ℂ) :
    (embedding v)ᴴ * KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) c X * embedding v =
      KSBalancedSpin.source (fun i => KSRankOne.atom (compressedVector v i)) c
        ((embedding v)ᴴ * X * embedding v) := by
  have hV := krausSupportEmbedding_isometry (fun i => KSRankOne.atom (v i))
  change (embedding v)ᴴ * embedding v = 1 at hV
  rw [source_reconstruct v hv c X]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (embedding v)ᴴ (embedding v), hV, Matrix.one_mul, Matrix.mul_one]

theorem rankOne_source_eq_kraus (v : ι → n → ℂ) {X : Matrix n n ℂ}
    (hX : X.IsHermitian) :
    KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (fun _ => 1) X =
      krausChannel (fun i => KSRankOne.atom (v i)) X := by
  simp only [KSBalancedSpin.source, krausChannel, one_mul,
    (KSRankOne.atom_isHermitian (v _)).eq, KSRankOne.atom_sandwich_real _ hX]

/-- The unit-owner compressed source is the canonical positive compression. -/
theorem compressed_source_eq (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    KSBalancedSpin.source (fun i => KSRankOne.atom (compressedVector v i)) (fun _ => 1)
      ((embedding v)ᴴ * X * embedding v) =
      krausCompressedSource (fun i => KSRankOne.atom (v i)) X := by
  let V := embedding v
  have hV : Vᴴ * V = 1 := krausSupportEmbedding_isometry _
  have hr := source_reconstruct v hv (fun _ => 1) X
  have hc := congrArg (fun Y : Matrix n n ℂ => Vᴴ * Y * V) hr
  have he : Vᴴ * (V * KSBalancedSpin.source
      (fun i => KSRankOne.atom (compressedVector v i)) (fun _ => 1) (Vᴴ * X * V) * Vᴴ) * V =
      KSBalancedSpin.source (fun i => KSRankOne.atom (compressedVector v i)) (fun _ => 1)
        (Vᴴ * X * V) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul, Matrix.mul_one]
  change Vᴴ * KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (fun _ => 1) X * V =
    Vᴴ * (V * KSBalancedSpin.source (fun i => KSRankOne.atom (compressedVector v i))
      (fun _ => 1) (Vᴴ * X * V) * Vᴴ) * V at hc
  rw [he, rankOne_source_eq_kraus v hX] at hc
  rw [krausCompressedSource_eq_compression]
  exact hc.symm

/-- Coefficient monotonicity for the actual trace-and-prepare source. -/
theorem source_mono (B : ι → Matrix n n ℂ) (hB : ∀ i, (B i).PosSemidef)
    {X : Matrix n n ℂ} (hX : X.PosSemidef) {c c' : ι → ℝ}
    (hc : ∀ i, c i ≤ c' i) :
    KSBalancedSpin.source B c X ≤ KSBalancedSpin.source B c' X := by
  apply Matrix.le_iff.mpr
  have he : KSBalancedSpin.source B c' X - KSBalancedSpin.source B c X =
      ∑ i, ((c' i - c i) * realTrace (B i * X)) • B i := by
    simp only [KSBalancedSpin.source, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← sub_smul, sub_mul]
  rw [he]
  exact (Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    ((hB i).smul (mul_nonneg (sub_nonneg.mpr (hc i)) (realTrace_mul_nonneg (hB i) hX))).nonneg)).posSemidef

/-- Any live owner at least one is faithful on this fixed support. -/
theorem compressed_source_posDef (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    {X : Matrix n n ℂ} (hX : X.PosDef) (c : ι → ℝ) (hc : ∀ i, 1 ≤ c i) :
    (KSBalancedSpin.source (fun i => KSRankOne.atom (compressedVector v i)) c
      ((embedding v)ᴴ * X * embedding v)).PosDef := by
  have hbase : (KSBalancedSpin.source (fun i => KSRankOne.atom (compressedVector v i)) (fun _ => 1)
      ((embedding v)ᴴ * X * embedding v)).PosDef := by
    rw [compressed_source_eq v hv hX.isHermitian]
    exact krausCompressedSource_posDef _ hX
  have horder := source_mono (fun i => KSRankOne.atom (compressedVector v i))
    (fun i => KSRankOne.atom_posSemidef _) ((krausCompressedDensity_posDef _ hX).posSemidef) hc
  have hh := hbase.add_posSemidef (Matrix.le_iff.mp horder)
  change (KSBalancedSpin.source (fun i => KSRankOne.atom (compressedVector v i)) (fun _ => 1)
    ((embedding v)ᴴ * X * embedding v) +
    (KSBalancedSpin.source (fun i => KSRankOne.atom (compressedVector v i)) c ((embedding v)ᴴ * X * embedding v) -
    KSBalancedSpin.source (fun i => KSRankOne.atom (compressedVector v i)) (fun _ => 1)
    ((embedding v)ᴴ * X * embedding v))).PosDef at hh
  convert hh using 1
  congr 1
  abel

end MatrixSpencer.KSEighthSupport
