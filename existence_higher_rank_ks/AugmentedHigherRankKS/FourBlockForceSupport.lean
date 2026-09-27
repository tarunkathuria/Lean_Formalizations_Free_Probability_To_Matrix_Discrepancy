import AugmentedHigherRankKS.FourBlockDomination
import AugmentedHigherRankKS.FourBlockSupportedSource
import HigherRankKS.SupportedDiagonal

/-! The actual four-center forces are supported on the original atom ranges. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS KSSupportSymmetry
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance forceSupportCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}

theorem scalar_four_blocks_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (Matrix.fromBlocks (Matrix.fromBlocks (a • A) 0 0 (b • A)) 0 0
      (Matrix.fromBlocks (c • A) 0 0 (d • A))).PosSemidef :=
  posSemidef_fromBlocks_diagonal
    (posSemidef_fromBlocks_diagonal (hA.smul ha) (hA.smul hb))
    (posSemidef_fromBlocks_diagonal (hA.smul hc) (hA.smul hd))

theorem force_order_bounds {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {x : ℝ} (hx : |x| ≤ 1) :
    -(2 : ℝ) • spinAtom A ≤ forceAtom x A ∧ forceAtom x A ≤ (2 : ℝ) • spinAtom A := by
  have hx' := abs_le.mp hx
  have hp := scalar_four_blocks_posSemidef hA (by norm_num : (0 : ℝ) ≤ 3)
    (by norm_num : (0 : ℝ) ≤ 1) (show 0 ≤ 2 - 2 * x by linarith)
    (show 0 ≤ 2 + 2 * x by linarith)
  have hm := scalar_four_blocks_posSemidef hA (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 3) (show 0 ≤ 2 + 2 * x by linarith)
    (show 0 ≤ 2 - 2 * x by linarith)
  constructor
  · apply sub_nonneg.mp
    convert hp.nonneg using 1
    ext (i | i) (j | j) <;> cases i <;> cases j <;>
      simp [spinAtom, HigherRankKS.spinAtom, forceAtom, signedLift] <;> ring
  · apply sub_nonneg.mp
    convert hm.nonneg using 1
    ext (i | i) (j | j) <;> cases i <;> cases j <;>
      simp [spinAtom, HigherRankKS.spinAtom, forceAtom, signedLift] <;> ring

namespace SupportedSpin
variable {ι : Type*} [Fintype ι]

def force (A : ι → Matrix n n ℂ) (x : ι → ℝ) (i : ι) :
    Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ :=
  compress (sourceEmbedding A) (forceAtom (x i) (A i))

theorem force_isHermitian (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (x : ι → ℝ) (i : ι) : (force A x i).IsHermitian :=
  compress_isHermitian _ (forceAtom_isHermitian _ (hA i).isHermitian)

theorem force_reconstruct (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) (i : ι) :
    sourceEmbedding A * force A x i * (sourceEmbedding A)ᴴ = forceAtom (x i) (A i) := by
  have hb := force_order_bounds (hA i) (hx i)
  have hp : ((2 : ℝ) • spinAtom (A i) + forceAtom (x i) (A i)).PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    have hh := sub_nonneg.mpr hb.1
    simpa only [neg_smul, sub_neg_eq_add, add_comm] using hh
  have hle : (2 : ℝ) • spinAtom (A i) + forceAtom (x i) (A i) ≤
      sourceEmbedding A * ((4 : ℝ) • probe A i) * (sourceEmbedding A)ᴴ := by
    rw [Matrix.mul_smul, Matrix.smul_mul, probe_reconstruct A hA i]
    have hh := add_le_add_left hb.2 ((2 : ℝ) • spinAtom (A i))
    simpa only [← add_smul, show (2 : ℝ) + 2 = 4 by norm_num] using hh
  have he := KSOwnerRetirement.support_reconstruct_of_le (sourceEmbedding A)
    (embedding_isometry A) ((4 : ℝ) • probe A i) hp hle
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul] at he
  change (2 : ℝ) • (sourceEmbedding A * probe A i * (sourceEmbedding A)ᴴ) +
    sourceEmbedding A * force A x i * (sourceEmbedding A)ᴴ =
    (2 : ℝ) • spinAtom (A i) + forceAtom (x i) (A i) at he
  rw [probe_reconstruct A hA i] at he
  exact add_left_cancel he

theorem force_pairing (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (X : Matrix (FourSpin n) (FourSpin n) ℂ) (i : ι) :
    realTrace (forceAtom (x i) (A i) * X) = realTrace (force A x i * density A X) := by
  have h := KSSafeRetirement.realTrace_embedded_mul (sourceEmbedding A) (force A x i) X
  rw [force_reconstruct A hA x hx i] at h
  exact h

/-- Actual supported ordinary-probe energy, with the coarse factor four. -/
theorem actual_supported_probe_bound (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef)
    {Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ} (hZ : Z.PosSemidef)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (i : ι) :
    realTrace (density A S * probe A i * Z * probe A i) ≤
      4 * realTrace (Z * term A β S i) := by
  rw [density, HigherRankKS.compressed_quadratic_trace (sourceEmbedding A) (embedding_isometry A)
    S (spinAtom (A i)) (probe A i) Z (probe_reconstruct A hA i)]
  have h := realTrace_mul_mono (hZ.mul_mul_conjTranspose_same (sourceEmbedding A))
    (atom_density_atom_le_source (hA i) hS hβ hβ1)
  rw [Matrix.mul_smul, realTrace_smul, ← term_pairing] at h
  convert h using 1
  simpa only [Matrix.mul_assoc] using realTrace_mul_comm (S * spinAtom (A i))
    ((sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) * spinAtom (A i))

/-- Actual supported four-center force energy, with the coarse factor sixteen. -/
theorem actual_supported_force_bound (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef)
    {Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ} (hZ : Z.PosSemidef)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (i : ι) :
    realTrace (density A S * force A x i * Z * force A x i) ≤
      16 * realTrace (Z * term A β S i) := by
  rw [density, HigherRankKS.compressed_quadratic_trace (sourceEmbedding A) (embedding_isometry A)
    S (forceAtom (x i) (A i)) (force A x i) Z (force_reconstruct A hA x hx i)]
  have h := realTrace_mul_mono (hZ.mul_mul_conjTranspose_same (sourceEmbedding A))
    (force_density_force_le_source (hA i) hS hβ hβ1 (hx i))
  rw [Matrix.mul_smul, realTrace_smul, ← term_pairing] at h
  convert h using 1
  simpa only [Matrix.mul_assoc] using realTrace_mul_comm (S * forceAtom (x i) (A i))
    ((sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) * forceAtom (x i) (A i))

end SupportedSpin
end AugmentedHigherRankKS
