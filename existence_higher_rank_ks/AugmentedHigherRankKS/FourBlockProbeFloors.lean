import AugmentedHigherRankKS.FourBlockQuantitativeFloors
import AugmentedHigherRankKS.FourBlockDomination
import AugmentedHigherRankKS.FourBlockFrameBridge
import MatrixSpencer.KSObjectiveUpper

/-! Quantitative owner floors use whole-atom norms, not minimum positive eigenvalues. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS Filter Set
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance probeFloorCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}

theorem realTrace_spinAtom (A : Matrix n n ℂ) : realTrace (spinAtom A) = 4 * realTrace A := by
  simp [spinAtom, HigherRankKS.spinAtom, realTrace, Matrix.trace, Matrix.diag, Fintype.sum_sum_type]
  ring

theorem marginal_floor {S : Matrix (FourSpin n) (FourSpin n) ℂ} {s : ℝ}
    (hs : 0 ≤ s) (hfloor : s • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ S) :
    s • (1 : Matrix n n ℂ) ≤ marginal S := by
  have hh := marginal_posSemidef (Matrix.le_iff.mp hfloor)
  have he : marginal (S-s • (1 : Matrix (FourSpin n) (FourSpin n) ℂ)) =
      marginal S - (4*s) • (1 : Matrix n n ℂ) := by
    ext i j
    simp [marginal, HigherRankKS.marginal, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.one_apply]
    split_ifs <;> ring
  rw [he] at hh
  have ht : s • (1 : Matrix n n ℂ) ≤ (4*s) • (1 : Matrix n n ℂ) := by
    exact smul_le_smul_of_nonneg_right (by linarith) Matrix.PosSemidef.one.nonneg
  exact ht.trans (Matrix.le_iff.mpr hh)

theorem carrierMass_floor (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} {s : ℝ} (hs : 0 ≤ s)
    (hfloor : s • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ S) (i : ι) :
    s * realTrace (A i) ≤ BalancedFrames.carrierMass (SupportedSpin.probe A) (SupportedSpin.density A S) i := by
  change _ ≤ realTrace (SupportedSpin.density A S * SupportedSpin.probe A i)
  rw [SupportedSpin.probe_pairing A hA]
  have hh := realTrace_mul_mono (spinAtom_posSemidef (hA i)) hfloor
  rw [Matrix.mul_smul, Matrix.mul_one, realTrace_smul, realTrace_spinAtom] at hh
  have ht := mul_nonneg hs (realTrace_nonneg (hA i))
  linarith

theorem sourceTerm_trace_floor {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef)
    {s β : ℝ} (hs : 0 ≤ s) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hfloor : s • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ S) :
    4*s * realTrace (A*A) ≤ realTrace (sourceTerm β A S) := by
  have hf := marginal_floor hs hfloor
  have hc := (Matrix.le_iff.mp hf).conjTranspose_mul_mul_same A
  have hp : s • (A*A) ≤ A * marginal S * A := by
    apply Matrix.le_iff.mpr
    convert hc using 1
    simp only [hA.isHermitian.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one]
  have ht := realTrace_mul_mono (Matrix.PosSemidef.one : (1 : Matrix n n ℂ).PosSemidef) hp
  simp only [Matrix.one_mul, realTrace_smul] at ht
  have hsrc := realTrace_mul_mono (Matrix.PosSemidef.one : (1 : Matrix (FourSpin n) (FourSpin n) ℂ).PosSemidef) (sourceTerm_ge_carrier hA hS hβ hβ1)
  simp only [Matrix.one_mul] at hsrc
  have he : spinAtom A * spinAtom (marginal S) * spinAtom A = spinAtom (A * marginal S * A) := by
    simp only [spinAtom, HigherRankKS.spinAtom, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [he, realTrace_spinAtom] at hsrc
  linarith

theorem supportedTerm_trace (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) (i : ι) :
    realTrace (SupportedSpin.term A ((1:ℝ)/2^k) S i) = realTrace (sourceTerm ((1:ℝ)/2^k) (A i) S) := by
  have hh := KSSafeRetirement.realTrace_embedded_mul (sourceEmbedding A)
    (SupportedSpin.term A ((1:ℝ)/2^k) S i) (1 : Matrix (FourSpin n) (FourSpin n) ℂ)
  rw [SupportedSpin.term_reconstruct A hA hS k hk i] at hh
  simpa only [Matrix.mul_one, SupportedSpin.embedding_isometry, Matrix.one_mul] using hh.symm

theorem transportMass_floor (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef)
    {s B : ℝ} (hs : 0 ≤ s) (hB : 0 < B)
    (hfloor : s • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ S)
    (hz : B⁻¹ • (1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) ≤
      SupportedSpin.transport A ((1:ℝ)/2^k) c S) (i : ι) :
    4*s*realTrace (A i*A i)/B ≤ BalancedFrames.transportMass
      (SupportedSpin.term A ((1:ℝ)/2^k) S) (SupportedSpin.transport A ((1:ℝ)/2^k) c S) i := by
  have ht := realTrace_mul_mono (SupportedSpin.term_posSemidef A ((1:ℝ)/2^k) hS.posSemidef i) hz
  rw [Matrix.mul_smul, Matrix.mul_one, realTrace_smul, supportedTerm_trace A hA hS k hk i] at ht
  have hb : (1:ℝ)/2^k ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hf := sourceTerm_trace_floor (hA i) hS.posSemidef hs (by positivity : 0 ≤ (1:ℝ)/2^k) hb hfloor
  change _ ≤ realTrace (SupportedSpin.transport A ((1:ℝ)/2^k) c S * SupportedSpin.term A ((1:ℝ)/2^k) S i)
  rw [realTrace_mul_comm (SupportedSpin.transport A ((1:ℝ)/2^k) c S)]
  have hscaled := mul_le_mul_of_nonneg_left hf (inv_nonneg.mpr hB.le)
  exact (by simpa only [div_eq_mul_inv, mul_comm] using hscaled.trans ht)

theorem carrierMass_floor_of_norm (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} {s η : ℝ} (hs : 0 ≤ s)
    (hfloor : s • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ S)
    (i : ι) (hi : η ≤ ‖A i‖) :
    s*η ≤ BalancedFrames.carrierMass (SupportedSpin.probe A) (SupportedSpin.density A S) i :=
  (mul_le_mul_of_nonneg_left (hi.trans (posSemidef_norm_le_realTrace (hA i))) hs).trans
    (carrierMass_floor A hA hs hfloor i)

theorem transportMass_floor_of_norm (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef)
    {s B η : ℝ} (hs : 0 ≤ s) (hB : 0 < B) (hη : 0 ≤ η)
    (hfloor : s • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ S)
    (hz : B⁻¹ • (1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) ≤
      SupportedSpin.transport A ((1:ℝ)/2^k) c S) (i : ι) (hi : η ≤ ‖A i‖) :
    4*s*η^2/B ≤ BalancedFrames.transportMass
      (SupportedSpin.term A ((1:ℝ)/2^k) S) (SupportedSpin.transport A ((1:ℝ)/2^k) c S) i := by
  have hh : η^2 ≤ realTrace (A i*A i) :=
    (sq_le_sq₀ hη (norm_nonneg _) |>.mpr hi).trans (KSObjectiveUpper.norm_sq_le_trace_square (hA i).isHermitian)
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by positivity)) hB.le).trans
    (transportMass_floor A hA k hk c hS hs hB hfloor hz i)
end AugmentedHigherRankKS
