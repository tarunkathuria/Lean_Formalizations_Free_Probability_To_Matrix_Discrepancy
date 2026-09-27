import HigherRankKS.TwoFrames
import MatrixSpencer.KSSpinDrift

/-! Weighted Gram bounds for distinct measurement and preparation frames. -/

open Matrix MatrixSpencer MatrixSpencer.KSFisher MatrixSpencer.KSSpinDrift
open MatrixSpencer.KSWeightedProjection
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section
namespace HigherRankKS.TwoFrames

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

omit [DecidableEq ι] [DecidableEq n] in
theorem channel_transpose_mulVec (E F : ι → Matrix n n ℂ) (x : ι → ℝ) (i : ι) :
    ((channel E F)ᵀ *ᵥ x) i = realTrace (F i * synthesis E x) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, channel, synthesis,
    Matrix.mul_sum, Matrix.mul_smul, realTrace_sum, realTrace_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [realTrace_mul_comm (E j) (F i), mul_comm]

/-- The two-frame Fisher inequality retains the transpose: the channel
need not be self-adjoint. -/
theorem channel_fisher (E F : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).IsHermitian) (hF : ∀ i, (F i).PosSemidef)
    {μ r : ι → ℝ} (hμ : ∀ i, 0 ≤ μ i) (hr : ∀ i, 0 < r i)
    (htrace : ∀ i, realTrace (F i) = r i) :
    channel E F * Matrix.diagonal (fun i => μ i / r i) * (channel E F)ᵀ ≤
      physicalRealGram (frameSum F μ) E := by
  have hP : (frameSum F μ).IsHermitian :=
    synthesis_isHermitian F (fun i => (hF i).isHermitian) μ
  apply Matrix.le_iff.mpr
  refine ⟨(physicalGram_isHermitian hP E hE).sub ?_, fun x => ?_⟩
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
      using Matrix.isHermitian_conjTranspose_mul_mul (channel E F)ᵀ
        (Matrix.isHermitian_diagonal (fun i => μ i / r i))
  · simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
    have he := diagonal_sandwich_quadratic (channel E F)ᵀ (fun i => μ i / r i) x
    rw [Matrix.transpose_transpose] at he
    rw [he, physicalGram_quadratic]
    simpa only [channel_transpose_mulVec] using
      frame_weighted_cauchy F hF hμ hr htrace (synthesis_isHermitian E hE x)

def spinChannel (J : Matrix n n ℂ) (E F : ι → Matrix n n ℂ) : Matrix ι ι ℝ :=
  channel (fun i => J * E i) F

omit [DecidableEq ι] [DecidableEq n] in
theorem spinChannel_transpose_mulVec (J : Matrix n n ℂ)
    (E F : ι → Matrix n n ℂ) (x : ι → ℝ) (i : ι) :
    ((spinChannel J E F)ᵀ *ᵥ x) i = realTrace (F i * (J * synthesis E x)) := by
  rw [spinChannel, channel_transpose_mulVec]
  simp only [synthesis, Matrix.mul_sum, Matrix.mul_smul]

theorem spinChannel_fisher (E F : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).IsHermitian) (hF : ∀ i, (F i).PosSemidef)
    {μ r : ι → ℝ} (hμ : ∀ i, 0 ≤ μ i) (hr : ∀ i, 0 < r i)
    (htrace : ∀ i, realTrace (F i) = r i)
    {J : Matrix n n ℂ} (hJ : J.IsHermitian) (hJJ : J * J = 1)
    (hc : ∀ i, J * E i = E i * J) :
    spinChannel J E F * Matrix.diagonal (fun i => μ i / r i) *
      (spinChannel J E F)ᵀ ≤ physicalRealGram (frameSum F μ) E := by
  have hP : (frameSum F μ).IsHermitian :=
    synthesis_isHermitian F (fun i => (hF i).isHermitian) μ
  apply Matrix.le_iff.mpr
  refine ⟨(physicalGram_isHermitian hP E hE).sub ?_, fun x => ?_⟩
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
      using Matrix.isHermitian_conjTranspose_mul_mul (spinChannel J E F)ᵀ
        (Matrix.isHermitian_diagonal (fun i => μ i / r i))
  · simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
    have he := diagonal_sandwich_quadratic (spinChannel J E F)ᵀ
      (fun i => μ i / r i) x
    rw [Matrix.transpose_transpose] at he
    rw [he, physicalGram_quadratic]
    have hf := frame_weighted_cauchy F hF hμ hr htrace
      (spin_synthesis_isHermitian hJ E hE hc x)
    rw [spin_synthesis_square hJJ E hc x] at hf
    simpa only [spinChannel_transpose_mulVec] using hf

theorem two_frame_hs_bounds (E F : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).IsHermitian) (hF : ∀ i, (F i).PosSemidef)
    {μ r : ι → ℝ} (hμ : ∀ i, 0 < μ i) (hr : ∀ i, 0 < r i)
    (htrace : ∀ i, realTrace (F i) = r i)
    {J : Matrix n n ℂ} (hJ : J.IsHermitian) (hJJ : J * J = 1)
    (hc : ∀ i, J * E i = E i * J) (d z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1)
    (hdiag : ∀ i, realTrace (frameSum F μ * E i * E i) / (μ i / r i) ≤ d i) :
    let R := fun i => μ i / r i
    let Ew := weightedConjugate R (channel E F)ᵀ
    let Bw := weightedConjugate R (spinChannel J E F)ᵀ
    hsSq Ew ≤ ∑ i, d i ∧ hsSq Bw ≤ ∑ i, d i ∧
      hsSq (Bw - Ew * Matrix.diagonal z) ≤ 4 * ∑ i, d i := by
  dsimp only
  have hR : ∀ i, 0 < μ i / r i := fun i => div_pos (hμ i) (hr i)
  have hf := channel_fisher E F hE hF (fun i => (hμ i).le) hr htrace
  have hj := spinChannel_fisher E F hE hF (fun i => (hμ i).le) hr htrace hJ hJJ hc
  have he := weightedConjugate_hsSq_le (fun i => μ i / r i) d hR
    (channel E F)ᵀ (physicalRealGram (frameSum F μ) E)
    (by simpa only [Matrix.transpose_transpose] using hf) hdiag
  have hb := weightedConjugate_hsSq_le (fun i => μ i / r i) d hR
    (spinChannel J E F)ᵀ (physicalRealGram (frameSum F μ) E)
    (by simpa only [Matrix.transpose_transpose] using hj) hdiag
  refine ⟨he, hb, ?_⟩
  have hh := hsSq_sub_le (weightedConjugate (fun i => μ i / r i) (spinChannel J E F)ᵀ)
    (weightedConjugate (fun i => μ i / r i) (channel E F)ᵀ * Matrix.diagonal z)
  have hz' := hsSq_mul_diagonal_le z hz
    (weightedConjugate (fun i => μ i / r i) (channel E F)ᵀ)
  linarith

end HigherRankKS.TwoFrames
