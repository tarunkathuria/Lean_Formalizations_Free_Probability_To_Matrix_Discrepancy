import HigherRankKS.CarrierOrder
import MatrixSpencer.DyadicTraceInterpolation

/-!
# Elementary estimates for two positive frames

The measurement and preparation frames need not be equal. Positivity
gives their channel nonnegative entries, a positive fixed vector controls
its diagonal, and trace Cauchy–Schwarz supplies the weighted Gram estimate.
-/

open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section
namespace HigherRankKS.TwoFrames

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

def frameSum (F : ι → Matrix n n ℂ) (a : ι → ℝ) : Matrix n n ℂ :=
  ∑ i, a i • F i

def channel (E F : ι → Matrix n n ℂ) : Matrix ι ι ℝ :=
  fun i j => realTrace (E i * F j)

omit [Fintype ι] [DecidableEq ι] in
theorem channel_nonneg (E F : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).PosSemidef) (hF : ∀ i, (F i).PosSemidef) (i j : ι) :
    0 ≤ channel E F i j := realTrace_mul_nonneg (hE i) (hF j)

omit [DecidableEq ι] [DecidableEq n] in
theorem channel_fixed_vector (E F : ι → Matrix n n ℂ) (μ : ι → ℝ)
    (hpair : ∀ i, realTrace (E i * frameSum F μ) = μ i) :
    (channel E F).mulVec μ = μ := by
  funext i
  have h := hpair i
  simp only [frameSum, Matrix.mul_sum, Matrix.mul_smul, realTrace_sum, realTrace_smul] at h
  simpa only [Matrix.mulVec, dotProduct, channel, mul_comm] using h

omit [DecidableEq ι] in
theorem channel_diagonal_le_one (E F : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).PosSemidef) (hF : ∀ i, (F i).PosSemidef)
    {μ : ι → ℝ} (hμ : ∀ i, 0 < μ i)
    (hfixed : (channel E F).mulVec μ = μ) (i : ι) :
    channel E F i i ≤ 1 := by
  have hsum : channel E F i i * μ i ≤ ∑ j, channel E F i j * μ j :=
    Finset.single_le_sum
      (fun j _ => mul_nonneg (channel_nonneg E F hE hF i j) (hμ j).le)
      (Finset.mem_univ i)
  have h := congrFun hfixed i
  change ∑ j, channel E F i j * μ j = μ i at h
  rw [h] at hsum
  nlinarith [hμ i]

omit [DecidableEq ι] in
theorem frame_weighted_cauchy (F : ι → Matrix n n ℂ)
    (hF : ∀ i, (F i).PosSemidef)
    {μ r : ι → ℝ} (hμ : ∀ i, 0 ≤ μ i) (hr : ∀ i, 0 < r i)
    (htrace : ∀ i, realTrace (F i) = r i)
    {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    ∑ i, μ i / r i * realTrace (F i * Y) ^ 2 ≤
      realTrace (frameSum F μ * (Y * Y)) := by
  calc
    _ ≤ ∑ i, μ i * realTrace (F i * (Y * Y)) := by
      apply Finset.sum_le_sum
      intro i _
      have h := DyadicTraceInterpolation.weightedTrace_sq_le (hF i) hY
      rw [htrace i] at h
      calc
        _ ≤ μ i / r i * (r i * realTrace (F i * (Y * Y))) :=
          mul_le_mul_of_nonneg_left h (div_nonneg (hμ i) (hr i).le)
        _ = μ i * realTrace (F i * (Y * Y)) := by
          rw [← mul_assoc, div_mul_cancel₀ _ (hr i).ne']
    _ = _ := by
      simp only [frameSum, Matrix.sum_mul, Matrix.smul_mul, realTrace_sum, realTrace_smul]

/-- The two spin diagonal trace pairings are bounded by the carrier pairing;
the omitted cross terms are positive. -/
theorem cross_spin_trace_le {M₁ M₂ Q₁ Q₂ : Matrix n n ℂ}
    (hM₁ : M₁.PosSemidef) (hM₂ : M₂.PosSemidef)
    (hQ₁ : Q₁.PosSemidef) (hQ₂ : Q₂.PosSemidef)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    realTrace (M₁ * Q₁) + realTrace (M₂ * Q₂) ≤
      realTrace (carrierPower β (M₁ + M₂) * (Q₁ + Q₂)) := by
  apply le_trans _ (trace_pairing_le_carrierPower (hM₁.add hM₂) (hQ₁.add hQ₂) hβ hβ1)
  simp only [Matrix.add_mul, Matrix.mul_add, realTrace_add]
  linarith [realTrace_mul_nonneg hM₁ hQ₂, realTrace_mul_nonneg hM₂ hQ₁]

end HigherRankKS.TwoFrames
