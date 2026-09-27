import HigherRankKS.TwoFrameFisher
import HigherRankKS.ProjectionAveraging

/-!
# A negative legal direction for two concrete positive frames

The coefficient covariance and response Gram are constructed explicitly.
The frame identities and diagonal cap are mathematical hypotheses to be
verified for the balanced source; they are not assumptions of the final
signing theorem.
-/

open Matrix MatrixSpencer MatrixSpencer.KSFisher MatrixSpencer.KSSpinDrift
open MatrixSpencer.KSWeightedProjection
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section
namespace HigherRankKS.TwoFrames

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype n] [DecidableEq n]

theorem exists_negative_frame_direction (E F : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).PosSemidef) (hF : ∀ i, (F i).PosSemidef)
    {μ r : ι → ℝ} (hμ : ∀ i, 0 < μ i) (hr : ∀ i, 0 < r i)
    (htrace : ∀ i, realTrace (F i) = r i)
    (hpair : ∀ i, realTrace (E i * frameSum F μ) = μ i)
    {J : Matrix n n ℂ} (hJ : J.IsHermitian) (hJJ : J * J = 1)
    (hc : ∀ i, J * E i = E i * J)
    {β L : ℝ} (hβ : 0 < β) (hβhalf : β ≤ 1 / 2)
    (hL : 0 ≤ L) (hLcap : L ≤ 1 / (2 * β))
    (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1)
    (hcap : ∀ i, r i ^ 2 ≤ L / (100 / β))
    (hdiag : ∀ i, realTrace (frameSum F μ * E i * E i) / (μ i / r i) ≤ r i ^ 2) :
    let R := fun i => μ i / r i
    let u := 100 / β
    ∃ ω y : ι → ℝ, y ≠ 0 ∧
      (1 - (channel E F)ᵀ) *ᵥ ω =
        ((spinChannel J E F)ᵀ - (channel E F)ᵀ * Matrix.diagonal z) *ᵥ y ∧
      legalUpper ((1 / β) • frameSum F μ) J E R
        (fun i => r i ^ 2 + (2 / u) * (z i) ^ 2) z u ω y < 0 := by
  dsimp only
  let R := fun i => μ i / r i
  let d := fun i => r i ^ 2
  let h := ∑ i, d i
  let P := frameSum F μ
  let Ew := weightedConjugate R (channel E F)ᵀ
  let Bw := weightedConjugate R (spinChannel J E F)ᵀ
  let Fw := Bw - Ew * Matrix.diagonal z
  let H := physicalRealGram P (jointFeatures E J R z)
  have hR : ∀ i, 0 < R i := fun i => div_pos (hμ i) (hr i)
  have hP : P.PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    exact Finset.sum_nonneg (fun i _ => ((hF i).smul (hμ i).le).nonneg)
  have hh : 0 < h := by
    apply Finset.sum_pos (fun i _ => sq_pos_of_pos (hr i)) Finset.univ_nonempty
  have hb := two_frame_hs_bounds E F (fun i => (hE i).isHermitian) hF
    hμ hr htrace hJ hJJ hc d z hz hdiag
  have hH : H.PosSemidef := physicalGram_posSemidef hP _
    (jointFeatures_isHermitian E (fun i => (hE i).isHermitian) hJ hc R z)
  have ht : realTrace H ≤ 5 * h := joint_response_trace_le E
    (fun i => (hE i).isHermitian) hP hJ hJJ hc R z d hR hz hdiag
  have hfixed := channel_fixed_vector E F μ hpair
  have hdE : ∀ i, 0 ≤ Ew i i ∧ Ew i i ≤ 1 := by
    intro i
    rw [show Ew i i = channel E F i i by
      simp only [Ew, weightedConjugate_diagonal R hR, Matrix.transpose_apply]]
    exact ⟨channel_nonneg E F hE hF i i,
      channel_diagonal_le_one E F hE hF hμ hfixed i⟩
  have hn := ProjectionAveraging.higher_averaged_negative Ew Bw d z H hh hL hβ
    hβhalf hLcap hcap rfl hz hb.1 hb.2.1 hb.2.2 hdE hH ht
  rw [ProjectionAveraging.higherAveraged_eq_averagedUpper] at hn
  obtain ⟨x, hx, hqx⟩ := exists_negative_kernel_direction Ew Fw
    (fun i => d i + (2 / (100 / β)) * (z i) ^ 2) z ((1 / β) • H) (100 / β) hn
  have hu : 0 < 100 / β := div_pos (by norm_num) hβ
  have hscaled : ((1 / β) • H).PosSemidef := hH.smul (by positivity : 0 ≤ 1 / β)
  have hv := negative_kernel_bottom_ne_zero _ _ hscaled hu hqx
  have hFw : Fw = weightedConjugate R
      ((spinChannel J E F)ᵀ - (channel E F)ᵀ * Matrix.diagonal z) := by
    rw [weightedConjugate_sub, weightedConjugate_mul_diagonal]
  rw [hFw] at hx
  refine ⟨unwhiten R (x ∘ Sum.inl), unwhiten R (x ∘ Sum.inr),
    unwhiten_ne_zero R hR hv,
    unwhiten_legal R hR (channel E F)ᵀ (spinChannel J E F)ᵀ z hx, ?_⟩
  have hgram : (1 / β) • H =
      physicalRealGram ((1 / β) • P) (jointFeatures E J R z) := by
    ext i j
    change (1 / β) * realTrace (P * jointFeatures E J R z i * jointFeatures E J R z j) =
      realTrace (((1 / β) • P) * jointFeatures E J R z i * jointFeatures E J R z j)
    simp only [Matrix.smul_mul, realTrace_smul]
  rw [hgram, upperMatrix_eq_legalUpper _ _ _ _ _ _ hR] at hqx
  exact hqx

end HigherRankKS.TwoFrames
