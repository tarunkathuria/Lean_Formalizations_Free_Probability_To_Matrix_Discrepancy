import AugmentedHigherRankKS.IndependentFrameGeometry
import AugmentedHigherRankKS.ConstrainedAveraging

/-! A negative legal direction obtained by averaging the concrete two-frame Gram. -/
noncomputable section
open Matrix MatrixSpencer MatrixSpencer.KSFisher MatrixSpencer.KSSpinDrift
open MatrixSpencer.KSWeightedProjection
open scoped BigOperators MatrixOrder ComplexOrder
namespace AugmentedHigherRankKS.IndependentFrameDirection
open HigherRankKS.TwoFrames IndependentFrameGeometry
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype n] [DecidableEq n]

theorem exists_direction (E F N : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).PosSemidef) (hF : ∀ i, (F i).PosSemidef)
    (hN : ∀ i, (N i).IsHermitian) {μ r : ι → ℝ}
    (hμ : ∀ i, 0 < μ i) (hr : ∀ i, 0 < r i)
    (htrace : ∀ i, realTrace (F i) = r i)
    (hpair : ∀ i, realTrace (E i * frameSum F μ) = μ i)
    (hEdiag : ∀ i, realTrace (frameSum F μ * E i * E i) / (μ i / r i) ≤ 4 * r i ^ 2)
    (hNdiag : ∀ i, realTrace (frameSum F μ * N i * N i) / (μ i / r i) ≤ 16 * r i ^ 2)
    (hcap : ∀ i, r i ^ 2 ≤ 1 / 48)
    {β σ a : ℝ} (hβ : 0 < β) (hσ : 4 * β / 3 ≤ σ) (ha : 60 / β ≤ a)
    (z : ι → ℝ) :
    ∃ ω y : ι → ℝ, y ≠ 0 ∧
      (1 - (channel E F)ᵀ) *ᵥ ω = (channel N F)ᵀ *ᵥ y ∧
      (∑ i, z i * y i) = 0 ∧
      realTrace (frameSum F μ * (IndependentLegalResponse.trial E N ω y *
        IndependentLegalResponse.trial E N ω y)) / σ -
        a * ∑ i, μ i * r i * y i ^ 2 < 0 := by
  let R := fun i => μ i / r i
  let P := frameSum F μ
  let Ew := weightedConjugate R (channel E F)ᵀ
  let Fw := weightedConjugate R (channel N F)ᵀ
  let H := physicalRealGram P (features E N R)
  have hR : ∀ i, 0 < R i := fun i => div_pos (hμ i) (hr i)
  have hP : P.PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    exact Finset.sum_nonneg (fun i _ => ((hF i).smul (hμ i).le).nonneg)
  have hhs := channel_hs_bounds E F N (fun i => (hE i).isHermitian) hF hN
    hμ hr htrace hEdiag hNdiag
  have hμne : μ ≠ 0 := by
    intro he
    have hp := hμ (Classical.arbitrary ι)
    rw [he] at hp
    exact (lt_irrefl 0) hp
  have hfixed := channel_fixed_vector E F μ hpair
  have hlarge := ConstrainedAveraging.weighted_transpose_hsSq_ge_one R hR
    (channel E F) hμne hfixed
  have hh : 1 / 4 ≤ ∑ i, r i ^ 2 := by linarith [hhs.1]
  have hH : H.PosSemidef := physicalGram_posSemidef hP _
    (features_isHermitian E N (fun i => (hE i).isHermitian) hN R)
  have ht : realTrace H ≤ 20 * ∑ i, r i ^ 2 :=
    response_trace_le E N P R (fun i => r i ^ 2) hR hEdiag hNdiag
  obtain ⟨v, hv, hz, hvne, hneg⟩ := ConstrainedAveraging.exists_negative_legal
    Ew Fw (fun i => z i / Real.sqrt (R i)) (fun i => r i ^ 2)
    hh hcap rfl hhs.1 hhs.2 hH ht hβ hσ ha
  let ω := unwhiten R (v ∘ Sum.inl)
  let y := unwhiten R (v ∘ Sum.inr)
  refine ⟨ω, y, unwhiten_ne_zero R hR hvne,
    IndependentFrameGeometry.unwhiten_legal R hR _ _ hv, ?_, ?_⟩
  · simpa only [y, unwhiten_apply, Function.comp_apply, div_mul_eq_mul_div,
      mul_div_assoc] using hz
  · rw [ConstrainedAveraging.upper_quadratic, physicalGram_quadratic,
      features_synthesis] at hneg
    have hd : (v ∘ Sum.inr) ⬝ᵥ (Matrix.diagonal (fun i => r i ^ 2) *ᵥ (v ∘ Sum.inr)) =
        ∑ i, μ i * r i * y i ^ 2 := by
      simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [y]
      rw [unwhiten_apply, div_pow, Real.sq_sqrt (hR i).le]
      simp only [Function.comp_apply]
      dsimp only [R]
      field_simp [(hr i).ne', (hμ i).ne']
    rw [hd] at hneg
    exact hneg

end AugmentedHigherRankKS.IndependentFrameDirection
