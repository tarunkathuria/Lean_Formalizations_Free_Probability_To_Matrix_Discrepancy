import AugmentedHigherRankKS.IndependentLegalResponse
import HigherRankKS.TwoFrameFisher

/-! The coefficient Gram bounds for distinct measurement, preparation and force frames. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS MatrixSpencer.KSFisher MatrixSpencer.KSSpinDrift
open MatrixSpencer.KSWeightedProjection
open scoped BigOperators MatrixOrder ComplexOrder
namespace AugmentedHigherRankKS.IndependentFrameGeometry
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
open HigherRankKS.TwoFrames

def features (E N : ι → Matrix n n ℂ) (R : ι → ℝ) : (ι ⊕ ι) → Matrix n n ℂ :=
  Sum.elim (fun i => (Real.sqrt (R i))⁻¹ • E i) (fun i => (Real.sqrt (R i))⁻¹ • N i)

theorem features_isHermitian (E N : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).IsHermitian) (hN : ∀ i, (N i).IsHermitian) (R : ι → ℝ)
    (j : ι ⊕ ι) : (features E N R j).IsHermitian := by
  cases j <;> simp only [features, Sum.elim_inl, Sum.elim_inr]
  · exact IsSelfAdjoint.smul (show IsSelfAdjoint ((Real.sqrt (R _))⁻¹) from rfl) (hE _)
  · exact IsSelfAdjoint.smul (show IsSelfAdjoint ((Real.sqrt (R _))⁻¹) from rfl) (hN _)

theorem features_synthesis (E N : ι → Matrix n n ℂ) (R : ι → ℝ) (v : ι ⊕ ι → ℝ) :
    synthesis (features E N R) v = IndependentLegalResponse.trial E N
      (unwhiten R (v ∘ Sum.inl)) (unwhiten R (v ∘ Sum.inr)) := by
  simp only [synthesis, features, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    smul_smul, unwhiten_apply, IndependentLegalResponse.trial, Function.comp_apply,
    div_eq_mul_inv]
  rw [add_comm]

theorem response_trace_le (E N : ι → Matrix n n ℂ) (P : Matrix n n ℂ)
    (R d : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hE : ∀ i, realTrace (P * E i * E i) / R i ≤ 4 * d i)
    (hN : ∀ i, realTrace (P * N i * N i) / R i ≤ 16 * d i) :
    realTrace (physicalRealGram P (features E N R)) ≤ 20 * ∑ i, d i := by
  change (∑ j, realTrace (P * features E N R j * features E N R j)) ≤ _
  rw [Fintype.sum_sum_type]
  have he : (∑ i, realTrace (P * features E N R (Sum.inl i) *
      features E N R (Sum.inl i))) ≤ 4 * ∑ i, d i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      change realTrace (P * ((Real.sqrt (R i))⁻¹ • E i) * ((Real.sqrt (R i))⁻¹ • E i)) ≤ _
      rw [weighted_scaled_energy P _ (hR i)]
      exact hE i
  have hn : (∑ i, realTrace (P * features E N R (Sum.inr i) *
      features E N R (Sum.inr i))) ≤ 16 * ∑ i, d i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      change realTrace (P * ((Real.sqrt (R i))⁻¹ • N i) * ((Real.sqrt (R i))⁻¹ • N i)) ≤ _
      rw [weighted_scaled_energy P _ (hR i)]
      exact hN i
  linarith

/-- Both weighted channels inherit the actual four- and sixteen-probe budgets. -/
theorem channel_hs_bounds (E F N : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).IsHermitian) (hF : ∀ i, (F i).PosSemidef)
    (hN : ∀ i, (N i).IsHermitian) {μ r : ι → ℝ}
    (hμ : ∀ i, 0 < μ i) (hr : ∀ i, 0 < r i) (htrace : ∀ i, realTrace (F i) = r i)
    (hEdiag : ∀ i, realTrace (frameSum F μ * E i * E i) / (μ i / r i) ≤ 4 * r i ^ 2)
    (hNdiag : ∀ i, realTrace (frameSum F μ * N i * N i) / (μ i / r i) ≤ 16 * r i ^ 2) :
    hsSq (weightedConjugate (fun i => μ i / r i) (channel E F)ᵀ) ≤ 4 * ∑ i, r i ^ 2 ∧
    hsSq (weightedConjugate (fun i => μ i / r i) (channel N F)ᵀ) ≤ 16 * ∑ i, r i ^ 2 := by
  have hR : ∀ i, 0 < μ i / r i := fun i => div_pos (hμ i) (hr i)
  have he := channel_fisher E F hE hF (fun i => (hμ i).le) hr htrace
  have hn := channel_fisher N F hN hF (fun i => (hμ i).le) hr htrace
  constructor
  · simpa only [← Finset.mul_sum] using
      weightedConjugate_hsSq_le (fun i => μ i / r i) (fun i => 4 * r i ^ 2) hR
        (channel E F)ᵀ (physicalRealGram (frameSum F μ) E)
        (by simpa only [Matrix.transpose_transpose] using he) hEdiag
  · simpa only [← Finset.mul_sum] using
      weightedConjugate_hsSq_le (fun i => μ i / r i) (fun i => 16 * r i ^ 2) hR
        (channel N F)ᵀ (physicalRealGram (frameSum F μ) N)
        (by simpa only [Matrix.transpose_transpose] using hn) hNdiag

/-- Removing the positive diagonal coordinate rescaling preserves the legal equation. -/
theorem unwhiten_legal (R : ι → ℝ) (hR : ∀ i, 0 < R i) (T B : Matrix ι ι ℝ)
    {v : ι ⊕ ι → ℝ}
    (hv : constraintMatrix (weightedConjugate R T) (weightedConjugate R B) *ᵥ v = 0) :
    (1 - T) *ᵥ unwhiten R (v ∘ Sum.inl) = B *ᵥ unwhiten R (v ∘ Sum.inr) := by
  have he := MatrixSpencer.KSSpinDrift.unwhiten_legal R hR T B (fun _ => 0)
    (x := v) (by simpa only [Matrix.diagonal_zero, Matrix.mul_zero, sub_zero] using hv)
  simpa only [Matrix.diagonal_zero, Matrix.mul_zero, sub_zero] using he

end AugmentedHigherRankKS.IndependentFrameGeometry
