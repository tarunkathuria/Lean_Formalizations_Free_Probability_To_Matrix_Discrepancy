import AugmentedHigherRankKS.EpochPotential
import HigherRankKS.SourceBudget
import MatrixSpencer.SignedLift

/-! Initial rank-sensitive reserve budget and control of both actual centers. -/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace AugmentedHigherRankKS

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance initialCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}

theorem realTrace_sourceTerm (β : ℝ) (A : Matrix n n ℂ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) :
    realTrace (sourceTerm β A S) = 4 * realTrace (sourceBlock β A S) := by
  simp [sourceTerm, sourceBlock, HigherRankKS.sourceTerm,
    HigherRankKS.spinDuplicateCLM, realTrace, Matrix.trace, Matrix.diag,
    Fintype.sum_sum_type]
  ring

theorem sum_carrier_trace_le_mass (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) {b : ℝ}
    (hsum : ∑ i, A i ≤ b • (1 : Matrix n n ℂ))
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S ∈ densitySet) :
    ∑ i, realTrace (HigherRankKS.carrier (A i) (HigherRankKS.marginal S)) ≤ b := by
  have h := realTrace_mul_mono (marginal_posSemidef hS.1) hsum
  rw [Matrix.mul_smul, Matrix.mul_one, realTrace_smul] at h
  have ht : realTrace (marginal S) = 1 := by
    rw [marginal, HigherRankKS.realTrace_marginal,
      HigherRankKS.realTrace_marginal, hS.2]
  rw [ht, mul_one] at h
  simpa only [HigherRankKS.realTrace_carrier (hA _), marginal,
    Matrix.mul_sum, realTrace_sum, realTrace_mul_comm] using h

theorem source_trace_le_mass (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) {b : ℝ}
    (hsum : ∑ i, A i ≤ b • (1 : Matrix n n ℂ))
    {ε : ℝ} (hε : 0 ≤ ε) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {c : ι → ℝ} {L : ℝ} (hL : 0 ≤ L) (hcap : ∀ i, c i ≤ L)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S ∈ densitySet) :
    realTrace (source A β c S) ≤ 4 * L * ε * (r : ℝ) ^ β * b := by
  have hp : 0 ≤ (r : ℝ) ^ β := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    realTrace (source A β c S) =
        ∑ i, c i * (4 * realTrace (sourceBlock β (A i) S)) := by
      simp [source, realTrace_sourceTerm]
    _ ≤ ∑ i, L * (4 * (ε * ((r : ℝ) ^ β *
        realTrace (HigherRankKS.carrier (A i) (HigherRankKS.marginal S))))) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul (hcap i)
        (mul_le_mul_of_nonneg_left
          (HigherRankKS.sourceBlock_trace_le (hA i) hε (hN i)
            (HigherRankKS.marginal_posSemidef hS.1) hβ hβ1 (hr i)) (by norm_num))
        (mul_nonneg (by norm_num)
          (realTrace_nonneg (HigherRankKS.sourceBlock_posSemidef β (A i)
            (HigherRankKS.marginal_posSemidef hS.1)))) hL
    _ = (4 * L * ε * (r : ℝ) ^ β) *
        ∑ i, realTrace (HigherRankKS.carrier (A i) (HigherRankKS.marginal S)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (4 * L * ε * (r : ℝ) ^ β) * b :=
      mul_le_mul_of_nonneg_left (sum_carrier_trace_le_mass A hA hsum hS) (by positivity)

theorem potential_zero_le_source_budget [Nonempty n]
    (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {B θ : ℝ} (hθ : 0 ≤ θ)
    (hbudget : ∀ S ∈ densitySet, realTrace (source A β c S) ≤ B) :
    potential 0 A β c θ ≤ 2 * Real.sqrt B +
      2 * θ * Real.sqrt (Fintype.card (FourSpin n) : ℝ) := by
  obtain ⟨S, hS, hmax⟩ := exists_optimizer 0 A hβ hβ1 hc θ
  rw [potential_eq_of_optimizer 0 A β c θ hS hmax]
  have hf := fidelity_le_sqrt_trace_mul hS.1 (source_posSemidef A β hc hS.1)
  rw [hS.2, one_mul] at hf
  have hf' := hf.trans (Real.sqrt_le_sqrt (hbudget S hS))
  have hr := mul_le_mul_of_nonneg_left (density_trace_sqrt_le_sqrt_card hS)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hθ)
  simp only [objective, Matrix.zero_mul, realTrace_zero, zero_add]
  linarith

theorem left_center_norm_le_potential [Nonempty n]
    {H K : Matrix n n ℂ} (hH : H.IsHermitian) (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 ≤ θ) :
    ‖H‖ ≤ potential (augmentedCenter H K) A β c θ := by
  obtain ⟨S, hS, hval⟩ := exists_signedLift_density_norm hH
  have h := trace_center_le_potential (augmentedCenter H K) A hβ hβ1 hc hθ
    (leftDensity_mem hS)
  have heq : realTrace (augmentedCenter H K * leftDensity S) =
      realTrace (signedLift H * S) := by
    simp [augmentedCenter, leftDensity, Matrix.fromBlocks_multiply, realTrace,
      Matrix.trace, Matrix.diag, Fintype.sum_sum_type]
  rwa [heq, hval] at h

theorem right_center_norm_le_potential [Nonempty n]
    {H K : Matrix n n ℂ} (hK : K.IsHermitian) (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 ≤ θ) :
    ‖K‖ ≤ potential (augmentedCenter H K) A β c θ := by
  obtain ⟨S, hS, hval⟩ := exists_signedLift_density_norm hK
  have h := trace_center_le_potential (augmentedCenter H K) A hβ hβ1 hc hθ
    (rightDensity_mem hS)
  have heq : realTrace (augmentedCenter H K * rightDensity S) =
      realTrace (signedLift K * S) := by
    simp [augmentedCenter, rightDensity, Matrix.fromBlocks_multiply, realTrace,
      Matrix.trace, Matrix.diag, Fintype.sum_sum_type]
  rwa [heq, hval] at h

theorem epochPotential_initial_le [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {b : ℝ} (hsum : ∑ i, A i ≤ b • (1 : Matrix n n ℂ))
    {ε : ℝ} (hε : 0 ≤ ε) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {a R θ : ℝ} (haR : 0 ≤ a * R) (hθ : 0 ≤ θ) (x₀ : ι → ℝ) :
    epochPotential A β θ x₀ (initialState a R x₀) ≤
      2 * Real.sqrt (4 * (a * R) * ε * (r : ℝ) ^ β * b) +
      2 * θ * Real.sqrt (Fintype.card (FourSpin n) : ℝ) := by
  have hc : ∀ i : ι, 0 ≤ (fun _ : ι => a * R) i := fun _ => haR
  have hz : augmentedCenter (discrepancy A x₀ (initialState a R x₀))
      (budgetCenter A x₀ (initialState a R x₀)) = 0 := by
    simp [augmentedCenter, discrepancy, budgetCenter, initialState, position, spent,
      signedLift]
  unfold epochPotential
  rw [hz]
  exact potential_zero_le_source_budget A hβ.le hβ1.le hc hθ
    (fun _ hS => source_trace_le_mass A hA hsum hε hN hr hβ hβ1 haR
      (fun _ => le_rfl) hS)

end AugmentedHigherRankKS
