import AugmentedHigherRankKS.FourBlockProbeFloors
import AugmentedHigherRankKS.FourBlockInitialPotential

/-! Input-only caps for the quantitative optimizer and owner floors. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS Filter Set
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance inputFloorCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}

theorem objective_le_input_bound (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) {b : ℝ}
    (hsum : ∑ i, A i ≤ b • (1 : Matrix n n ℂ))
    {ε : ℝ} (hε : 0 ≤ ε) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {c : ι → ℝ} {L : ℝ} (hc : ∀ i, 0 ≤ c i) (hL : 0 ≤ L) (hcap : ∀ i, c i ≤ L)
    {θ : ℝ} (hθ : 0 ≤ θ) {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S ∈ densitySet) :
    objective H A β c θ S ≤ ‖H‖ + 2 * Real.sqrt (4*L*ε*(r:ℝ)^β*b) +
      2*θ*Real.sqrt (Fintype.card (FourSpin n) : ℝ) := by
  have hlin := realTrace_mul_density_le_norm hH hS
  have hf := fidelity_le_sqrt_trace_mul hS.1 (source_posSemidef A β hc hS.1)
  rw [hS.2, one_mul] at hf
  have hsource := source_trace_le_mass A hA hsum hε hN hr hβ hβ1 hL hcap hS
  have hf' := hf.trans (Real.sqrt_le_sqrt hsource)
  have hr' := mul_le_mul_of_nonneg_left (density_trace_sqrt_le_sqrt_card hS)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hθ)
  unfold objective
  linarith

/-- All four quantitative floors follow from ordinary input norms and rank bounds.
The actual optimizing density and transport are used throughout. -/
theorem maximizer_input_floors (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) {b : ℝ}
    (hsum : ∑ i, A i ≤ b • (1 : Matrix n n ℂ))
    {ε : ℝ} (hε : 0 ≤ ε) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) {L : ℝ} (hL : 0 ≤ L) (hccap : ∀ i, c i ≤ L)
    {θ B : ℝ} (hθ : 0 < θ) (hB : 0 < B)
    (hinput : 2*‖H‖ + 2*Real.sqrt (4*L*ε*(r:ℝ)^((1:ℝ)/2^k)*b) +
      2*θ*Real.sqrt (Fintype.card (FourSpin n) : ℝ) ≤ B)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, objective H A ((1:ℝ)/2^k) c θ T ≤ objective H A ((1:ℝ)/2^k) c θ S) :
    let s := (θ/B)^2
    s • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ (S : Matrix (FourSpin n) (FourSpin n) ℂ) ∧
    B⁻¹ • (1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) ≤
      SupportedSpin.transport A ((1:ℝ)/2^k) c S ∧
    (∀ i, s*realTrace (A i) ≤ BalancedFrames.carrierMass
      (SupportedSpin.probe A) (SupportedSpin.density A S) i) ∧
    (∀ i, 4*s*realTrace (A i*A i)/B ≤ BalancedFrames.transportMass
      (SupportedSpin.term A ((1:ℝ)/2^k) S) (SupportedSpin.transport A ((1:ℝ)/2^k) c S) i) := by
  have hb : (1:ℝ)/2^k < 1 := (div_lt_one (by positivity)).mpr
    (one_lt_pow₀ (by norm_num) (by omega))
  have hin := objective_le_input_bound H hH A hA hsum hε hN hr (by positivity) hb
    (fun i => (hc i).le) hL hccap hθ.le ⟨hS.posSemidef,ht⟩
  have hcap : objective H A ((1:ℝ)/2^k) c θ S + ‖H‖ ≤ B := by linarith
  have hs := maximizer_density_floor H hH A hA k hk c hc hθ hB S hS ht hmax hcap
  have hz := maximizer_transport_floor H hH A hA k hk c hc hθ hB S hS ht hmax hcap
  exact ⟨hs,hz,fun i => carrierMass_floor A hA (sq_nonneg _) hs i,
    fun i => transportMass_floor A hA k hk c hS (sq_nonneg _) hB hs hz i⟩
end AugmentedHigherRankKS
