import AugmentedHigherRankKS.FourBlockInputFloors
import AugmentedHigherRankKS.BudgetOrder
import AugmentedHigherRankKS.EpochPotential

/-! Uniform conditioning of the actual SDP queries throughout an epoch. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS Filter Set
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance queryFloorCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}

/-- The deliberately generous denominator dominates the exact KKT input cap. -/
theorem scalar_query_cap {a T d u θ : ℝ} (ha : 1 ≤ a) (hT : 1 ≤ T)
    (hd : d ≤ T) (hu : u ≤ 64*a) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    16+2*Real.sqrt u+2*θ*Real.sqrt (4*d) ≤ 64*a*T := by
  have ha0 : 0 ≤ a := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hs : Real.sqrt u ≤ 8*a := (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩
  have hd' : Real.sqrt (4*d) ≤ 2*T := (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩
  have ht : θ*Real.sqrt (4*d) ≤ 2*T := by
    calc _ ≤ 1*Real.sqrt (4*d) := mul_le_mul_of_nonneg_right hθ1 (Real.sqrt_nonneg _)
         _ ≤ _ := by simpa only [one_mul] using hd'
  have hat : a ≤ a*T := by nlinarith
  have hta : T ≤ a*T := by nlinarith
  have h1 : 1 ≤ a*T := by nlinarith
  nlinarith

theorem source_query_budget (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) {β : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hrβ : (r:ℝ)^β ≤ 2)
    {a : ℝ} (ha : 0 ≤ a) {c : ι → ℝ} (hc : ∀ i, c i ≤ 8*a)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S ∈ densitySet) :
    realTrace (source A β c S) ≤ 64*a := by
  have hh := source_trace_le_mass A hA (b := 1) (by simpa using hsum) hε hN hr hβ hβ1
    (by positivity : 0 ≤ 8*a) hc hS
  apply hh.trans
  calc 4*(8*a)*ε*(r:ℝ)^β*1 ≤ 4*(8*a)*1*2*1 := by gcongr
       _ = 64*a := by ring

/-- Uniform base fidelity, including every queried optimizing density. -/
theorem fidelity_query_bound (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) {β : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hrβ : (r:ℝ)^β ≤ 2)
    {a : ℝ} (ha : 0 ≤ a) {c : ι → ℝ} (hc0 : ∀ i, 0 ≤ c i) (hc : ∀ i, c i ≤ 8*a)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S ∈ densitySet) :
    fidelity S (source A β c S) ≤ 8*Real.sqrt a := by
  have hf := fidelity_le_sqrt_trace_mul hS.1 (source_posSemidef A β hc0 hS.1)
  rw [hS.2, one_mul] at hf
  have hb := source_query_budget A hA hsum hε hε1 hN hr hβ hβ1 hrβ ha hc hS
  have he : Real.sqrt (64*a) = 8*Real.sqrt a := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 64)]
    norm_num
  exact (hf.trans (Real.sqrt_le_sqrt hb)).trans_eq he

/-- Actual query optimizers have the runtime density, transport, and probe floors. -/
theorem query_optimizer_floors (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian)
    (hH8 : ‖H‖ ≤ 8) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    {a T θ : ℝ} (ha : 1 ≤ a) (hT : 1 ≤ T) (hd : (Fintype.card n : ℝ) ≤ T)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (c : ι → ℝ) (hc : ∀ i, 0 < c i) (hccap : ∀ i, c i ≤ 8*a)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    (hmax : ∀ U ∈ densitySet, objective H A ((1:ℝ)/2^k) c θ U ≤ objective H A ((1:ℝ)/2^k) c θ S) :
    let B := 64*a*T
    let s := (θ/B)^2
    s • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ (S : Matrix (FourSpin n) (FourSpin n) ℂ) ∧
    B⁻¹ • (1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) ≤
      SupportedSpin.transport A ((1:ℝ)/2^k) c S ∧
    (∀ i, s*realTrace (A i) ≤ BalancedFrames.carrierMass
      (SupportedSpin.probe A) (SupportedSpin.density A S) i) ∧
    (∀ i, 4*s*realTrace (A i*A i)/B ≤ BalancedFrames.transportMass
      (SupportedSpin.term A ((1:ℝ)/2^k) S) (SupportedSpin.transport A ((1:ℝ)/2^k) c S) i) := by
  have ha0 : 0 ≤ a := by linarith
  have hrad : 4*(8*a)*ε*(r:ℝ)^((1:ℝ)/2^k)*1 ≤ 64*a := by
    calc _ ≤ 4*(8*a)*1*2*1 := by gcongr
         _ = _ := by ring
  have hnum := scalar_query_cap ha hT hd hrad hθ.le hθ1
  have hcard : (Fintype.card (FourSpin n) : ℝ) = 4*(Fintype.card n : ℝ) := by
    simp only [FourSpin, Fintype.card_sum, Nat.cast_add]
    ring
  apply maximizer_input_floors H hH A hA (b := 1) (by simpa using hsum)
    hε hN hr k hk c hc (L := 8*a) (by positivity) hccap hθ (by positivity) _ S hS ht hmax
  rw [hcard]
  linarith

end AugmentedHigherRankKS
