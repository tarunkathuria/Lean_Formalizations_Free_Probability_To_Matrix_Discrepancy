import AugmentedHigherRankKS.FourBlockResponseGeometry

/-! The actual joint response bounded by one legal transport trial, uniformly in density. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS MatrixSpencer.KSFisher
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS.Frames
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance normalizedResponseCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}
open TwoFrames

theorem normalized_objective_second_le (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (c : ℝ → ι → ℝ) (hcs : ContDiffAt ℝ 2 c 0) (hc : ∀ i, 0 < c 0 i)
    (hdc : ∀ i, deriv (fun t => c t i) 0 = 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (w y : ι → ℝ)
    (hlegal : (1 - (channel (E A ((1 : ℝ) / 2 ^ k) (c 0) S)
      (F A ((1 : ℝ) / 2 ^ k) (c 0) S))ᵀ) *ᵥ w =
      (channel (N A ((1 : ℝ) / 2 ^ k) (c 0) x S) (F A ((1 : ℝ) / 2 ^ k) (c 0) S))ᵀ *ᵥ y) :
    let β := (1 : ℝ) / 2 ^ k
    let σ := 2 * β / (1 + β)
    let K := coefficientForce A x (direction (c 0) y)
    let Z := SupportedSpin.transport A β (c 0) S
    iteratedDeriv 2 (fun t : ℝ => hermitianObjective (H+t • K) A β (c t) θ (S+t • X)) 0 / 2 ≤
      PointwiseResponse.direct A β c Z S / 2 +
      realTrace (P A β (c 0) S * (IndependentLegalResponse.trial (E A β (c 0) S)
        (N A β (c 0) x S) w y * IndependentLegalResponse.trial (E A β (c 0) S)
          (N A β (c 0) x S) w y)) / σ := by
  dsimp only
  let β := (1 : ℝ) / 2 ^ k
  have hZ := SupportedSpin.transport_posDef A hA hc hS k hk
  have hP := SupportedSourceMetric.balanced_posDef A hA (c 0) hc k hk S hS
  obtain ⟨hE, hF, hN, _⟩ := frame_properties A hA hne k hk (c 0) hc x hS
  have hY := balanced_variation_isHermitian A β (c 0) S hZ X
  have hσ : 0 < 2 * β / (1 + β) := by positivity
  have hr := IndependentLegalResponse.response_le (E A β (c 0) S) (F A β (c 0) S)
    (N A β (c 0) x S) (fun i => (hE i).isHermitian) (fun i => (hF i).isHermitian) hN
    (P A β (c 0) S) hP w y hlegal hσ hY
  have hp := PointwiseResponse.independent_response_le A hA hne k hk c hcs hc hdc
    H (coefficientForce A x (direction (c 0) y)) θ hθ S X hS
  dsimp only at hp
  rw [normalized_force_pairing A hA k hk (c 0) hc x y hx hS X] at hp
  have hm : PointwiseResponse.frameMismatch A β (c 0) (fun _ => 0)
      (SupportedSpin.transport A β (c 0) S) S X =
      balancedDensity (SupportedSpin.density A X) (SupportedSpin.transport A β (c 0) S) -
      frameChannel (E A β (c 0) S) (F A β (c 0) S)
        (balancedDensity (SupportedSpin.density A X) (SupportedSpin.transport A β (c 0) S)) := by
    simp only [PointwiseResponse.frameMismatch, zero_smul, Finset.sum_const_zero, sub_zero, E, F]
  change _ ≤ _ at hp
  rw [hm] at hp
  dsimp only [β, P, SupportedSourceMetric.balanced] at hr hp ⊢
  linarith

end AugmentedHigherRankKS.Frames
