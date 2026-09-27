import HigherRankKS.FaceEndpoint

/-! The concrete endpoint-or-negative-frame dichotomy on the current live face. -/

open Matrix MatrixSpencer Set MatrixSpencer.KSSignSymmetry MatrixSpencer.KSSpinDrift
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS.FaceGeometry

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- At every nonvertex cube point, either an actual endpoint move succeeds,
or the actual faithful optimizer yields a legal balanced-frame direction with negative bound.
All objects in the second branch are constructed from the original atoms and current face. -/
theorem endpoint_or_negative_frame
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 < θ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) (hnot : ¬ ksVertex 1 x) :
    let β := (1 : ℝ) / 2 ^ k
    let B := fun i : {i // i ∈ live x} => A i
    let y₀ := livePoint x
    CompactVertex.EndpointOrDescent 1 (cubePotential A β θ) x ∨
      (∀ i, B i ≠ 0) ∧
      ∃ S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ),
        (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef ∧
        realTrace (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 1 ∧
        (∀ T ∈ densitySet, liveObjective A β θ x T ≤
          liveObjective A β θ x (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) ∧
        conjugate signMatrix (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) = S ∧
        (∀ i, β * SourceProfile.owner β (y₀ i) * SupportedFrames.q B β y₀ S i <
          SourceProfile.endpointDistance (y₀ i)) ∧
        ∃ ω y : {i // i ∈ live x} → ℝ, y ≠ 0 ∧
          (1 - (TwoFrames.channel (SupportedFrames.E B β y₀ S) (SupportedFrames.F B β y₀ S))ᵀ) *ᵥ ω =
            ((TwoFrames.spinChannel (SupportedSpin.involution B) (SupportedFrames.E B β y₀ S)
                (SupportedFrames.F B β y₀ S))ᵀ -
              (TwoFrames.channel (SupportedFrames.E B β y₀ S) (SupportedFrames.F B β y₀ S))ᵀ *
                Matrix.diagonal (SupportedFrames.z B β y₀ S)) *ᵥ y ∧
          legalUpper ((1 / β) • SupportedFrames.P B β y₀ S) (SupportedSpin.involution B)
            (SupportedFrames.E B β y₀ S) (SupportedFrames.R B β y₀ S)
            (fun i => SupportedFrames.r B β y₀ S i ^ 2 +
              (2 / (100 / β)) * SupportedFrames.z B β y₀ S i ^ 2)
            (SupportedFrames.z B β y₀ S) (100 / β) ω y < 0 := by
  dsimp only
  have hβ : (1 : ℝ) / 2 ^ k ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    exact (div_lt_one (by positivity)).2 (one_lt_pow₀ (by norm_num) (by omega))
  obtain ⟨S, hS, ht, hmax, hfixed⟩ := exists_faithful_live_optimizer A hβ hθ x
  by_cases hz : ∃ i : {i // i ∈ live x}, A i = 0
  · obtain ⟨i, hi⟩ := hz
    exact Or.inl (zero_live_endpoint A _ θ x i i.property hi)
  have hne : ∀ i : {i // i ∈ live x}, A i ≠ 0 := fun i hi => hz ⟨i, hi⟩
  by_cases hcert : ∃ i : {i // i ∈ live x},
      1 - |x i| ≤ ((1 : ℝ) / 2 ^ k) * SourceProfile.owner ((1 : ℝ) / 2 ^ k) (x i) *
      SupportedFrames.q (fun j : {j // j ∈ live x} => A j) ((1 : ℝ) / 2 ^ k)
        (livePoint x) (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) i
  · exact Or.inl (endpointOrDescent_of_supported_certificate A hA k hk θ hθ.le hx S hS ht hmax hcert)
  have hfail : ∀ i : {i // i ∈ live x},
      ((1 : ℝ) / 2 ^ k) * SourceProfile.owner ((1 : ℝ) / 2 ^ k) (livePoint x i) *
        SupportedFrames.q (fun j : {j // j ∈ live x} => A j) ((1 : ℝ) / 2 ^ k)
          (livePoint x) (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) i <
        SourceProfile.endpointDistance (livePoint x i) := by
    intro i
    exact lt_of_not_ge (fun hi => hcert ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := live_nonempty hx hnot
  letI : Nonempty {i // i ∈ live x} := ⟨⟨i, hi⟩⟩
  exact Or.inr ⟨hne, S, hS, ht, hmax, hfixed, hfail,
    SupportedFrames.exists_negative_actual_frame (fun j : {j // j ∈ live x} => A j)
      (fun j => hA j) hne k hk (livePoint x) (livePoint_interior x) hS hfixed hfail⟩

end HigherRankKS.FaceGeometry
