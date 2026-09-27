import HigherRankKS.EndpointCertificate
import MatrixSpencer.KSStateRetirement

/-! The fixed-transport certificate for a literal nearest-endpoint owner move. -/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS.EndpointCertificate

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]


def probeRatio (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) (i : ι) : ℝ :=
  SourceDerivative.probe β (A i)
    (extended A (SupportedSpin.transport A β c (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))) S /
      realTrace (spinAtom (A i) * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))

omit [Fintype ι] [Fintype n] [DecidableEq n] in
theorem owner_nearest_update {β : ℝ} (hβ : 0 < β) (x : ι → ℝ) (i : ι) :
    (fun j => SourceProfile.owner β (Function.update x i (KSPotentialModels.nearestSign (x i)) j)) =
      Function.update (fun j => SourceProfile.owner β (x j)) i 0 := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self]
    rcases KSPotentialModels.nearestSign_isSign (x i) with hs | hs
    · rw [hs, SourceProfile.owner_one hβ]
    · rw [hs, SourceProfile.owner_neg_one hβ]
  · simp only [Function.update_of_ne hj]

/-- A nearest endpoint move is nonincreasing whenever the actual scalar certificate holds.
The center may include an arbitrary fixed contribution from frozen labels. -/
theorem potential_nearest_endpoint_le (H : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (x : ι → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet,
      objective H A ((1 : ℝ) / 2 ^ k) (fun j => SourceProfile.owner ((1 : ℝ) / 2 ^ k) (x j)) θ T ≤
      objective H A ((1 : ℝ) / 2 ^ k) (fun j => SourceProfile.owner ((1 : ℝ) / 2 ^ k) (x j)) θ
        (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (i : ι) (hi : A i ≠ 0)
    (hcert : 1 - |x i| ≤ ((1 : ℝ) / 2 ^ k) * SourceProfile.owner ((1 : ℝ) / 2 ^ k) (x i) *
      probeRatio A ((1 : ℝ) / 2 ^ k)
        (fun j => SourceProfile.owner ((1 : ℝ) / 2 ^ k) (x j)) S i) :
    potential (H + (KSPotentialModels.nearestSign (x i) - x i) • signedLift (A i)) A
      ((1 : ℝ) / 2 ^ k)
      (fun j => SourceProfile.owner ((1 : ℝ) / 2 ^ k)
        (Function.update x i (KSPotentialModels.nearestSign (x i)) j)) θ ≤
      potential H A ((1 : ℝ) / 2 ^ k)
        (fun j => SourceProfile.owner ((1 : ℝ) / 2 ^ k) (x j)) θ := by
  have hβ : 0 < (1 : ℝ) / 2 ^ k := by positivity
  rw [owner_nearest_update hβ]
  apply potential_delete_le H _ A hA k hk _ (fun j => SourceProfile.owner_pos hβ (hx j))
    θ hθ S hS ht hmax i hi (1 - |x i|) _ hcert
  exact KSEndpointRetirement.spin_step_le (hA i)
    (KSPotentialModels.nearestSign_distance ⟨(hx i).1.le, (hx i).2.le⟩).le

end HigherRankKS.EndpointCertificate
