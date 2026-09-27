import HigherRankKS.EndpointMove
import HigherRankKS.FaceGeometry
import HigherRankKS.SupportedFrameDirection
import HigherRankKS.SpinSymmetry

/-! The supported endpoint certificate in the coordinates of the original cube. -/

open Matrix MatrixSpencer Set MatrixSpencer.KSSignSymmetry
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS.EndpointCertificate

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

omit [DecidableEq ι] in
/-- The endpoint probe is exactly the ratio in the supported balanced frames. -/
theorem probeRatio_eq_q (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (β : ℝ) (x : ι → ℝ) (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) (i : ι) :
    probeRatio A β (SupportedFrames.weights β x) S i =
      SupportedFrames.q A β x (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) i := by
  unfold SupportedFrames.q BalancedFrames.transportMass BalancedFrames.carrierMass
  rw [SupportedSpin.probe_pairing A hA, SupportedSpin.term_pairing]
  rfl

end HigherRankKS.EndpointCertificate

namespace HigherRankKS.FaceGeometry

variable {N : ℕ}

theorem faceState_update_live (x : Fin N → ℝ) (i : {i // i ∈ live x}) (s : ℝ) :
    faceState (live x) x (Function.update (livePoint x) i s) =
      Function.update x i.val s := by
  funext j
  by_cases hji : j = i.val
  · subst j
    simp [faceState, i.property]
  · by_cases hj : j ∈ live x
    · have hsub : (⟨j, hj⟩ : {i // i ∈ live x}) ≠ i := by
        intro he
        exact hji (congrArg Subtype.val he)
      simp [faceState, hj, Function.update_of_ne hsub, Function.update_of_ne hji, livePoint]
    · simp [faceState, hj, Function.update_of_ne hji]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The objective on the current live face, retaining the frozen center. -/
def liveObjective (A : Fin N → Matrix n n ℂ) (β θ : ℝ) (x : Fin N → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) : ℝ :=
  objective (signedLift (KSPotentialModels.center A x))
    (fun i : {i // i ∈ live x} => A i) β
    (SupportedFrames.weights β (livePoint x)) θ S

/-- Every live face has an attained, faithful, spin-symmetric optimizer.
This also permits an empty live family. -/
theorem exists_faithful_live_optimizer [Nonempty n]
    (A : Fin N → Matrix n n ℂ) {β θ : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1)
    (hθ : 0 < θ) (x : Fin N → ℝ) :
    ∃ S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ),
      (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef ∧
      realTrace (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 1 ∧
      (∀ T ∈ densitySet, liveObjective A β θ x T ≤
        liveObjective A β θ x (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) ∧
      conjugate signMatrix (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
        (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  let B : {i // i ∈ live x} → Matrix n n ℂ := fun i => A i
  let c := SupportedFrames.weights β (livePoint x)
  have hc : ∀ i, 0 ≤ c i := fun i =>
    (SourceProfile.owner_pos hβ.1 (livePoint_interior x i)).le
  obtain ⟨S, hSd, hmax⟩ := exists_optimizer (signedLift (KSPotentialModels.center A x))
    B hβ.1.le hβ.2.le hc θ
  have hS := maximizer_posDef (signedLift (KSPotentialModels.center A x))
    B hβ.1 hβ.2 hc hθ hSd hmax
  refine ⟨⟨S, hS.isHermitian⟩, hS, hSd.2, hmax, ?_⟩
  have hval := objective_sign_invariant (KSPotentialModels.center A x) B β hc θ hSd.1
  exact (strictConcaveOn_objective (signedLift (KSPotentialModels.center A x))
    B hβ.1 hβ.2 hc hθ).eq_of_isMaxOn
    (fun T hT => (hmax T hT).trans_eq hval.symm) hmax
    (conjugate_mem_density signMatrix_isHermitian signMatrix_sq hSd) hSd

/-- A live supported certificate gives the literal full-cube endpoint inequality. -/
theorem cubePotential_nearest_endpoint_le
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 ≤ θ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, liveObjective A ((1 : ℝ) / 2 ^ k) θ x T ≤
      liveObjective A ((1 : ℝ) / 2 ^ k) θ x (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (i : {i // i ∈ live x}) (hi : A i ≠ 0)
    (hcert : 1 - |x i| ≤ ((1 : ℝ) / 2 ^ k) * SourceProfile.owner ((1 : ℝ) / 2 ^ k) (x i) *
      SupportedFrames.q (fun j : {j // j ∈ live x} => A j) ((1 : ℝ) / 2 ^ k)
        (livePoint x) (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) i) :
    cubePotential A ((1 : ℝ) / 2 ^ k) θ
        (Function.update x i.val (KSPotentialModels.nearestSign (x i))) ≤
      cubePotential A ((1 : ℝ) / 2 ^ k) θ x := by
  have hβ : 0 < (1 : ℝ) / 2 ^ k := by positivity
  have heq₀ := face_potential_eq A hβ θ hx (livePoint x)
  rw [faceState_base] at heq₀
  have heq₁ := face_potential_eq A hβ θ hx
    (Function.update (livePoint x) i (KSPotentialModels.nearestSign (x i)))
  rw [faceState_update_live, KSPotentialModels.signed_center_update] at heq₁
  rw [heq₁, heq₀]
  apply EndpointCertificate.potential_nearest_endpoint_le
    (signedLift (KSPotentialModels.center A x)) (fun j : {j // j ∈ live x} => A j)
    (fun j => hA j) k hk (livePoint x) (livePoint_interior x) θ hθ S hS ht hmax i hi
  have hratio := EndpointCertificate.probeRatio_eq_q
    (fun j : {j // j ∈ live x} => A j) (fun j => hA j) ((1 : ℝ) / 2 ^ k)
    (livePoint x) S i
  change EndpointCertificate.probeRatio (fun j : {j // j ∈ live x} => A j)
    ((1 : ℝ) / 2 ^ k) (fun j => SourceProfile.owner ((1 : ℝ) / 2 ^ k) (livePoint x j)) S i = _ at hratio
  rw [hratio]
  exact hcert

/-- A successful supported certificate supplies the endpoint branch of the cube alternative.
A zero atom is retired directly. -/
theorem endpointOrDescent_of_supported_certificate
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 ≤ θ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, liveObjective A ((1 : ℝ) / 2 ^ k) θ x T ≤
      liveObjective A ((1 : ℝ) / 2 ^ k) θ x (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hcert : ∃ i : {i // i ∈ live x},
      1 - |x i| ≤ ((1 : ℝ) / 2 ^ k) * SourceProfile.owner ((1 : ℝ) / 2 ^ k) (x i) *
      SupportedFrames.q (fun j : {j // j ∈ live x} => A j) ((1 : ℝ) / 2 ^ k)
        (livePoint x) (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) i) :
    CompactVertex.EndpointOrDescent 1 (cubePotential A ((1 : ℝ) / 2 ^ k) θ) x := by
  obtain ⟨i, hi⟩ := hcert
  by_cases hz : A i = 0
  · exact zero_live_endpoint A _ θ x i i.property hz
  · left
    exact ⟨i, (mem_live x i).mp i.property, KSPotentialModels.nearestSign (x i),
      (KSPotentialModels.nearestSign_isSign (x i)).symm,
      cubePotential_nearest_endpoint_le A hA k hk θ hθ hx S hS ht hmax i hz hi⟩

end HigherRankKS.FaceGeometry
