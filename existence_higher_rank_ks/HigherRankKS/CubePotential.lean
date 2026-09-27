import HigherRankKS.Potential
import HigherRankKS.SourceProfile
import HigherRankKS.CompactVertex
import MatrixSpencer.KSPotentialModels

/-!
# The concrete potential on the coefficient cube

The state has one real coordinate for each original input matrix.
The source profile is evaluated at those same coordinates. This file
proves continuity, actual attainment of a cube minimum, and the
discrepancy bound. The vertex-minimum assertion needs the separate
local curvature argument.
-/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

def cubePotential (A : Fin N → Matrix n n ℂ) (β θ : ℝ)
    (x : Fin N → ℝ) : ℝ :=
  potential (signedLift (KSPotentialModels.center A x)) A β
    (fun i => SourceProfile.owner β (x i)) θ

theorem cube_weights_nonneg {β : ℝ} (hβ : 0 < β)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) (i : Fin N) :
    0 ≤ SourceProfile.owner β (x i) :=
  SourceProfile.weight_nonneg (SourceProfile.ownerScale_pos hβ).le
    (SourceProfile.kappa_pos hβ).le ⟨hx.1 i, hx.2 i⟩

theorem continuousOn_cubePotential (A : Fin N → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (θ : ℝ) :
    ContinuousOn (cubePotential A β θ) (ksCube 1) := by
  apply continuousOn_iff_continuous_restrict.mpr
  exact continuous_potential_of_data A
    ((KSPotentialModels.continuous_signed_center A).comp continuous_subtype_val)
    hβ.le hβ1
    (fun i => (SourceProfile.continuous_coordinate_owner hβ i).comp continuous_subtype_val)
    (fun x i => cube_weights_nonneg hβ x.property i) θ

theorem exists_cubePotential_minimum (A : Fin N → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (θ : ℝ) :
    ∃ x ∈ ksCube 1, IsMinOn (cubePotential A β θ) (ksCube 1) x :=
  CompactVertex.exists_cube_minimum (by norm_num) _
    (continuousOn_cubePotential A hβ hβ1 θ)

theorem center_norm_le_cubePotential [Nonempty n]
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {θ : ℝ} (hθ : 0 ≤ θ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    ‖KSPotentialModels.center A x‖ ≤ cubePotential A β θ x :=
  norm_le_potential (KSPotentialModels.center_isHermitian A hA x) A
    hβ.le hβ1 (cube_weights_nonneg hβ hx) hθ

theorem source_vanishes_at_signing (A : Fin N → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 < β) {x : Fin N → ℝ}
    (hx : ∀ i, x i = 1 ∨ x i = -1)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    source A β (fun i => SourceProfile.owner β (x i)) S = 0 := by
  have heq : (fun i => SourceProfile.owner β (x i)) = (fun _ => 0) := by
    funext i
    rcases hx i with h | h
    · rw [h, SourceProfile.owner_one hβ]
    · rw [h, SourceProfile.owner_neg_one hβ]
  rw [heq, source_zero_weights]

end HigherRankKS
