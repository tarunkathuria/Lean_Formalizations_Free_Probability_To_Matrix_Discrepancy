import RadialKS.RadialBasis

/-! The identity frame at zero and the Householder frame otherwise. -/
noncomputable section
namespace RadialKS
open RadialBasis (Space)
variable {m : ℕ}

structure Frame (z : Space m) where
  rank : ℕ
  embed : Space rank →ₗᵢ[ℝ] Space m
  orthogonal : ∀ v, inner ℝ z (embed v) = 0
  onto : ∀ g, inner ℝ z g = 0 → ∃ v, embed v = g

namespace Frame

def atZero (z : Space m) (hz : z = 0) : Frame z where
  rank := m
  embed := LinearIsometry.id
  orthogonal := by intro v; simp [hz]
  onto := by intro g _; exact ⟨g, rfl⟩

def unitVector (z : Space m) : Space m := ‖z‖⁻¹ • z

theorem unitVector_norm (z : Space m) (hz : z ≠ 0) : ‖unitVector z‖ = 1 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [unitVector, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
    inv_mul_cancel₀ hn.ne']

def atNonzero (z : Space (m + 1)) (hz : z ≠ 0) : Frame z where
  rank := m
  embed := RadialBasis.embedding (unitVector z)
  orthogonal := by
    intro v
    have h := RadialBasis.embedding_orthogonal (unitVector z) (unitVector_norm z hz) v
    rw [unitVector, real_inner_smul_left] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (norm_ne_zero_iff.mpr hz))
  onto := by
    intro g hg
    apply RadialBasis.embedding_surjective_orthogonal _ g (unitVector_norm z hz)
    simp only [unitVector, real_inner_smul_left, hg, mul_zero]

def canonical : (m : ℕ) → (z : Space m) → Frame z
  | 0, z => atZero z (Subsingleton.elim _ _)
  | _ + 1, z => if hz : z = 0 then atZero z hz else atNonzero z hz

theorem rank_pos_of_nonzero {z : Space m} (F : Frame z)
    (g : Space m) (hg : g ≠ 0) (ho : inner ℝ z g = 0) : 0 < F.rank := by
  obtain ⟨v, hv⟩ := F.onto g ho
  by_contra h
  have hr : F.rank = 0 := Nat.eq_zero_of_not_pos h
  haveI : IsEmpty (Fin F.rank) := by rw [hr]; infer_instance
  have hz : v = 0 := by
    apply Subsingleton.elim
  apply hg
  rw [← hv, hz, map_zero]

end Frame
end RadialKS
