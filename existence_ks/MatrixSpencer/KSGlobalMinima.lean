import MatrixSpencer.KSPotentialModels

/-! Attainment for the actual continuous full-cube and discontinuous truncated potentials. -/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Set

noncomputable section
namespace MatrixSpencer.KSPotentialModels

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

def branchDomain (a : ℝ) (L : Finset (Fin N)) : Set (Fin N → ℝ) :=
  {x | x ∈ ksCube a ∧ ∀ i ∉ L, |x i| = a}

theorem branchDomain_compact (a : ℝ) (L : Finset (Fin N)) : IsCompact (branchDomain a L) := by
  have hclosed : IsClosed {x : Fin N → ℝ | ∀ i ∉ L, |x i| = a} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro _
    exact isClosed_eq (continuous_apply i).abs continuous_const
  exact (ksCube_compact a).inter_right hclosed

theorem mem_own_branch {a : ℝ} {x : Fin N → ℝ} (hx : x ∈ ksCube a) :
    x ∈ branchDomain a (live a x) := by
  refine ⟨hx, ?_⟩
  intro i hi
  have hnot : ¬ |x i| < a := by simpa only [live, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  exact le_antisymm (abs_le.mpr ⟨hx.1 i, hx.2 i⟩) (le_of_not_gt hnot)

theorem truncatedOwners_le_branch {a u : ℝ} (hu : 0 ≤ u) (ha : a ≤ 1)
    {L : Finset (Fin N)} {x : Fin N → ℝ} (hx : x ∈ branchDomain a L) (i : Fin N) :
    truncatedOwners a u x i ≤ maskedOwners u L x i := by
  by_cases hi : i ∈ live a x
  · have hiL : i ∈ L := by
      by_contra hn
      have hil : |x i| < a := (Finset.mem_filter.mp hi).2
      exact (ne_of_lt hil) (hx.2 i hn)
    simp only [truncatedOwners, maskedOwners, if_pos hi, if_pos hiL, le_refl]
  · simp only [truncatedOwners, maskedOwners, if_neg hi]
    split_ifs
    · exact naturalOwners_nonneg hu ha hx.1 i
    · exact le_rfl

theorem continuousOn_common_masked (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) {a u : ℝ} (hu : 0 ≤ u) (ha : a ≤ 1)
    (L : Finset (Fin N)) :
    ContinuousOn (fun x => commonPotential A θ x (maskedOwners u L x)) (ksCube a) := by
  exact continuousOn_diagonal_ownerPotential (KSCommonSource.family A)
    (KSCommonSource.family_isHermitian A hA) θ (ksCube a)
    (fun x => signedLift (center A x)) (maskedOwners u L)
    (continuous_signed_center A).continuousOn (continuous_maskedOwners u L).continuousOn
    (fun _ hx i => maskedOwners_nonneg hu ha hx L i)

theorem continuousOn_spinPotential (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) :
    ContinuousOn (spinPotential A θ) (ksCube 1) := by
  have hc : Continuous (fun x : Fin N → ℝ => fun j : Fin N × Fin 4 => naturalOwners 64 x j.1 / 2) := by
    unfold naturalOwners
    fun_prop
  exact continuousOn_diagonal_ownerPotential (KSSpinSource.family A)
    (KSSpinSource.family_isHermitian A hA) θ (ksCube 1)
    (fun x => signedLift (center A x)) (fun x j => naturalOwners 64 x j.1 / 2)
    (continuous_signed_center A).continuousOn hc.continuousOn
    (fun _ hx j => div_nonneg (naturalOwners_nonneg (by norm_num) le_rfl hx j.1) (by norm_num))

theorem spinPotential_has_minimum (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) :
    ∃ x ∈ ksCube 1, IsMinOn (spinPotential A θ) (ksCube 1) x :=
  (ksCube_compact 1).exists_isMinOn ⟨0, ksCube_zero (by norm_num)⟩
    (continuousOn_spinPotential A hA θ)

theorem eighthPotential_has_minimum [Nonempty n] (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) :
    ∃ x ∈ ksCube (1 / 8), IsMinOn (eighthPotential A θ) (ksCube (1 / 8)) x := by
  apply ks_exists_minimum_of_compact_branches (ksCube (1 / 8))
    (branchDomain (1 / 8)) (eighthPotential A θ)
    (fun L x => commonPotential A θ x (maskedOwners 64 L x))
    ⟨0, ksCube_zero (by norm_num)⟩ (branchDomain_compact (1 / 8))
  · intro L
    exact (continuousOn_common_masked A hA θ (by norm_num) (by norm_num) L).mono (fun _ hx => hx.1)
  · intro _ _ hx
    exact hx.1
  · intro L x hx
    apply commonPotential_mono A hA θ x
      (fun i => maskedOwners_nonneg (by norm_num) (by norm_num) hx.1 _ i)
      (fun i => maskedOwners_nonneg (by norm_num) (by norm_num) hx.1 L i)
    exact truncatedOwners_le_branch (by norm_num) (by norm_num) hx
  · intro x hx
    exact ⟨live (1 / 8) x, mem_own_branch hx, rfl⟩

end MatrixSpencer.KSPotentialModels
