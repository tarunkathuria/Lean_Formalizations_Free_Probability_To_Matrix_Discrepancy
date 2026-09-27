import MatrixSpencer.KSLiveCurve
import MatrixSpencer.KSJacobiRayleigh
import Mathlib.Data.List.NodupEquivFin

/-!
# Explicit live-label enumeration for the finite Jacobi direction

The original labels are scanned in order and filtered by their actual
coefficient comparison. Forward indexing uses list lookup; inverse indexing
uses the finite list index search. Extension inserts exact zeroes on frozen
labels and preserves the Euclidean norm.
-/

open Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSLiveEnumeration

variable {N : ℕ}

def labels (x : Fin N → ℝ) : List (Fin N) :=
  (List.finRange N).filter (fun i => decide (|x i| < 1))

def count (x : Fin N → ℝ) : ℕ := (labels x).length

theorem labels_nodup (x : Fin N → ℝ) : (labels x).Nodup :=
  (List.nodup_finRange N).filter _

theorem mem_labels (x : Fin N → ℝ) (i : Fin N) : i ∈ labels x ↔ |x i| < 1 := by
  simp [labels]

/-- This equivalence is implemented by `get` and `idxOf` on the computed list. -/
def liveEquiv (x : Fin N → ℝ) : Fin (count x) ≃ KSLiveCurve.Live 1 x :=
  ((labels_nodup x).getEquiv (labels x)).trans
    { toFun := fun i => ⟨i.val, (mem_labels x i.val).mp i.property⟩
      invFun := fun i => ⟨i.val, (mem_labels x i.val).mpr i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def extend (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin (count x))) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (KSLiveCurve.extend 1 x (fun i => v ((liveEquiv x).symm i)))

theorem extend_live (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin (count x)))
    (i : KSLiveCurve.Live 1 x) : extend x v i = v ((liveEquiv x).symm i) := by
  exact KSLiveCurve.extend_live 1 x (fun j => v ((liveEquiv x).symm j)) i

theorem extend_dead (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin (count x)))
    (i : Fin N) (hi : ¬ |x i| < 1) : extend x v i = 0 := by
  exact KSLiveCurve.extend_dead 1 x (fun j => v ((liveEquiv x).symm j)) i hi

theorem extend_frozen (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin (count x)))
    (i : Fin N) (hi : |x i| = 1) : extend x v i = 0 :=
  extend_dead x v i (by rw [hi]; exact lt_irrefl _)

theorem extend_norm (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin (count x))) :
    ‖extend x v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rw [KSLiveCurve.sum_restrict_live 1 x (fun i => (extend x v i) ^ 2)
    (by intro i hi; dsimp only; rw [extend_dead x v i hi]; norm_num)]
  simp only [extend_live]
  exact (liveEquiv x).symm.sum_comp (fun i => v i ^ 2)

theorem count_pos_of_not_vertex {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (hnot : ¬ksVertex 1 x) : 0 < count x := by
  by_contra hcount
  have he : labels x = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hcount)
  apply hnot
  intro i
  have hdead : ¬ |x i| < 1 := by
    intro hi
    have hm := (mem_labels x i).mpr hi
    rw [he] at hm
    exact List.not_mem_nil hm
  have habs : |x i| = 1 := le_antisymm (abs_le.mpr ⟨hx.1 i, hx.2 i⟩) (not_lt.mp hdead)
  exact ((abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs).symm

/-- The actual Jacobi vector on the finite live block has the exact
normalization and frozen-coordinate properties needed by the walk. -/
def direction (x : Fin N → ℝ) (K : Matrix (Fin (count x)) (Fin (count x)) ℝ)
    (κ : ℝ) (hlive : 0 < count x) : EuclideanSpace ℝ (Fin N) :=
  extend x (KSJacobiRayleigh.outputVector K κ hlive)

theorem direction_unit (x : Fin N → ℝ)
    (K : Matrix (Fin (count x)) (Fin (count x)) ℝ) (κ : ℝ) (hlive : 0 < count x) :
    ‖direction x K κ hlive‖ = 1 := by
  rw [direction, extend_norm]
  exact KSJacobiRayleigh.outputVector_norm K κ hlive

theorem direction_frozen (x : Fin N → ℝ)
    (K : Matrix (Fin (count x)) (Fin (count x)) ℝ) (κ : ℝ) (hlive : 0 < count x)
    (i : Fin N) (hi : |x i| = 1) : direction x K κ hlive i = 0 :=
  extend_frozen x _ i hi

end MatrixSpencer.KSLiveEnumeration
