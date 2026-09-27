import MatrixSpencer.KSEndpointCube

/-!
# The actual coordinate snapping operation for the KS walk

This is the first preparation operation of the eighth-cube numerical walk:
snap every coordinate within `ρ` of the boundary to its nearest endpoint.
All conclusions concern this defined operation, rather than a hypothetical
map with assumed progress. This module does not yet establish the potential
cost of snapping or the numerical covariance oracle.
-/

open scoped BigOperators
open Set

noncomputable section
namespace MatrixSpencer.KSCubePreparation

variable {N : ℕ}

def endpoint (a t : ℝ) : ℝ := if 0 ≤ t then a else -a

def snap (a ρ : ℝ) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => if a - |x i| ≤ ρ then endpoint a (x i) else x i

def energy (x : Fin N → ℝ) : ℝ := ∑ i, x i ^ 2

theorem endpoint_eq (a t : ℝ) : endpoint a t = -a ∨ endpoint a t = a := by
  unfold endpoint
  split_ifs <;> simp

theorem endpoint_abs {a : ℝ} (ha : 0 ≤ a) (t : ℝ) : |endpoint a t| = a := by
  rcases endpoint_eq a t with h | h <;> rw [h] <;> simp [abs_of_nonneg ha]

theorem endpoint_distance {a t : ℝ} (ht : -a ≤ t ∧ t ≤ a) :
    |endpoint a t - t| = a - |t| := by
  unfold endpoint
  split_ifs with h
  · rw [abs_of_nonneg h, abs_of_nonneg (by linarith : 0 ≤ a - t)]
  · rw [abs_of_neg (lt_of_not_ge h), abs_of_nonpos (by linarith : -a - t ≤ 0)]
    ring

theorem endpoint_of_abs_eq {a t : ℝ} (ht : |t| = a) :
    endpoint a t = t := by
  unfold endpoint
  split_ifs with h
  · rw [abs_of_nonneg h] at ht
    exact ht.symm
  · rw [abs_of_neg (lt_of_not_ge h)] at ht
    linarith

theorem snap_mem_cube {a ρ : ℝ} (ha : 0 ≤ a)
    {x : Fin N → ℝ} (hx : x ∈ ksCube a) : snap a ρ x ∈ ksCube a := by
  constructor <;> intro i <;> unfold snap <;> split_ifs
  · rcases endpoint_eq a (x i) with h | h <;> rw [h] <;> linarith
  · exact hx.1 i
  · rcases endpoint_eq a (x i) with h | h <;> rw [h] <;> linarith
  · exact hx.2 i

theorem snap_preserves_frozen {a ρ : ℝ}
    (x : Fin N → ℝ) (i : Fin N) (hi : |x i| = a) : snap a ρ x i = x i := by
  unfold snap
  split_ifs
  · exact endpoint_of_abs_eq hi
  · rfl

theorem snap_live_margin {a ρ : ℝ} (ha : 0 ≤ a)
    (x : Fin N → ℝ) (i : Fin N) (hi : |snap a ρ x i| < a) :
    ρ < a - |snap a ρ x i| := by
  by_cases h : a - |x i| ≤ ρ
  · have he : |snap a ρ x i| = a := by
      simp only [snap, if_pos h, endpoint_abs ha]
    exact False.elim ((ne_of_lt hi) he)
  · simpa only [snap, if_neg h] using lt_of_not_ge h

theorem snap_distance_le {a ρ : ℝ} (hρ : 0 ≤ ρ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube a) (i : Fin N) :
    |snap a ρ x i - x i| ≤ ρ := by
  unfold snap
  split_ifs with h
  · rwa [endpoint_distance ⟨hx.1 i, hx.2 i⟩]
  · simpa using hρ

theorem coordinate_sq_le {a t : ℝ} (ht : -a ≤ t ∧ t ≤ a) :
    t ^ 2 ≤ a ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (by linarith : 0 ≤ a + t)]

theorem snap_coordinate_progress {a ρ : ℝ}
    {x : Fin N → ℝ} (hx : x ∈ ksCube a) (i : Fin N) :
    x i ^ 2 ≤ snap a ρ x i ^ 2 := by
  unfold snap
  split_ifs
  · have hs : endpoint a (x i) ^ 2 = a ^ 2 := by
      rcases endpoint_eq a (x i) with h | h <;> rw [h] <;> ring
    rw [hs]
    exact coordinate_sq_le ⟨hx.1 i, hx.2 i⟩
  · exact le_rfl

theorem snap_energy_progress {a ρ : ℝ}
    {x : Fin N → ℝ} (hx : x ∈ ksCube a) : energy x ≤ energy (snap a ρ x) := by
  exact Finset.sum_le_sum (fun i _ => snap_coordinate_progress hx i)

theorem energy_bounds {a : ℝ}
    {x : Fin N → ℝ} (hx : x ∈ ksCube a) :
    0 ≤ energy x ∧ energy x ≤ (N : ℝ) * a ^ 2 := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  · calc
      energy x ≤ ∑ _i : Fin N, a ^ 2 :=
        Finset.sum_le_sum (fun i _ => coordinate_sq_le ⟨hx.1 i, hx.2 i⟩)
      _ = _ := by simp

theorem snap_idempotent {a ρ : ℝ} (ha : 0 ≤ a) (x : Fin N → ℝ) :
    snap a ρ (snap a ρ x) = snap a ρ x := by
  funext i
  by_cases h : a - |x i| ≤ ρ
  · have he : |snap a ρ x i| = a := by
      simp only [snap, if_pos h, endpoint_abs ha]
    exact snap_preserves_frozen (snap a ρ x) i he
  · simp only [snap, if_neg h]

theorem vertex_iff_no_live {a : ℝ} (ha : 0 ≤ a)
    {x : Fin N → ℝ} (hx : x ∈ ksCube a) :
    ksVertex a x ↔ ∀ i, ¬ |x i| < a := by
  constructor
  · intro hv i
    rcases hv i with h | h <;> simp [h, abs_of_nonneg ha]
  · intro hl i
    have habs : |x i| = a := le_antisymm (abs_le.mpr ⟨hx.1 i, hx.2 i⟩)
      (not_lt.mp (hl i))
    rcases le_total 0 (x i) with h | h
    · right
      rwa [abs_of_nonneg h] at habs
    · left
      rw [abs_of_nonpos h] at habs
      linarith

end MatrixSpencer.KSCubePreparation
