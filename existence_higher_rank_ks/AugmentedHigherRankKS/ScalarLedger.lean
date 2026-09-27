import Mathlib

/-! Exact scalar-coordinate identities for the augmented-reserve controller.
These lemmas contain no analytic or oracle assumptions. The shared matrix
epoch-state implementation is owned by the companion existence project. -/

open scoped BigOperators
namespace AugmentedHigherRankKS.ScalarLedger


def FeasibleCoordinate (a R x s c : ℝ) : Prop :=
  -1 ≤ x ∧ x ≤ 1 ∧ 0 ≤ s ∧ s ≤ R ∧ 0 ≤ c ∧ c ≤ a * R ∧
    c + a * s ≤ a * R ∧ (1 - x ^ 2) * (c + a * s - a * R) = 0

theorem interior_balance {a R x s c : ℝ}
    (h : FeasibleCoordinate a R x s c) (hx : |x| < 1) :
    c + a * s = a * R := by
  have hx0 : 0 < 1 - x ^ 2 := by
    obtain ⟨hl, hu⟩ := abs_lt.mp hx
    nlinarith [sq_nonneg x]
  have he := h.2.2.2.2.2.2.2
  have hz : c + a * s - a * R = 0 :=
    (mul_eq_zero.mp he).resolve_left (ne_of_gt hx0)
  linarith

theorem preparation_feasible {a R x s c t : ℝ}
    (h : FeasibleCoordinate a R x s c) (ha : 0 < a)
    (ht : 0 ≤ t) (htc : t ≤ c) :
    FeasibleCoordinate a R x (s + t / a) (c - t) := by
  obtain ⟨hxl, hxu, hs0, hsR, hc0, hcR, hbudget, hface⟩ := h
  have hta : 0 ≤ t / a := div_nonneg ht (le_of_lt ha)
  have hid : c - t + a * (s + t / a) = c + a * s := by
    field_simp
    <;> ring
  refine ⟨hxl, hxu, by linarith, ?_, by linarith, by linarith, ?_, ?_⟩
  · have hb : a * (s + t / a) ≤ a * R := by linarith [hid]
    exact (mul_le_mul_iff_right₀ ha).mp hb
  · rw [hid]
    exact hbudget
  · rw [hid]
    exact hface

theorem centered_feasible {a R x s c u : ℝ}
    (h : FeasibleCoordinate a R x s c) (ha : 0 < a)
    (hbalance : c + a * s = a * R)
    (hxl : -1 ≤ x + u) (hxu : x + u ≤ 1) (hcu : a * u ^ 2 ≤ c) :
    FeasibleCoordinate a R (x + u) (s + u ^ 2) (c - a * u ^ 2) := by
  obtain ⟨_, _, hs0, hsR, hc0, hcR, _, _⟩ := h
  have hu : 0 ≤ u ^ 2 := sq_nonneg u
  have hau : 0 ≤ a * u ^ 2 := mul_nonneg (le_of_lt ha) hu
  have he : c - a * u ^ 2 + a * (s + u ^ 2) = a * R := by
    nlinarith [hbalance]
  refine ⟨hxl, hxu, by linarith, ?_, by linarith, by linarith, by linarith, ?_⟩
  · have hb : a * (s + u ^ 2) ≤ a * R := by linarith
    exact (mul_le_mul_iff_right₀ ha).mp hb
  · rw [he]
    simp

theorem face_cleanup_feasible {a R x s c σ : ℝ}
    (h : FeasibleCoordinate a R x s c) (hσ : σ = -1 ∨ σ = 1) :
    FeasibleCoordinate a R σ s 0 := by
  obtain ⟨_, _, hs0, hsR, hc0, hcR, hbudget, _⟩ := h
  have haR : 0 ≤ a * R := hc0.trans hcR
  rcases hσ with rfl | rfl <;>
    refine ⟨by norm_num, by norm_num, hs0, hsR, le_rfl, haR, ?_, by norm_num⟩ <;>
    linarith

theorem floor_cleanup_spent {a R x s c : ℝ}
    (h : FeasibleCoordinate a R x s c) (ha : 0 < a) (hx : |x| < 1) :
    s + c / a = R := by
  have hb := interior_balance h hx
  apply (mul_left_cancel₀ (ne_of_gt ha))
  field_simp
  <;> nlinarith [hb]

theorem centered_budget_identity (x0 x s u : ℝ) :
    x0 ^ 2 - (x + u) ^ 2 + (s + u ^ 2) =
      (x0 ^ 2 - x ^ 2 + s) - 2 * x * u := by ring

theorem centered_reserve_identity (a s c u : ℝ) :
    (c - a * u ^ 2) + a * (s + u ^ 2) = c + a * s := by ring

theorem terminal_unfinished_spent {a R x s : ℝ}
    (h : FeasibleCoordinate a R x s 0) (ha : 0 < a) (hx : |x| < 1) :
    s = R := by
  have hb := interior_balance h hx
  nlinarith

section Finite
variable {ι : Type*} [Fintype ι]

def energy (x : ι → ℝ) : ℝ := ∑ i, (x i) ^ 2

theorem centered_energy (x g : ι → ℝ) (h : ℝ)
    (horth : ∑ i, x i * g i = 0) (hunit : ∑ i, (g i) ^ 2 = 1) :
    energy (fun i => x i + h * g i) = energy x + h ^ 2 := by
  unfold energy
  calc
    _ = ∑ i, ((x i) ^ 2 + (2 * h) * (x i * g i) + h ^ 2 * (g i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, (x i) ^ 2) + (2 * h) * (∑ i, x i * g i) +
        h ^ 2 * (∑ i, (g i) ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [horth, hunit]; ring

theorem energy_nonnegative (x : ι → ℝ) : 0 ≤ energy x :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

theorem energy_le_card (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    energy x ≤ Fintype.card ι := by
  have hs : ∀ i, (x i) ^ 2 ≤ 1 := by
    intro i
    obtain ⟨hl, hu⟩ := abs_le.mp (hx i)
    nlinarith [sq_nonneg (x i)]
  calc
    energy x ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hs i)
    _ = _ := by simp

end Finite
end AugmentedHigherRankKS.ScalarLedger
