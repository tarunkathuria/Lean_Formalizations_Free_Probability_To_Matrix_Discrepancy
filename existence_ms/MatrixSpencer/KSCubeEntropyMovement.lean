import MatrixSpencer.KSCubeEntropy
import MatrixSpencer.KSDebitMovement

/-!
# Entropy progress of the actual weighted movement

The scalar entropy estimate is summed over the original labels. Frozen
coordinates remain fixed and have zero entropy. Actual endpoint preparation
only replaces coordinates by endpoints, so it cannot increase entropy.
-/

open Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSCubeEntropyMovement

open KSCubeEntropy KSDebitMovement
variable {N : ℕ}

def entropy (x : Fin N → ℝ) : ℝ := ∑ i, u (x i)

theorem entropy_bounds {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    0 ≤ entropy x ∧ entropy x ≤ (N : ℝ) * (2 * Real.log 2) := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => (bounds (abs_le.mpr ⟨hx.1 i, hx.2 i⟩)).1)
  · calc
      entropy x ≤ ∑ _i : Fin N, 2 * Real.log 2 :=
        Finset.sum_le_sum (fun i _ => (bounds (abs_le.mpr ⟨hx.1 i, hx.2 i⟩)).2)
      _ = _ := by simp

@[simp] theorem u_eq_zero_of_endpoint {x : ℝ} (hx : |x| = 1) : u x = 0 := by
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hx with h | h <;> rw [h] <;> simp

/-- A prepared coordinate either remains unchanged or becomes an endpoint;
each endpoint has entropy zero and every cube coordinate has nonnegative entropy. -/
theorem prepare_entropy_nonincreasing (η : ℝ) (report : (Fin N → ℝ) → ℝ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    entropy (KSDebitPreparation.prepare η report x) ≤ entropy x := by
  apply Finset.sum_le_sum
  intro i _
  rcases KSEighthPreparedState.prepare_eq_or_endpoint (by norm_num : (0 : ℝ) ≤ 1)
    (τ := -η) report N x i with he | he
  · change u (KSEighthRetirementLoop.prepare 1 (-η) report N x i) ≤ u (x i)
    rw [he]
  · change u (KSEighthRetirementLoop.prepare 1 (-η) report N x i) ≤ u (x i)
    rw [u_eq_zero_of_endpoint he]
    exact (bounds (abs_le.mpr ⟨hx.1 i, hx.2 i⟩)).1

/-- The weighted displacement cancels the denominator in the scalar entropy
drop. Summing the live direction's squared coordinates therefore gives exactly
the normalized movement gain `t²`, without a factor of the live margin. -/
theorem proposal_entropy_drop (x : Fin N → ℝ) (hx : x ∈ ksCube 1)
    (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖ = 1)
    (hfrozen : ∀ i, |x i| = 1 → v i = 0) {δ t : ℝ}
    (hδ : 0 < δ) (ht : |t| ≤ δ / 4)
    (hmargin : ∀ i, |x i| < 1 → δ < 1 - |x i|) :
    (entropy (proposal x v t) + entropy (proposal x v (-t))) / 2 ≤ entropy x - t ^ 2 := by
  have hcoord (i : Fin N) :
      (u (proposal x v t i) + u (proposal x v (-t) i)) / 2 ≤ u (x i) - t ^ 2 * (v i) ^ 2 := by
    have hi : |x i| ≤ 1 := abs_le.mpr ⟨hx.1 i, hx.2 i⟩
    rcases lt_or_eq_of_le hi with hi | hi
    · let r := t * (Real.sqrt (1 - x i ^ 2) * v i)
      have hr : |r| < 1 - |x i| := by
        have hd := proposal_displacement_le x v hv t i
        rw [proposal_apply, add_sub_cancel_left] at hd
        have hm := hmargin i hi
        dsimp only [r]
        linarith
      have hp := symmetric_drop hi hr
      have ha := one_sub_sq_pos hi
      have hrat : r ^ 2 / (1 - x i ^ 2) = t ^ 2 * (v i) ^ 2 := by
        apply (div_eq_iff ha.ne').mpr
        dsimp only [r]
        rw [mul_pow, mul_pow, Real.sq_sqrt ha.le]
        ring
      rw [hrat] at hp
      simpa only [proposal_apply, neg_mul, ← sub_eq_add_neg, r] using hp
    · rw [proposal_preserves_frozen x v t i hi, proposal_preserves_frozen x v (-t) i hi,
        hfrozen i hi, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero]
      linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hcoord i)
  have hnorm : (∑ i, (v i) ^ 2) = 1 := by
    have hh := EuclideanSpace.norm_sq_eq v
    rw [hv] at hh
    simpa only [one_pow, Real.norm_eq_abs, sq_abs] using hh.symm
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hnorm, mul_one] at hsum
  exact hsum

/-- The actual proposal followed by exhaustive endpoint preparation retains
the full entropy drop for the uniform random sign. -/
theorem prepared_entropy_drop (η : ℝ) (report : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℝ) (hx : x ∈ ksCube 1)
    (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖ = 1)
    (hfrozen : ∀ i, |x i| = 1 → v i = 0) {δ t : ℝ}
    (hδ : 0 < δ) (ht : |t| ≤ δ / 4)
    (hmargin : ∀ i, |x i| < 1 → δ < 1 - |x i|) :
    (entropy (KSDebitPreparation.prepare η report (proposal x v t)) +
      entropy (KSDebitPreparation.prepare η report (proposal x v (-t)))) / 2 ≤ entropy x - t ^ 2 := by
  have hp := proposal_entropy_drop x hx v hv hfrozen hδ ht hmargin
  have hplus := prepare_entropy_nonincreasing η report (proposal_mem_cube x hx v hv hδ ht hmargin)
  have hminus := prepare_entropy_nonincreasing η report
    (proposal_mem_cube x hx v hv (t := -t) hδ (by simpa only [abs_neg] using ht) hmargin)
  linarith

end MatrixSpencer.KSCubeEntropyMovement
