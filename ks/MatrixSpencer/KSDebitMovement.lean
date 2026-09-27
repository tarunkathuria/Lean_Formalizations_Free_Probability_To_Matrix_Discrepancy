import MatrixSpencer.KSDebitPreparation
import MatrixSpencer.KSSymmetricProgress

/-!
# Geometry of the full-cube movement with the actual debit

The proposal is exactly `x + t D(x)^(1/2) v`. With a positive live margin,
a unit vector supported on live labels, and a sufficiently small step, both
coin outcomes stay in the same open face. Thus old endpoints stay fixed and
the debit remains exactly unchanged during the movement. The symmetric
average has positive squared-norm progress without radial orthogonality.
The numerical direction and the potential drift are separate obligations.
-/

open Set
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.KSDebitMovement

open KSSymmetricProgress
variable {N : ℕ}

def proposal (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin N)) (t : ℝ) : Fin N → ℝ :=
  WithLp.ofLp ((WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N)) + t • weightedDirection x v)

theorem proposal_apply (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin N)) (t : ℝ) (i : Fin N) :
    proposal x v t i = x i + t * (Real.sqrt (1 - x i ^ 2) * v i) := rfl

theorem proposal_preserves_frozen (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin N))
    (t : ℝ) (i : Fin N) (hi : |x i| = 1) : proposal x v t i = x i := by
  have hs : x i ^ 2 = 1 := by nlinarith [sq_abs (x i)]
  simp only [proposal_apply, hs, sub_self, Real.sqrt_zero, zero_mul, mul_zero, add_zero]

theorem proposal_displacement_le (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin N))
    (hv : ‖v‖ = 1) (t : ℝ) (i : Fin N) : |proposal x v t i - x i| ≤ |t| := by
  have hvone : |v i| ≤ 1 := by simpa only [Real.norm_eq_abs, hv] using PiLp.norm_apply_le v i
  have hs : Real.sqrt (1 - x i ^ 2) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    nlinarith [sq_nonneg (x i)]
  rw [proposal_apply, add_sub_cancel_left, abs_mul, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hm : Real.sqrt (1 - x i ^ 2) * |v i| ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - Real.sqrt (1 - x i ^ 2)) (abs_nonneg (v i))]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hm (abs_nonneg t)

theorem proposal_live_interior (x : Fin N → ℝ) (v : EuclideanSpace ℝ (Fin N))
    (hv : ‖v‖ = 1) {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ δ / 4)
    (i : Fin N) (hmargin : δ < 1 - |x i|) : |proposal x v t i| < 1 := by
  have hd := proposal_displacement_le x v hv t i
  have ha : |proposal x v t i| ≤ |x i| + |proposal x v t i - x i| := by
    calc
      _ = |x i + (proposal x v t i - x i)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  linarith

theorem proposal_mem_cube (x : Fin N → ℝ) (hx : x ∈ ksCube 1)
    (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖ = 1)
    {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ δ / 4)
    (hmargin : ∀ i, |x i| < 1 → δ < 1 - |x i|) : proposal x v t ∈ ksCube 1 := by
  have hall (i : Fin N) : |proposal x v t i| ≤ 1 := by
    have hi : |x i| ≤ 1 := abs_le.mpr ⟨hx.1 i, hx.2 i⟩
    rcases lt_or_eq_of_le hi with hi | hi
    · exact (proposal_live_interior x v hv hδ ht i (hmargin i hi)).le
    · rw [proposal_preserves_frozen x v t i hi, hi]
  exact ⟨fun i => (abs_le.mp (hall i)).1, fun i => (abs_le.mp (hall i)).2⟩

theorem proposal_frozen_eq (x : Fin N → ℝ) (hx : x ∈ ksCube 1)
    (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖ = 1)
    {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ δ / 4)
    (hmargin : ∀ i, |x i| < 1 → δ < 1 - |x i|) :
    ksFrozen 1 (proposal x v t) = ksFrozen 1 x := by
  ext i
  simp only [ksFrozen, Finset.mem_filter, Finset.mem_univ, true_and]
  have hi : |x i| ≤ 1 := abs_le.mpr ⟨hx.1 i, hx.2 i⟩
  rcases lt_or_eq_of_le hi with hi | hi
  · have hj := proposal_live_interior x v hv hδ ht i (hmargin i hi)
    exact iff_of_false (ne_of_lt hj) (ne_of_lt hi)
  · rw [proposal_preserves_frozen x v t i hi]

theorem proposal_debit_eq {n : Type*} [Fintype n] [DecidableEq n]
    (A : Fin N → Matrix n n ℂ) (η : ℝ) (x : Fin N → ℝ) (hx : x ∈ ksCube 1)
    (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖ = 1)
    {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ δ / 4)
    (hmargin : ∀ i, |x i| < 1 → δ < 1 - |x i|) :
    KSDebitBudget.debit A δ η (proposal x v t) = KSDebitBudget.debit A δ η x :=
  KSDebitBudget.debit_eq_of_same_frozen A δ η (proposal_frozen_eq x hx v hv hδ ht hmargin)

/-- The progress bound permits frozen original labels. Only the normalized
direction is required to have zero entries on those labels. -/
theorem weightedDirection_norm_sq_lower_live (x : Fin N → ℝ) (hx : x ∈ ksCube 1)
    (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖ = 1)
    (hfrozen : ∀ i, |x i| = 1 → v i = 0) {δ : ℝ}
    (hmargin : ∀ i, |x i| < 1 → δ ≤ 1 - |x i|) :
    δ ≤ ‖weightedDirection x v‖ ^ 2 := by
  have hsq (i : Fin N) : x i ^ 2 ≤ 1 :=
    by simpa only [one_pow] using KSCubePreparation.coordinate_sq_le ⟨hx.1 i, hx.2 i⟩
  have hsum : δ * ‖v‖ ^ 2 ≤ ‖weightedDirection x v‖ ^ 2 := by
    rw [weightedDirection_norm_sq x v hsq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simp only [Real.norm_eq_abs, sq_abs]
    have hi : |x i| ≤ 1 := abs_le.mpr ⟨hx.1 i, hx.2 i⟩
    rcases lt_or_eq_of_le hi with hi | hi
    · have hm := hmargin i hi
      have hb : δ ≤ 1 - x i ^ 2 := by
        nlinarith [sq_abs (x i), mul_nonneg (abs_nonneg (x i)) (by linarith : 0 ≤ 1 - |x i|)]
      exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    · simp only [hfrozen i hi, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
  simpa only [hv, one_pow, mul_one] using hsum

theorem symmetric_energy_progress (x : Fin N → ℝ) (hx : x ∈ ksCube 1)
    (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖ = 1)
    (hfrozen : ∀ i, |x i| = 1 → v i = 0) {δ : ℝ}
    (hmargin : ∀ i, |x i| < 1 → δ ≤ 1 - |x i|) (t : ℝ) :
    KSCubePreparation.energy x + δ * t ^ 2 ≤
      (KSCubePreparation.energy (proposal x v t) +
        KSCubePreparation.energy (proposal x v (-t))) / 2 := by
  have hw := weightedDirection_norm_sq_lower_live x hx v hv hfrozen hmargin
  simp only [energy_eq_norm_sq, proposal, WithLp.toLp_ofLp]
  rw [neg_smul, ← sub_eq_add_neg, symmetric_norm_sq]
  nlinarith [sq_nonneg t]

/-- Exhaustive numerical retirement after each legal proposal preserves its
progress. This is the actual composition used for the two successor states. -/
theorem prepared_symmetric_energy_progress (η : ℝ) (report : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℝ) (hx : x ∈ ksCube 1)
    (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖ = 1)
    (hfrozen : ∀ i, |x i| = 1 → v i = 0) {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ δ / 4)
    (hmargin : ∀ i, |x i| < 1 → δ < 1 - |x i|) :
    KSCubePreparation.energy x + δ * t ^ 2 ≤
      (KSCubePreparation.energy (KSDebitPreparation.prepare η report (proposal x v t)) +
        KSCubePreparation.energy (KSDebitPreparation.prepare η report (proposal x v (-t)))) / 2 := by
  have hp := symmetric_energy_progress x hx v hv hfrozen (fun i hi => (hmargin i hi).le) t
  have hl := KSDebitPreparation.prepare_energy_progress η report
    (proposal_mem_cube x hx v hv hδ ht hmargin)
  have hr := KSDebitPreparation.prepare_energy_progress η report
    (proposal_mem_cube x hx v hv (t := -t) hδ (by simpa only [abs_neg] using ht) hmargin)
  linarith

end MatrixSpencer.KSDebitMovement
