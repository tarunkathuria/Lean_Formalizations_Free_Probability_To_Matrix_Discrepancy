import MatrixSpencer.RectangularRidgeRemainingPotential
import MatrixSpencer.RectangularRidgeUniformResponse
import MatrixSpencer.RectangularEpochParameters
import MatrixSpencer.MSManuscriptPhaseProgress

/-!
# Fixed-universe half-phase progress

The live count at the start of a phase, rather than the original ambient
count, normalizes the available norm and freezing ledgers. The duration and
regularizer remain fixed at their original input parameters.
-/
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RectangularRidgePhaseProgress
open RectangularRidgeRemainingPotential
variable {N : ℕ}

theorem frozen_card_le_norm_sq (x : EuclideanSpace ℝ (Fin N)) :
    ((frozenCoordinates x).card : ℝ) ≤ ‖x‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ = ∑ i ∈ frozenCoordinates x, ‖x i‖ ^ 2 := by
      have he : ∀ i ∈ frozenCoordinates x, ‖x i‖ ^ 2 = (1 : ℝ) := by
        intro i hi
        rcases (mem_frozenCoordinates x i).mp hi with h | h <;> rw [h] <;> norm_num
      simp only [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)

def terminal (start x : EuclideanSpace ℝ (Fin N)) : Prop :=
  2 * liveCount x ≤ liveCount start ∨ liveCount x < 32

def progress (τ : ℝ) (start x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  ((32 / τ) * (‖x‖ ^ 2 - (frozenCoordinates start).card) +
    128 * ((frozenCoordinates x).card - (frozenCoordinates start).card : ℝ)) /
      liveCount start

theorem liveCount_cast (x : EuclideanSpace ℝ (Fin N)) :
    (liveCount x : ℝ) = N - (frozenCoordinates x).card := by
  rw [liveCount, RectangularRidgeLiveOwner.count_eq, Nat.cast_sub]
  simpa only [Fintype.card_fin] using frozenCoordinates_card_le x

theorem progress_nonneg {τ : ℝ} (hτ : 0 < τ)
    {start x : EuclideanSpace ℝ (Fin N)} (hx : frozenCoordinates start ⊆ frozenCoordinates x) :
    0 ≤ progress τ start x := by
  have hf : ((frozenCoordinates start).card : ℝ) ≤ (frozenCoordinates x).card :=
    Nat.cast_le.mpr (Finset.card_le_card hx)
  have hn := frozen_card_le_norm_sq x
  unfold progress
  exact div_nonneg (add_nonneg (mul_nonneg (by positivity) (by linarith))
    (mul_nonneg (by norm_num) (sub_nonneg.mpr hf))) (Nat.cast_nonneg _)

theorem progress_le {τ : ℝ} (hτ : 0 < τ)
    (start : EuclideanSpace ℝ (Fin N)) (hs : 0 < liveCount start)
    {x : EuclideanSpace ℝ (Fin N)} (hx : FiniteHalfPhase.Cube x) :
    progress τ start x ≤ 32 / τ + 128 := by
  have hℓ : (0 : ℝ) < liveCount start := Nat.cast_pos.mpr hs
  have hn := cube_euclidean_norm_sq_le_card hx
  have hf : ((frozenCoordinates x).card : ℝ) ≤ N := by
    exact_mod_cast (show (frozenCoordinates x).card ≤ N by simpa using frozenCoordinates_card_le x)
  simp only [Fintype.card_fin] at hn
  have hc : 0 ≤ (32 : ℝ) / τ := by positivity
  have hm := mul_le_mul_of_nonneg_left
    (show ‖x‖ ^ 2 - (frozenCoordinates start).card ≤
      (N : ℝ) - (frozenCoordinates start).card by linarith) hc
  unfold progress
  apply (div_le_iff₀ hℓ).mpr
  rw [liveCount_cast]
  nlinarith

/-- A successful actual epoch increases the relative phase ledger by one.
The record contains concrete elapsed time, norm gain, and newly frozen labels. -/
theorem progress_advance {τ K time : ℝ} (hτ : 0 < τ)
    {f : EuclideanSpace ℝ (Fin N) → ℝ}
    {start x y : EuclideanSpace ℝ (Fin N)} (hs : 0 < liveCount start)
    (h : FiniteHalfPhase.EpochAdvance f τ K x y time) (hx : ¬terminal start x) :
    progress τ start x + 1 ≤ progress τ start y := by
  have hℓ : (0 : ℝ) < liveCount start := Nat.cast_pos.mpr hs
  have hl : (liveCount start : ℝ) ≤ 2 * liveCount x := by
    have hh : liveCount start < 2 * liveCount x := lt_of_not_ge (fun h' => hx (Or.inl h'))
    exact le_of_lt (by exact_mod_cast hh)
  have hg := h.norm_progress
  have ht := h.successful
  have hc : 0 ≤ (32 : ℝ) / τ := by positivity
  have hcτ : ((32 : ℝ) / τ) * τ = 32 := by field_simp
  have he : (FiniteHalfPhase.liveCount x : ℝ) = liveCount x := by
    simp only [FiniteHalfPhase.liveCount, liveCount, RectangularRidgeLiveOwner.count_eq,
      Fintype.card_fin]
  rw [he] at hg ht
  have hg' : ‖x‖ ^ 2 + (liveCount start : ℝ) / 32 * time ≤ ‖y‖ ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * (liveCount x : ℝ) - liveCount start by linarith)
      h.time_nonneg]
  have hg0 : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    nlinarith [mul_nonneg hℓ.le h.time_nonneg]
  have hf : ((frozenCoordinates x).card : ℝ) ≤ (frozenCoordinates y).card :=
    Nat.cast_le.mpr (Finset.card_le_card h.frozen)
  unfold progress
  rw [← div_self hℓ.ne', ← add_div, div_le_div_iff_of_pos_right hℓ]
  rcases ht with ht | hf'
  · have hm := mul_le_mul_of_nonneg_left
      (show (liveCount start : ℝ) * τ ≤ 32 * (‖y‖ ^ 2 - ‖x‖ ^ 2) by nlinarith) hc
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hg0 hc
    nlinarith

/-- The same original-input duration gives a polynomial number of epochs,
independently of how few coordinates remain live in this phase. -/
theorem uniform_epoch_count {D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    32 / RectangularRidgeUniformResponse.duration N D hN + 128 <
        (RectangularEpochParameters.count (RectangularRidgeUniformResponse.coefficient N D hN) : ℝ) ∧
      (RectangularEpochParameters.count (RectangularRidgeUniformResponse.coefficient N D hN) : ℝ) ≤
        76 * RectangularRidgeNumericalParameters.phaseResponse
          (RectangularRidgeNumericalOptimizerFloor.size D N) := by
  have hB := RectangularRidgeUniformResponse.coefficient_two_le hN hND
  exact ⟨RectangularEpochParameters.count_sufficient hB,
    (RectangularEpochParameters.count_le hB).trans (mul_le_mul_of_nonneg_left
      (RectangularRidgeUniformResponse.polynomial_coefficient_le hN hND) (by norm_num))⟩

/-- A finite mesh reaches half the operational duration; this count uses
that established threshold, including the clock's final mesh interval. -/
def epochCalls (N D : ℕ) (hN : 1 ≤ N) : ℕ :=
  RectangularEpochParameters.count (2 * RectangularRidgeUniformResponse.coefficient N D hN + 1)

theorem epochCalls_sufficient {D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    32 / (RectangularRidgeUniformResponse.duration N D hN / 2) + 128 <
      (epochCalls N D hN : ℝ) := by
  have hB := RectangularRidgeUniformResponse.coefficient_two_le hN hND
  have hb : 2 ≤ 2 * RectangularRidgeUniformResponse.coefficient N D hN + 1 := by linarith
  have he : RectangularEpochParameters.duration
      (2 * RectangularRidgeUniformResponse.coefficient N D hN + 1) =
        RectangularRidgeUniformResponse.duration N D hN / 2 := by
    unfold RectangularEpochParameters.duration RectangularRidgeUniformResponse.duration
    field_simp
    ring
  simpa only [epochCalls, he] using RectangularEpochParameters.count_sufficient hb

theorem epochCalls_le {D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    (epochCalls N D hN : ℝ) ≤
      152 * (RectangularRidgeUniformResponse.coefficient N D hN + 1) := by
  have hB := RectangularRidgeUniformResponse.coefficient_two_le hN hND
  have hb : 2 ≤ 2 * RectangularRidgeUniformResponse.coefficient N D hN + 1 := by linarith
  have hh := RectangularEpochParameters.count_le hb
  change (epochCalls N D hN : ℝ) ≤ _ at hh
  linarith

theorem epochCalls_polynomial {D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    (epochCalls N D hN : ℝ) ≤ 152 * RectangularRidgeNumericalParameters.phaseResponse
      (RectangularRidgeNumericalOptimizerFloor.size D N) :=
  (epochCalls_le hN hND).trans (mul_le_mul_of_nonneg_left
    (RectangularRidgeUniformResponse.polynomial_coefficient_le hN hND) (by norm_num))

/-- The actual outer process uses `N+1` half phases. Its total selected
epoch calls fit the explicit numerical ledger used for amplification. -/
theorem total_epochCalls_le {D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    ((N + 1 : ℕ) : ℝ) * epochCalls N D hN ≤
      RectangularRidgeNumericalParameters.selectedEpochs
        (RectangularRidgeNumericalOptimizerFloor.size D N) := by
  let P := RectangularRidgeNumericalOptimizerFloor.size D N
  have hP : 0 ≤ P := by dsimp [P, RectangularRidgeNumericalOptimizerFloor.size]; positivity
  have hNP : ((N + 1 : ℕ) : ℝ) ≤ P := by
    dsimp [P, RectangularRidgeNumericalOptimizerFloor.size]
    push_cast
    linarith [show (0 : ℝ) ≤ D from Nat.cast_nonneg D]
  have hc := epochCalls_polynomial hN hND
  change (epochCalls N D hN : ℝ) ≤ 152 * RectangularRidgeNumericalParameters.phaseResponse P at hc
  have hh := mul_le_mul hc hNP (Nat.cast_nonneg _) (by
    unfold RectangularRidgeNumericalParameters.phaseResponse RectangularRidgeNumericalParameters.big
    positivity : 0 ≤ 152 * RectangularRidgeNumericalParameters.phaseResponse P)
  calc
    _ = (epochCalls N D hN : ℝ) * ((N + 1 : ℕ) : ℝ) := mul_comm _ _
    _ ≤ (152 * RectangularRidgeNumericalParameters.phaseResponse P) * P := hh
    _ ≤ RectangularRidgeNumericalParameters.selectedEpochs P := by
      norm_num [RectangularRidgeNumericalParameters.phaseResponse,
        RectangularRidgeNumericalParameters.selectedEpochs,
        RectangularRidgeNumericalParameters.big]
      nlinarith [pow_nonneg hP 4]

end MatrixSpencer.RectangularRidgePhaseProgress
