import MatrixSpencer.FiniteHalfPhase
import MatrixSpencer.PartialColoringIteration
import Mathlib.Algebra.Order.Floor.Ring

/-!
# One global epoch duration for the rectangular argument

These scalar lemmas take a response coefficient `B ≥ 2` fixed for the entire
construction. The finite-assembly lemmas retain the actual continuation and
moment hypotheses explicitly; this module does not assert a general-order
matrix walk or the rectangular signing theorem.
-/

open scoped BigOperators
noncomputable section

namespace MatrixSpencer
namespace RectangularEpochParameters

/-- The same duration is used at every retained label count. -/
def duration (B : ℝ) : ℝ := 1 / (B + 1)

/-- A natural ceiling strictly exceeding the time/freezing progress budget. -/
def count (B : ℝ) : ℕ := Nat.ceil (32 * (B + 1) + 129)

/-- The compensated energy rate includes the fixed Taylor-error allowance. -/
def energyRate (B k : ℝ) : ℝ :=
  B * Real.sqrt k + Real.sqrt k / (200 * duration B)

/-- The scalar value can later be instantiated by certificate plus paid trace. -/
def energyAccount (B k value time rounding : ℝ) : ℝ :=
  value - energyRate B k * time - 2 * rounding

theorem duration_pos {B : ℝ} (hB : 2 ≤ B) : 0 < duration B := by
  unfold duration
  exact div_pos (by norm_num) (by linarith)

theorem duration_le_third {B : ℝ} (hB : 2 ≤ B) : duration B ≤ 1 / 3 := by
  unfold duration
  apply (div_le_iff₀ (show 0 < B + 1 by linarith)).mpr
  linarith

theorem duration_le_one {B : ℝ} (hB : 2 ≤ B) : duration B ≤ 1 :=
  (duration_le_third hB).trans (by norm_num)

theorem response_duration_le_one {B : ℝ} (hB : 2 ≤ B) :
    B * duration B ≤ 1 := by
  have hden : 0 < B + 1 := by linarith
  unfold duration
  rw [mul_one_div]
  exact (div_le_one hden).mpr (by linarith)

theorem inverse_duration {B : ℝ} (hB : 2 ≤ B) :
    32 / duration B = 32 * (B + 1) := by
  have hden : B + 1 ≠ 0 := by linarith
  unfold duration
  field_simp

theorem count_sufficient {B : ℝ} (hB : 2 ≤ B) :
    32 / duration B + 128 < (count B : ℝ) := by
  rw [inverse_duration hB]
  have hceil := Nat.le_ceil (32 * (B + 1) + 129)
  change 32 * (B + 1) + 128 < (Nat.ceil (32 * (B + 1) + 129) : ℝ)
  linarith

theorem count_le {B : ℝ} (hB : 2 ≤ B) :
    (count B : ℝ) ≤ 76 * (B + 1) := by
  have harg : 0 ≤ 32 * (B + 1) + 129 := by linarith
  have hceil := Nat.ceil_lt_add_one harg
  change (Nat.ceil (32 * (B + 1) + 129) : ℝ) ≤ 76 * (B + 1)
  linarith

theorem energyRate_nonneg {B k : ℝ} (hB : 2 ≤ B) :
    0 ≤ energyRate B k := by
  have hτ := duration_pos hB
  have hB0 : 0 ≤ B := by linarith
  unfold energyRate
  positivity

theorem energyRate_duration {B k : ℝ} (hB : 2 ≤ B) :
    energyRate B k * duration B =
      B * duration B * Real.sqrt k + Real.sqrt k / 200 := by
  have hτ : duration B ≠ 0 := ne_of_gt (duration_pos hB)
  unfold energyRate
  field_simp

/-- The same numerical compensation allowance works for every `B ≥ 2`. -/
theorem compensation_le {B k time rounding : ℝ} (hB : 2 ≤ B)
    (hk : 1 ≤ Real.sqrt k) (htime : time ≤ duration B)
    (hrounding : rounding ≤ 1 / 1000) :
    energyRate B k * time + 2 * rounding ≤ (101 / 100 : ℝ) * Real.sqrt k := by
  have ht := mul_le_mul_of_nonneg_left htime (energyRate_nonneg (k := k) hB)
  have hb := mul_le_mul_of_nonneg_right (response_duration_le_one hB)
    (Real.sqrt_nonneg k)
  rw [energyRate_duration hB] at ht
  linarith

theorem value_le_account_add {B k value time rounding : ℝ} (hB : 2 ≤ B)
    (hk : 1 ≤ Real.sqrt k) (htime : time ≤ duration B)
    (hrounding : rounding ≤ 1 / 1000) :
    value ≤ energyAccount B k value time rounding + (101 / 100 : ℝ) * Real.sqrt k := by
  have h := compensation_le hB hk htime hrounding
  unfold energyAccount
  linarith

/-- A finite compensated moment gives the unchanged `3.01 sqrt(k)` value budget. -/
theorem combined_moment_of_account {σ : Type*} [Fintype σ]
    {B k : ℝ} (hB : 2 ≤ B) (hk : 1 ≤ Real.sqrt k)
    (w value time rounding : σ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (htime : ∀ i, time i ≤ duration B) (hrounding : ∀ i, rounding i ≤ 1 / 1000)
    (haccount : (∑ i, w i * energyAccount B k (value i) (time i) (rounding i)) ≤
      2 * Real.sqrt k) :
    (∑ i, w i * value i) ≤ (301 / 100 : ℝ) * Real.sqrt k := by
  calc
    _ ≤ ∑ i, w i * (energyAccount B k (value i) (time i) (rounding i) +
        (101 / 100 : ℝ) * Real.sqrt k) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (value_le_account_add hB hk (htime i) (hrounding i)) (hw i))
    _ = (∑ i, w i * energyAccount B k (value i) (time i) (rounding i)) +
        (101 / 100 : ℝ) * Real.sqrt k := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
    _ ≤ _ := by linarith

/-- The same duration also preserves the original scalar tangent variance budget. -/
theorem tangent_moment_of_account {σ : Type*} [Fintype σ]
    {B k : ℝ} (hB : 2 ≤ B) (hk : 0 ≤ k)
    (w tangent time : σ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (htime : ∀ i, time i ≤ duration B)
    (haccount : (∑ i, w i * (tangent i ^ 2 - k * time i)) ≤ 0) :
    (∑ i, w i * tangent i ^ 2) ≤ k := by
  have hcap : ∀ i, k * time i ≤ k := by
    intro i
    calc
      _ ≤ k * duration B := mul_le_mul_of_nonneg_left (htime i) hk
      _ ≤ k * 1 := mul_le_mul_of_nonneg_left (duration_le_one hB) hk
      _ = k := mul_one k
  calc
    _ ≤ ∑ i, w i * ((tangent i ^ 2 - k * time i) + k) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      linarith [hcap i]
    _ = (∑ i, w i * (tangent i ^ 2 - k * time i)) + k := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
    _ ≤ _ := by linarith

/-- Instantiation of the existing finite half-phase ledger with the global duration.
The actual continuation is retained as an explicit hypothesis. -/
theorem exists_half_terminal_of_continuation {ι : Type*} [Fintype ι]
    (potential : EuclideanSpace ℝ ι → ℝ)
    (step : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → Prop)
    (invariant : EuclideanSpace ℝ ι → Prop)
    {B K : ℝ} (hB : 2 ≤ B) (hK : 0 ≤ K) (hk : 0 < Fintype.card ι)
    (continuation : ∀ x, FiniteHalfPhase.Cube x → invariant x → ¬FiniteHalfPhase.Terminal x →
      ∃ y time, step x y ∧ invariant y ∧
        FiniteHalfPhase.EpochAdvance potential (duration B) K x y time)
    (start : EuclideanSpace ℝ ι) (hstart : FiniteHalfPhase.Cube start)
    (hstartInv : invariant start) :
    ∃ finish, Relation.ReflTransGen step start finish ∧ FiniteHalfPhase.Cube finish ∧
      invariant finish ∧ frozenCoordinates start ⊆ frozenCoordinates finish ∧
      FiniteHalfPhase.Terminal finish ∧
      potential finish ≤ potential start + (76 * K * (B + 1)) *
        Real.sqrt (Fintype.card ι : ℝ) := by
  obtain ⟨finish, hreach, hcube, hinv, hfrozen, hterminal, hcost⟩ :=
    FiniteHalfPhase.exists_terminal_of_epoch_continuation potential step invariant K hK
      (duration_pos hB) hk (count B) (count_sufficient hB) continuation start hstart hstartInv
  refine ⟨finish, hreach, hcube, hinv, hfrozen, hterminal, hcost.trans ?_⟩
  have hcount := mul_le_mul_of_nonneg_left (count_le hB) hK
  have htotal := mul_le_mul_of_nonneg_right hcount
    (Real.sqrt_nonneg (Fintype.card ι : ℝ))
  nlinarith

/-- Generic outer assembly with a uniform half-phase cost coefficient.
Every phase must still supply the actual invariant-preserving half reduction. -/
theorem exists_terminal_of_half_phases {State : Type*}
    (live : State → ℕ) (potential : State → ℝ) (invariant : State → Prop)
    (step : State → State → Prop) {B K : ℝ} (hB : 2 ≤ B) (hK : 0 ≤ K)
    (phase : ∀ s, invariant s → 0 < live s →
      ∃ s', step s s' ∧ invariant s' ∧ (live s' : ℝ) ≤ (live s : ℝ) / 2 ∧
        potential s' ≤ potential s + (76 * K * (B + 1)) * Real.sqrt (live s))
    (start : State) (hstart : invariant start) :
    ∃ finish, Relation.ReflTransGen step start finish ∧ invariant finish ∧ live finish = 0 ∧
      potential finish ≤ potential start + (304 * K * (B + 1)) * Real.sqrt (live start) := by
  have hconstant : 0 ≤ 76 * K * (B + 1) := by
    have : 0 ≤ B + 1 := by linarith
    positivity
  have hphase : ∀ s, invariant s → 0 < live s →
      ∃ s', step s s' ∧ invariant s' ∧
        (live s' : ℝ) ≤ (1 - (1 / 2 : ℝ)) * live s ∧
        potential s' ≤ potential s + (76 * K * (B + 1)) * Real.sqrt (live s) := by
    intro s hs hk
    obtain ⟨s', hstep, hinv, hshrink, hcost⟩ := phase s hs hk
    exact ⟨s', hstep, hinv, by linarith, hcost⟩
  obtain ⟨finish, hreach, hinv, hzero, hcost⟩ :=
    PartialColoringIteration.exists_terminal_of_phases live potential invariant step
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      hconstant hphase start hstart
  refine ⟨finish, hreach, hinv, hzero, ?_⟩
  convert hcost using 1; ring

end RectangularEpochParameters
end MatrixSpencer
