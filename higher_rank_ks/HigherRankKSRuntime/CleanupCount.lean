import HigherRankKSRuntime.Progress

/-! Every cleanup removes a positive reserve permanently within its epoch.
The resulting trace-length bound counts the concrete updates rather than
assuming a polynomial stopping time. -/

open scoped BigOperators
noncomputable section
namespace HigherRankKSRuntime
open AugmentedHigherRankKS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def activeOwners (z : EpochState ι) : Finset ι :=
  Finset.univ.filter (fun i => 0 < reserve z i)

def activeCount (z : EpochState ι) : ℕ := (activeOwners z).card

theorem activeCount_le_card (z : EpochState ι) : activeCount z ≤ Fintype.card ι :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem activeCount_mono {z w : EpochState ι}
    (h : ∀ i, reserve w i ≤ reserve z i) : activeCount w ≤ activeCount z := by
  apply Finset.card_le_card
  intro i hi
  simp only [activeOwners, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans_le (h i)

theorem prepareOwner_activeCount_le (a : ℝ) (z : EpochState ι) (i : ι)
    {step : ℝ} (hstep : 0 ≤ step) :
    activeCount (prepareOwner a z i step) ≤ activeCount z := by
  apply activeCount_mono
  intro j
  by_cases hj : j = i
  · subst j
    simp only [prepareOwner, preparation, reserve, Pi.single_eq_same]
    linarith
  · simp [prepareOwner, preparation, reserve, hj]

theorem movement_activeCount_le {a : ℝ} (ha : 0 ≤ a) (z : EpochState ι)
    (g : ι → ℝ) (h : ℝ) : activeCount (movement a z g h) ≤ activeCount z := by
  apply activeCount_mono
  intro i
  dsimp only [movement, reserve]
  have hp := mul_nonneg (mul_nonneg ha (sq_nonneg h)) (sq_nonneg (g i))
  linarith

theorem roundOwner_activeOwners (z : EpochState ι) (i : ι) :
    activeOwners (roundOwner z i) = (activeOwners z).erase i := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [activeOwners, roundOwner, reserve]
  · simp [activeOwners, roundOwner, reserve, hj, ne_comm]

theorem exhaustOwner_activeOwners (a : ℝ) (z : EpochState ι) (i : ι) :
    activeOwners (exhaustOwner a z i) = (activeOwners z).erase i := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [activeOwners]
  · simp [activeOwners, exhaustOwner, prepareOwner, preparation, reserve, hj, ne_comm]

theorem roundOwner_activeCount (z : EpochState ι) (i : ι) (hi : 0 < reserve z i) :
    activeCount (roundOwner z i) + 1 = activeCount z := by
  have hm : i ∈ activeOwners z := by simp [activeOwners, hi]
  simpa only [activeCount, roundOwner_activeOwners] using Finset.card_erase_add_one hm

theorem exhaustOwner_activeCount (a : ℝ) (z : EpochState ι) (i : ι)
    (hi : 0 < reserve z i) : activeCount (exhaustOwner a z i) + 1 = activeCount z := by
  have hm : i ∈ activeOwners z := by simp [activeOwners, hi]
  simpa only [activeCount, exhaustOwner_activeOwners] using Finset.card_erase_add_one hm

inductive CountedTrace (a R step h : ℝ) (start : EpochState ι) :
    EpochState ι → ℕ → ℕ → ℕ → Prop
  | nil : CountedTrace a R step h start start 0 0 0
  | prepare {z : EpochState ι} {walks preps cleanups : ℕ}
      (prior : CountedTrace a R step h start z walks preps cleanups) (i : ι) :
      CountedTrace a R step h start (prepareOwner a z i step) walks (preps + 1) cleanups
  | move {z : EpochState ι} {walks preps cleanups : ℕ}
      (prior : CountedTrace a R step h start z walks preps cleanups) (g : ι → ℝ)
      (orthogonal : ∑ i, position z i * g i = 0)
      (unit : ∑ i, (g i) ^ 2 = 1) :
      CountedTrace a R step h start (movement a z g h) (walks + 1) preps cleanups
  | round {z : EpochState ι} {walks preps cleanups : ℕ}
      (prior : CountedTrace a R step h start z walks preps cleanups)
      (feasible : z ∈ epochDomain a R) (i : ι) (active : 0 < reserve z i) :
      CountedTrace a R step h start (roundOwner z i) walks preps (cleanups + 1)
  | exhaust {z : EpochState ι} {walks preps cleanups : ℕ}
      (prior : CountedTrace a R step h start z walks preps cleanups)
      (feasible : z ∈ epochDomain a R) (i : ι) (active : 0 < reserve z i) :
      CountedTrace a R step h start (exhaustOwner a z i) walks preps (cleanups + 1)

theorem CountedTrace.toUpdateTrace {a R step h : ℝ} {start finish : EpochState ι}
    {walks preps cleanups : ℕ} (tr : CountedTrace a R step h start finish walks preps cleanups) :
    UpdateTrace a R step h start finish walks preps := by
  induction tr with
  | nil => exact .nil
  | prepare prior i ih => exact .prepare ih i
  | move prior g ho hu ih => exact .move ih g ho hu
  | round prior hz i hi ih => exact .round ih hz i
  | exhaust prior hz i hi ih => exact .exhaust ih hz i

theorem CountedTrace.cleanup_bound {a R step h : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ step)
    {start finish : EpochState ι} {walks preps cleanups : ℕ}
    (tr : CountedTrace a R step h start finish walks preps cleanups) :
    cleanups + activeCount finish ≤ activeCount start := by
  induction tr with
  | nil => simp
  | prepare prior i ih =>
    exact (Nat.add_le_add_left (prepareOwner_activeCount_le _ _ _ hs) _).trans ih
  | move prior g ho hu ih =>
    exact (Nat.add_le_add_left (movement_activeCount_le ha _ _ _) _).trans ih
  | round prior hz i hi ih =>
    have hc := roundOwner_activeCount _ i hi
    omega
  | exhaust prior hz i hi ih =>
    have hc := exhaustOwner_activeCount a _ i hi
    omega

theorem CountedTrace.length_bound {a R step h : ℝ} (ha : 0 ≤ a)
    (hs : 0 < step) (hh : h ≠ 0)
    {start finish : EpochState ι} {walks preps cleanups : ℕ}
    (tr : CountedTrace a R step h start finish walks preps cleanups)
    (hstart : start ∈ epochDomain a R) (hfinish : finish ∈ epochDomain a R) :
    (walks + preps + cleanups : ℝ) ≤
      (Fintype.card ι : ℝ) / h ^ 2 + (Fintype.card ι : ℝ) * (a * R) / step +
        (Fintype.card ι : ℝ) := by
  have hw := trace_walk_bound tr.toUpdateTrace hfinish
  have hp := trace_preparation_bound ha tr.toUpdateTrace hstart hfinish
  have hc := tr.cleanup_bound ha hs.le
  have hcn : cleanups ≤ Fintype.card ι := by
    have hc0 := activeCount_le_card start
    omega
  have hw' : (walks : ℝ) ≤ (Fintype.card ι : ℝ) / h ^ 2 :=
    (le_div_iff₀ (sq_pos_of_ne_zero hh)).mpr hw
  have hp' : (preps : ℝ) ≤ (Fintype.card ι : ℝ) * (a * R) / step :=
    (le_div_iff₀ hs).mpr hp
  have hc' : (cleanups : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcn
  linarith

end HigherRankKSRuntime
