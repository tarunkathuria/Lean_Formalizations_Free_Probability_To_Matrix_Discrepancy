import HigherRankKSRuntime.StateUpdates

/-! Deterministic pathwise resource accounting for the actual shared-state
updates. This module bounds finite execution traces; constructing the
controller's complete trace still requires its proved analytic decisions. -/

open scoped BigOperators
noncomputable section
namespace HigherRankKSRuntime
open AugmentedHigherRankKS
open AugmentedHigherRankKS.ScalarLedger

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def totalReserve (z : EpochState ι) : ℝ := ∑ i, reserve z i

theorem totalReserve_nonneg {a R : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) : 0 ≤ totalReserve z :=
  Finset.sum_nonneg (fun i _ => (hz i).2.2.2.2.1)

theorem totalReserve_le {a R : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) : totalReserve z ≤ (Fintype.card ι : ℝ) * (a * R) := by
  calc
    _ ≤ ∑ _i : ι, a * R := Finset.sum_le_sum (fun i _ => (hz i).2.2.2.2.2.1)
    _ = _ := by simp

theorem preparation_totalReserve (a : ℝ) (z : EpochState ι) (i : ι) (step : ℝ) :
    totalReserve (prepareOwner a z i step) = totalReserve z - step := by
  simp [totalReserve, prepareOwner, preparation, reserve, Finset.sum_sub_distrib]

theorem movement_totalReserve (a : ℝ) (z : EpochState ι) (g : ι → ℝ) (h : ℝ)
    (hunit : ∑ i, (g i) ^ 2 = 1) :
    totalReserve (movement a z g h) = totalReserve z - a * h ^ 2 := by
  simp only [totalReserve, movement, reserve, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hunit, mul_one]

theorem roundOwner_totalReserve_le {a R : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) (i : ι) : totalReserve (roundOwner z i) ≤ totalReserve z := by
  apply Finset.sum_le_sum
  intro j _
  by_cases hji : j = i
  · subst j
    simpa [roundOwner, reserve] using (hz i).2.2.2.2.1
  · simp [roundOwner, reserve, hji]

theorem exhaustOwner_totalReserve_le {a R : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) (i : ι) :
    totalReserve (exhaustOwner a z i) ≤ totalReserve z := by
  rw [exhaustOwner, preparation_totalReserve]
  have hc := (hz i).2.2.2.2.1
  linarith

/-- A trace records actual reserve and coordinate updates. It is not a
local-success primitive, and no complete controller theorem is asserted
merely from membership in this inductively defined relation. -/
inductive UpdateTrace (a R step h : ℝ) (start : EpochState ι) :
    EpochState ι → ℕ → ℕ → Prop
  | nil : UpdateTrace a R step h start start 0 0
  | prepare {z : EpochState ι} {walks preps : ℕ}
      (prior : UpdateTrace a R step h start z walks preps) (i : ι) :
      UpdateTrace a R step h start (prepareOwner a z i step) walks (preps + 1)
  | move {z : EpochState ι} {walks preps : ℕ}
      (prior : UpdateTrace a R step h start z walks preps) (g : ι → ℝ)
      (orthogonal : ∑ i, position z i * g i = 0)
      (unit : ∑ i, (g i) ^ 2 = 1) :
      UpdateTrace a R step h start (movement a z g h) (walks + 1) preps
  | round {z : EpochState ι} {walks preps : ℕ}
      (prior : UpdateTrace a R step h start z walks preps)
      (feasible : z ∈ epochDomain a R) (i : ι) :
      UpdateTrace a R step h start (roundOwner z i) walks preps
  | exhaust {z : EpochState ι} {walks preps : ℕ}
      (prior : UpdateTrace a R step h start z walks preps)
      (feasible : z ∈ epochDomain a R) (i : ι) :
      UpdateTrace a R step h start (exhaustOwner a z i) walks preps

theorem trace_energy {a R step h : ℝ} {start finish : EpochState ι} {walks preps : ℕ}
    (tr : UpdateTrace a R step h start finish walks preps) :
    energy (position start) + (walks : ℝ) * h ^ 2 ≤ energy (position finish) := by
  induction tr with
  | nil => simp
  | prepare prior i ih => simpa only [preparation_energy] using ih
  | move prior g horth hunit ih =>
    rw [movement_energy _ _ _ _ horth hunit]
    push_cast
    nlinarith
  | round prior hz i ih => exact ih.trans (roundOwner_energy_nondecreasing hz i)
  | exhaust prior hz i ih => simpa only [exhaustOwner, preparation_energy] using ih

theorem trace_reserve {a R step h : ℝ} (ha : 0 ≤ a)
    {start finish : EpochState ι} {walks preps : ℕ}
    (tr : UpdateTrace a R step h start finish walks preps) :
    (preps : ℝ) * step + totalReserve finish ≤ totalReserve start := by
  induction tr with
  | nil => simp
  | prepare prior i ih =>
    rw [preparation_totalReserve]
    push_cast
    nlinarith
  | move prior g horth hunit ih =>
    rw [movement_totalReserve _ _ _ _ hunit]
    nlinarith [mul_nonneg ha (sq_nonneg h)]
  | round prior hz i ih => linarith [roundOwner_totalReserve_le hz i]
  | exhaust prior hz i ih => linarith [exhaustOwner_totalReserve_le hz i]

theorem trace_walk_bound {a R step h : ℝ} {start finish : EpochState ι} {walks preps : ℕ}
    (tr : UpdateTrace a R step h start finish walks preps)
    (hf : finish ∈ epochDomain a R) :
    (walks : ℝ) * h ^ 2 ≤ (Fintype.card ι : ℝ) := by
  have he := trace_energy tr
  have he0 := energy_nonnegative (position start)
  have he1 := energy_le_card (position finish)
    (fun i => abs_le.mpr ⟨(hf i).1, (hf i).2.1⟩)
  linarith

theorem trace_preparation_bound {a R step h : ℝ} (ha : 0 ≤ a)
    {start finish : EpochState ι} {walks preps : ℕ}
    (tr : UpdateTrace a R step h start finish walks preps)
    (hs : start ∈ epochDomain a R) (hf : finish ∈ epochDomain a R) :
    (preps : ℝ) * step ≤ (Fintype.card ι : ℝ) * (a * R) := by
  have hc := trace_reserve ha tr
  have hc0 := totalReserve_nonneg hf
  have hc1 := totalReserve_le hs
  linarith

end HigherRankKSRuntime
