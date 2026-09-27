import AugmentedHigherRankKS.State
import HigherRankKSRuntime.Ledger

/-! Concrete controller updates on the shared original-owner epoch state. -/

open scoped BigOperators
noncomputable section
namespace HigherRankKSRuntime
open AugmentedHigherRankKS
open AugmentedHigherRankKS.ScalarLedger

variable {ι : Type*} [DecidableEq ι]

def faceSign (x : ℝ) : ℝ := if x ≤ 0 then -1 else 1

theorem faceSign_sign (x : ℝ) : faceSign x = -1 ∨ faceSign x = 1 := by
  unfold faceSign
  split_ifs <;> simp

theorem faceSign_sq (x : ℝ) : (faceSign x) ^ 2 = 1 := by
  rcases faceSign_sign x with h | h <;> rw [h] <;> norm_num

theorem faceSign_distance {x : ℝ} (hx : |x| ≤ 1) :
    |faceSign x - x| = 1 - |x| := by
  obtain ⟨hxl, hxu⟩ := abs_le.mp hx
  unfold faceSign
  split_ifs with h
  · rw [abs_of_nonpos h, abs_of_nonpos (by linarith : -1 - x ≤ 0)]
    ring
  · have hpos : 0 < x := lt_of_not_ge h
    rw [abs_of_pos hpos, abs_of_nonneg (by linarith : 0 ≤ 1 - x)]

def roundOwner (z : EpochState ι) (i : ι) : EpochState ι :=
  (Function.update (position z) i (faceSign (position z i)),
    spent z, Function.update (reserve z) i 0)

def prepareOwner (a : ℝ) (z : EpochState ι) (i : ι) (step : ℝ) : EpochState ι :=
  preparation a z (Pi.single i step)

def exhaustOwner (a : ℝ) (z : EpochState ι) (i : ι) : EpochState ι :=
  prepareOwner a z i (reserve z i)

theorem epochDomain_iff_coordinates (a R : ℝ) (z : EpochState ι) :
    z ∈ epochDomain a R ↔
      ∀ i, FeasibleCoordinate a R (position z i) (spent z i) (reserve z i) := Iff.rfl

theorem roundOwner_feasible {a R : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) (i : ι) : roundOwner z i ∈ epochDomain a R := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [roundOwner, position, spent, reserve, FeasibleCoordinate] using
      face_cleanup_feasible (hz i) (faceSign_sign (position z i))
  · simpa [roundOwner, position, spent, reserve, hji] using hz j

theorem prepareOwner_feasible {a R step : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) (ha : 0 < a) (i : ι)
    (hstep : 0 ≤ step) (hc : step ≤ reserve z i) :
    prepareOwner a z i step ∈ epochDomain a R := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [prepareOwner, preparation, position, spent, reserve, FeasibleCoordinate] using
      preparation_feasible (hz i) ha hstep hc
  · simpa [prepareOwner, preparation, position, spent, reserve, hji] using hz j

theorem exhaustOwner_feasible {a R : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) (ha : 0 < a) (i : ι) :
    exhaustOwner a z i ∈ epochDomain a R := by
  exact prepareOwner_feasible hz ha i (hz i).2.2.2.2.1 le_rfl

theorem exhaustOwner_spent {a R : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) (ha : 0 < a) (i : ι)
    (hi : |position z i| < 1) : spent (exhaustOwner a z i) i = R := by
  simpa [exhaustOwner, prepareOwner, preparation, spent, reserve] using
    floor_cleanup_spent (hz i) ha hi

@[simp] theorem prepareOwner_position (a : ℝ) (z : EpochState ι) (i : ι) (step : ℝ) :
    position (prepareOwner a z i step) = position z := rfl

@[simp] theorem exhaustOwner_reserve (a : ℝ) (z : EpochState ι) (i : ι) :
    reserve (exhaustOwner a z i) i = 0 := by
  simp [exhaustOwner, prepareOwner, preparation, reserve]

@[simp] theorem roundOwner_position (z : EpochState ι) (i : ι) :
    position (roundOwner z i) i = faceSign (position z i) := by
  simp [roundOwner, position]

theorem movement_feasible {a R : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) (ha : 0 < a) (g : ι → ℝ) (t : ℝ)
    (hinterior : ∀ i, g i ≠ 0 → |position z i| < 1)
    (hcube : ∀ i, -1 ≤ position z i + t * g i ∧ position z i + t * g i ≤ 1)
    (hreserve : ∀ i, a * (t * g i) ^ 2 ≤ reserve z i) :
    movement a z g t ∈ epochDomain a R := by
  intro i
  by_cases hg : g i = 0
  · simpa [movement, position, spent, reserve, hg] using hz i
  · have hb := interior_reserve_eq hz (hinterior i hg)
    have hf := centered_feasible (hz i) ha hb (hcube i).1 (hcube i).2 (hreserve i)
    simpa only [movement, position, spent, reserve, mul_pow, mul_assoc] using hf

section Finite
variable [Fintype ι]

theorem movement_energy (a : ℝ) (z : EpochState ι) (g : ι → ℝ) (t : ℝ)
    (horth : ∑ i, position z i * g i = 0) (hunit : ∑ i, (g i) ^ 2 = 1) :
    energy (position (movement a z g t)) = energy (position z) + t ^ 2 := by
  exact centered_energy (position z) g t horth hunit

theorem roundOwner_energy_nondecreasing {a R : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) (i : ι) :
    energy (position z) ≤ energy (position (roundOwner z i)) := by
  apply Finset.sum_le_sum
  intro j _
  by_cases hji : j = i
  · subst j
    rw [roundOwner_position, faceSign_sq]
    have hl := (hz i).1
    have hu := (hz i).2.1
    nlinarith [sq_nonneg (position z i)]
  · simp [roundOwner, position, hji]

theorem preparation_energy (a : ℝ) (z : EpochState ι) (i : ι) (step : ℝ) :
    energy (position (prepareOwner a z i step)) = energy (position z) := rfl

end Finite
end HigherRankKSRuntime
