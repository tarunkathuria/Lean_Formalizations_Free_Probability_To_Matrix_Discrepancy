import MatrixSpencer.KSJacobiIteration
import Mathlib.Data.Finset.Max

/-!
# Explicit finite projection onto a simplex with a coordinate floor

For every input coordinate, the algorithm forms its upper level set and the
corresponding candidate threshold. A finite comparison scan takes the largest
candidate. The projected coordinates are scalar truncations at this threshold.
Only finite sums, arithmetic, and comparisons occur in the construction; the
proof does not select an unknown minimizer. No operation-cost model is asserted.
-/

open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSSimplexProjection

variable {d : ℕ}

def upperSet (z : Fin d → ℝ) (i : Fin d) : Finset (Fin d) :=
  Finset.univ.filter (fun j => z i ≤ z j)

@[simp] theorem mem_upperSet (z : Fin d → ℝ) (i j : Fin d) :
    j ∈ upperSet z i ↔ z i ≤ z j := by simp [upperSet]

theorem upperSet_card_pos (z : Fin d → ℝ) (i : Fin d) : 0 < (upperSet z i).card :=
  Finset.card_pos.mpr ⟨i, by simp⟩

def candidate (z : Fin d → ℝ) (t : ℝ) (i : Fin d) : ℝ :=
  ((∑ j ∈ upperSet z i, z j) - t) / (upperSet z i).card

def bestIndex (z : Fin d → ℝ) (t : ℝ) (hd : 0 < d) : Fin d :=
  (KSJacobiIteration.maxScan (candidate z t) (List.finRange d)).getD ⟨0, hd⟩

def threshold (z : Fin d → ℝ) (t : ℝ) (hd : 0 < d) : ℝ :=
  candidate z t (bestIndex z t hd)

theorem candidate_le_threshold (z : Fin d → ℝ) (t : ℝ) (hd : 0 < d) (j : Fin d) :
    candidate z t j ≤ threshold z t hd := by
  cases hs : KSJacobiIteration.maxScan (candidate z t) (List.finRange d) with
  | none =>
    have hnil := (KSJacobiIteration.maxScan_none_iff _ _).mp hs
    have hlen := congrArg List.length hnil
    simp only [List.length_finRange, List.length_nil] at hlen
    omega
  | some i =>
    have hm := KSJacobiIteration.maxScan_maximal (candidate z t)
      (List.finRange d) hs (List.mem_finRange j)
    simpa only [threshold, bestIndex, hs, Option.getD_some] using hm

def positiveProjection (z : Fin d → ℝ) (t : ℝ) (hd : 0 < d) (i : Fin d) : ℝ :=
  max 0 (z i - threshold z t hd)

theorem positiveProjection_nonneg (z : Fin d → ℝ) (t : ℝ) (hd : 0 < d) (i : Fin d) :
    0 ≤ positiveProjection z t hd i := le_max_left _ _

theorem candidate_balance (z : Fin d → ℝ) (t : ℝ) (i : Fin d) :
    (∑ j ∈ upperSet z i, (z j - candidate z t i)) = t := by
  have hc : (upperSet z i).card ≠ 0 := (upperSet_card_pos z i).ne'
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, candidate]
  field_simp
  ring

/-- The selected candidate gives a lower bound for the mass of all positive parts. -/
theorem mass_lower (z : Fin d → ℝ) (t : ℝ) (hd : 0 < d) :
    t ≤ ∑ j, positiveProjection z t hd j := by
  let i := bestIndex z t hd
  calc
    t = ∑ j ∈ upperSet z i, (z j - threshold z t hd) := (candidate_balance z t i).symm
    _ ≤ ∑ j ∈ upperSet z i, positiveProjection z t hd j :=
      Finset.sum_le_sum (fun j _ => le_max_right _ _)
    _ ≤ ∑ j, positiveProjection z t hd j :=
      Finset.sum_le_univ_sum_of_nonneg (fun j => positiveProjection_nonneg z t hd j)

/-- The positive truncations have exactly the requested positive total mass. -/
theorem positiveProjection_sum (z : Fin d → ℝ) {t : ℝ} (ht : 0 < t) (hd : 0 < d) :
    (∑ j, positiveProjection z t hd j) = t := by
  let S := Finset.univ.filter (fun j => threshold z t hd < z j)
  have hS : S.Nonempty := by
    by_contra he
    have hzero : ∀ j, positiveProjection z t hd j = 0 := by
      intro j
      have hj : ¬ threshold z t hd < z j := by
        intro hj
        exact he ⟨j, by simpa [S] using hj⟩
      exact max_eq_left (sub_nonpos.mpr (le_of_not_gt hj))
    have h := mass_lower z t hd
    simp only [hzero, Finset.sum_const_zero] at h
    linarith
  obtain ⟨i, hi, hmin⟩ := S.exists_min_image z hS
  have hi' : threshold z t hd < z i := (Finset.mem_filter.mp hi).2
  have hset : upperSet z i = S := by
    ext j
    constructor
    · intro hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'.trans_le ((mem_upperSet z i j).mp hj)⟩
    · intro hj
      exact (mem_upperSet z i j).mpr (hmin j hj)
  have hsum : (∑ j, positiveProjection z t hd j) =
      ∑ j ∈ upperSet z i, (z j - threshold z t hd) := by
    rw [hset]
    symm
    calc
      (∑ j ∈ S, (z j - threshold z t hd)) = ∑ j ∈ S, positiveProjection z t hd j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := (Finset.mem_filter.mp hj).2
        exact (max_eq_right (sub_nonneg.mpr hj'.le)).symm
      _ = ∑ j, positiveProjection z t hd j := by
        apply Finset.sum_subset (Finset.subset_univ S)
        intro j _ hj
        have hj' : z j ≤ threshold z t hd := by
          by_contra hh
          exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hh⟩)
        exact max_eq_left (sub_nonpos.mpr hj')
  apply le_antisymm _ (mass_lower z t hd)
  rw [hsum]
  calc
    (∑ j ∈ upperSet z i, (z j - threshold z t hd)) ≤
        ∑ j ∈ upperSet z i, (z j - candidate z t i) :=
      Finset.sum_le_sum (fun j _ => sub_le_sub_left (candidate_le_threshold z t hd i) _)
    _ = t := candidate_balance z t i

/-- The projection variational inequality on a positive-mass nonnegative simplex. -/
theorem positiveProjection_variational (z : Fin d → ℝ) {t : ℝ} (ht : 0 < t) (hd : 0 < d)
    (y : Fin d → ℝ) (hy : ∀ i, 0 ≤ y i) (hysum : ∑ i, y i = t) :
    (∑ i, (z i - positiveProjection z t hd i) *
      (y i - positiveProjection z t hd i)) ≤ 0 := by
  have hcoord (i : Fin d) :
      (z i - positiveProjection z t hd i) * (y i - positiveProjection z t hd i) ≤
        threshold z t hd * (y i - positiveProjection z t hd i) := by
    by_cases hi : 0 ≤ z i - threshold z t hd
    · rw [positiveProjection, max_eq_right hi]
      ring_nf
      exact le_rfl
    · have hp : positiveProjection z t hd i = 0 := max_eq_left (le_of_not_ge hi)
      rw [hp, sub_zero, sub_zero]
      exact mul_le_mul_of_nonneg_right (by linarith) (hy i)
  calc
    _ ≤ ∑ i, threshold z t hd * (y i - positiveProjection z t hd i) :=
      Finset.sum_le_sum (fun i _ => hcoord i)
    _ = 0 := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, hysum, positiveProjection_sum z ht hd]
      ring

/-- Positive mass remaining above the common coordinate floor. -/
def freeMass (a s : ℝ) : ℝ := s - (d : ℝ) * a

/-- The actual floor-simplex projection, including the floor-equality branch. -/
def project (z : Fin d → ℝ) (a s : ℝ) (hd : 0 < d) (i : Fin d) : ℝ :=
  if freeMass (d := d) a s ≤ 0 then a
  else a + positiveProjection (fun j => z j - a) (freeMass (d := d) a s) hd i

theorem project_floor (z : Fin d → ℝ) (a s : ℝ) (hd : 0 < d) (i : Fin d) :
    a ≤ project z a s hd i := by
  unfold project
  split_ifs
  · exact le_rfl
  · exact le_add_of_nonneg_right (positiveProjection_nonneg _ _ _ _)

theorem project_sum (z : Fin d → ℝ) (a s : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ s) :
    (∑ i, project z a s hd i) = s := by
  by_cases ht : freeMass (d := d) a s ≤ 0
  · have heq : s = (d : ℝ) * a := by dsimp [freeMass] at ht; linarith
    simp only [project, if_pos ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact heq.symm
  · have hpos : 0 < freeMass (d := d) a s := lt_of_not_ge ht
    simp only [project, if_neg ht, Finset.sum_add_distrib]
    rw [positiveProjection_sum _ hpos hd]
    simp [freeMass]

/-- With positive free mass, the report has the usual clipped-threshold form. -/
theorem project_eq_max (z : Fin d → ℝ) (a s : ℝ) (hd : 0 < d)
    (ht : 0 < freeMass (d := d) a s) (i : Fin d) :
    project z a s hd i =
      max a (z i - threshold (fun j => z j - a) (freeMass (d := d) a s) hd) := by
  rw [project, if_neg (not_le.mpr ht), positiveProjection]
  rw [add_max]
  congr 1 <;> ring

theorem floor_feasible_eq_constant (a s : ℝ) (heq : s = (d : ℝ) * a)
    (y : Fin d → ℝ) (hy : ∀ i, a ≤ y i) (hysum : ∑ i, y i = s) : ∀ i, y i = a := by
  have hsum : ∑ i, (y i - a) = 0 := by
    rw [Finset.sum_sub_distrib, hysum, heq]
    simp
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => sub_nonneg.mpr (hy i))).mp hsum
  intro i
  exact sub_eq_zero.mp (hall i (Finset.mem_univ _))

/-- Exact metric-projection variational inequality, with no unknown optimizer premise. -/
theorem project_variational (z : Fin d → ℝ) (a s : ℝ) (hd : 0 < d)
    (has : (d : ℝ) * a ≤ s) (y : Fin d → ℝ)
    (hy : ∀ i, a ≤ y i) (hysum : ∑ i, y i = s) :
    (∑ i, (z i - project z a s hd i) * (y i - project z a s hd i)) ≤ 0 := by
  by_cases ht : freeMass (d := d) a s ≤ 0
  · have heq : s = (d : ℝ) * a := by dsimp [freeMass] at ht; linarith
    have hy' := floor_feasible_eq_constant a s heq y hy hysum
    simp [project, ht, hy']
  · have hpos : 0 < freeMass (d := d) a s := lt_of_not_ge ht
    have hypos : ∀ i, 0 ≤ y i - a := fun i => sub_nonneg.mpr (hy i)
    have hys : (∑ i, (y i - a)) = freeMass (d := d) a s := by
      rw [Finset.sum_sub_distrib, hysum]
      simp [freeMass]
    have h := positiveProjection_variational (fun i => z i - a) hpos hd
      (fun i => y i - a) hypos hys
    convert h using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [project, if_neg ht]
    ring

/-- Feasibility of the explicitly computed report. -/
theorem project_feasible (z : Fin d → ℝ) (a s : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ s) :
    (∀ i, a ≤ project z a s hd i) ∧ (∑ i, project z a s hd i) = s :=
  ⟨project_floor z a s hd, project_sum z a s hd has⟩

/-- Euclidean squared-distance minimality follows from the certified variational inequality. -/
theorem project_distance_le (z : Fin d → ℝ) (a s : ℝ) (hd : 0 < d)
    (has : (d : ℝ) * a ≤ s) (y : Fin d → ℝ)
    (hy : ∀ i, a ≤ y i) (hysum : ∑ i, y i = s) :
    (∑ i, (z i - project z a s hd i) ^ 2) ≤ ∑ i, (z i - y i) ^ 2 := by
  have hv := project_variational z a s hd has y hy hysum
  have hp : (∑ i, (z i - project z a s hd i) ^ 2) ≤
      ∑ i, ((z i - y i) ^ 2 +
        2 * ((z i - project z a s hd i) * (y i - project z a s hd i))) := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (y i - project z a s hd i)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hp
  linarith

/-- A feasible input is unchanged by the actual finite projection. -/
theorem project_of_feasible (z : Fin d → ℝ) (a s : ℝ) (hd : 0 < d)
    (has : (d : ℝ) * a ≤ s) (hz : ∀ i, a ≤ z i) (hzsum : ∑ i, z i = s) :
    project z a s hd = z := by
  have hv := project_variational z a s hd has z hz hzsum
  have hnonneg (i : Fin d) : 0 ≤ (z i - project z a s hd i) * (z i - project z a s hd i) :=
    mul_self_nonneg _
  have heq := le_antisymm hv (Finset.sum_nonneg (fun i _ => hnonneg i))
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hnonneg i)).mp heq
  funext i
  have hi := hall i (Finset.mem_univ _)
  nlinarith

end MatrixSpencer.KSSimplexProjection
