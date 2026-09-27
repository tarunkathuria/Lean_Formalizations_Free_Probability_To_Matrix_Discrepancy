import AugmentedHigherRankKS.CompactState
import AugmentedHigherRankKS.ScalarLedger

open Set Filter
open scoped Topology BigOperators

noncomputable section
namespace AugmentedHigherRankKS

variable {ι : Type*}

theorem preparation_mem {a R : ℝ} (ha : 0 < a) {z : EpochState ι}
    (hz : z ∈ epochDomain a R) (u : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ reserve z i) :
    preparation a z u ∈ epochDomain a R := by
  intro i
  exact ScalarLedger.preparation_feasible (hz i) ha (hu i).1 (hu i).2

theorem totalReserve_preparation [Fintype ι] (a : ℝ) (z : EpochState ι) (u : ι → ℝ) :
    totalReserve (preparation a z u) = totalReserve z - ∑ i, u i := by
  simp only [totalReserve, preparation, reserve, Finset.sum_sub_distrib]

theorem dropReserve_mem [DecidableEq ι] {a R : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) (i : ι) (hi : |position z i| = 1) :
    dropReserve z i ∈ epochDomain a R := by
  intro j
  by_cases hji : j = i
  · subst j
    have hs : position z i = -1 ∨ position z i = 1 := by
      exact ((abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hi).symm
    simpa [dropReserve, position, spent, reserve, ScalarLedger.FeasibleCoordinate] using
      ScalarLedger.face_cleanup_feasible (hz i) hs
  · simpa [dropReserve, position, spent, reserve, hji] using hz j

theorem totalReserve_dropReserve [Fintype ι] [DecidableEq ι]
    (z : EpochState ι) (i : ι) :
    totalReserve (dropReserve z i) = totalReserve z - reserve z i := by
  unfold totalReserve dropReserve reserve
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  simp

theorem positive_reserve_interior {a R : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R)
    (hfaces : ∀ i, |position z i| = 1 → reserve z i = 0)
    {i : ι} (hc : 0 < reserve z i) : |position z i| < 1 := by
  have hle : |position z i| ≤ 1 := abs_le.mpr ⟨(hz i).1, (hz i).2.1⟩
  apply lt_of_le_of_ne hle
  intro heq
  exact (ne_of_gt hc) (hfaces i heq)

/-- Both signs of the exact quadratic reserve curve are feasible near zero. -/
theorem eventually_movement_mem [Finite ι] {a R : ℝ} (ha : 0 < a)
    {z : EpochState ι} (hz : z ∈ epochDomain a R)
    (hfaces : ∀ i, |position z i| = 1 → reserve z i = 0)
    (h : ι → ℝ) (hsupport : ∀ i, reserve z i = 0 → h i = 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), movement a z h t ∈ epochDomain a R := by
  have hcoord : ∀ i, ∀ᶠ t in 𝓝 (0 : ℝ),
      ScalarLedger.FeasibleCoordinate a R
        (position z i + t * h i)
        (spent z i + t^2 * (h i)^2)
        (reserve z i - a * t^2 * (h i)^2) := by
    intro i
    by_cases hh : h i = 0
    · filter_upwards [] with t
      simpa [hh, ScalarLedger.FeasibleCoordinate] using hz i
    · have hc : 0 < reserve z i := lt_of_le_of_ne (hz i).2.2.2.2.1
        (fun heq => hh (hsupport i heq.symm))
      have hx := positive_reserve_interior hz hfaces hc
      have hcont : Continuous (fun t : ℝ => |position z i + t * h i|) := by fun_prop
      have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), |position z i + t * h i| < 1 :=
        hcont.continuousAt.eventually (isOpen_Iio.mem_nhds (by simpa using hx))
      have hccont : Continuous (fun t : ℝ => a * (t * h i)^2) := by fun_prop
      have hcnear : ∀ᶠ t in 𝓝 (0 : ℝ), a * (t * h i)^2 < reserve z i :=
        hccont.continuousAt.eventually (isOpen_Iio.mem_nhds (by simpa using hc))
      filter_upwards [hnear, hcnear] with t ht hct
      have ht' := abs_lt.mp ht
      simpa only [mul_pow, mul_assoc] using ScalarLedger.centered_feasible
        (hz i) ha (interior_reserve_eq hz hx) ht'.1.le ht'.2.le hct.le
  have hall := Filter.eventually_all.mpr hcoord
  filter_upwards [hall] with t ht
  exact ht

end AugmentedHigherRankKS
