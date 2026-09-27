import HigherRankKS.Statement
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Compact

/-! Exact original-owner state and augmented-reserve identities. -/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace AugmentedHigherRankKS

abbrev EpochState (ι : Type*) := (ι → ℝ) × (ι → ℝ) × (ι → ℝ)

def position {ι : Type*} (z : EpochState ι) : ι → ℝ := z.1
def spent {ι : Type*} (z : EpochState ι) : ι → ℝ := z.2.1
def reserve {ι : Type*} (z : EpochState ι) : ι → ℝ := z.2.2

def initialState {ι : Type*} (a R : ℝ) (x₀ : ι → ℝ) : EpochState ι :=
  (x₀, fun _ => 0, fun _ => a * R)

def epochDomain {ι : Type*} (a R : ℝ) : Set (EpochState ι) :=
  {z | ∀ i, -1 ≤ position z i ∧ position z i ≤ 1 ∧
    0 ≤ spent z i ∧ spent z i ≤ R ∧
    0 ≤ reserve z i ∧ reserve z i ≤ a * R ∧
    reserve z i + a * spent z i ≤ a * R ∧
    (1 - (position z i)^2) * (reserve z i + a * spent z i - a * R) = 0}

def movement {ι : Type*} (a : ℝ) (z : EpochState ι)
    (h : ι → ℝ) (t : ℝ) : EpochState ι :=
  (fun i => position z i + t * h i,
   fun i => spent z i + t^2 * (h i)^2,
   fun i => reserve z i - a * t^2 * (h i)^2)

def preparation {ι : Type*} (a : ℝ) (z : EpochState ι)
    (u : ι → ℝ) : EpochState ι :=
  (position z, fun i => spent z i + u i / a,
    fun i => reserve z i - u i)

def dropReserve {ι : Type*} [DecidableEq ι] (z : EpochState ι) (i : ι) :
    EpochState ι :=
  (position z, spent z, Function.update (reserve z) i 0)

def discrepancy {ι n : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ) (z : EpochState ι) : Matrix n n ℂ :=
  ∑ i, (position z i - x₀ i) • A i

def budgetCenter {ι n : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ) (z : EpochState ι) : Matrix n n ℂ :=
  ∑ i, ((x₀ i)^2 - (position z i)^2 + spent z i) • A i

def budgetMatrix {ι n : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ) (z : EpochState ι) : Matrix n n ℂ :=
  ∑ i, (1 - (position z i)^2 + spent z i) • A i

def initialRemaining {ι n : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ) : Matrix n n ℂ :=
  ∑ i, (1 - (x₀ i)^2) • A i

@[simp] theorem position_initialState {ι : Type*} (a R : ℝ) (x₀ : ι → ℝ) :
    position (initialState a R x₀) = x₀ := rfl

@[simp] theorem movement_zero {ι : Type*} (a : ℝ) (z : EpochState ι) (h : ι → ℝ) :
    movement a z h 0 = z := by
  rcases z with ⟨x, s, c⟩
  simp [movement, position, spent, reserve]

theorem movement_reserve_identity {ι : Type*} (a : ℝ) (z : EpochState ι)
    (h : ι → ℝ) (t : ℝ) (i : ι) :
    reserve (movement a z h t) i + a * spent (movement a z h t) i =
      reserve z i + a * spent z i := by
  simp only [movement, reserve, spent]
  ring

theorem preparation_reserve_identity {ι : Type*} {a : ℝ} (ha : a ≠ 0)
    (z : EpochState ι) (u : ι → ℝ) (i : ι) :
    reserve (preparation a z u) i + a * spent (preparation a z u) i =
      reserve z i + a * spent z i := by
  simp only [preparation, reserve, spent]
  field_simp
  ring

theorem initialState_mem {ι : Type*} {a R : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R)
    (x₀ : ι → ℝ) (hx : ∀ i, -1 ≤ x₀ i ∧ x₀ i ≤ 1) :
    initialState a R x₀ ∈ epochDomain a R := by
  intro i
  simp only [initialState, position, spent, reserve]
  exact ⟨(hx i).1, (hx i).2, le_rfl, hR, mul_nonneg ha hR,
    le_rfl, by simp, by simp⟩

theorem interior_reserve_eq {ι : Type*} {a R : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) {i : ι} (hi : |position z i| < 1) :
    reserve z i + a * spent z i = a * R := by
  have hx : (position z i)^2 < 1 := by nlinarith [sq_nonneg (position z i),
    (abs_lt.mp hi).1, (abs_lt.mp hi).2]
  have hm := (hz i).2.2.2.2.2.2.2
  have := (mul_eq_zero.mp hm).resolve_left (by linarith)
  linarith

theorem exhausted_spent_eq {ι : Type*} {a R : ℝ} (ha : a ≠ 0)
    {z : EpochState ι} (hz : z ∈ epochDomain a R) {i : ι}
    (hi : |position z i| < 1) (hc : reserve z i = 0) : spent z i = R := by
  have hh := interior_reserve_eq hz hi
  rw [hc, zero_add] at hh
  exact mul_left_cancel₀ ha hh

@[simp] theorem discrepancy_initial {ι n : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ) (a R : ℝ) (x₀ : ι → ℝ) :
    discrepancy A x₀ (initialState a R x₀) = 0 := by
  simp [discrepancy, initialState, position]

@[simp] theorem budgetCenter_initial {ι n : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ) (a R : ℝ) (x₀ : ι → ℝ) :
    budgetCenter A x₀ (initialState a R x₀) = 0 := by
  simp [budgetCenter, initialState, position, spent]

theorem budget_decomposition {ι n : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ) (z : EpochState ι) :
    budgetMatrix A z = initialRemaining A x₀ + budgetCenter A x₀ z := by
  rw [budgetMatrix, initialRemaining, budgetCenter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← add_smul]
  congr 1
  ring

theorem discrepancy_movement {ι n : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ) (a : ℝ)
    (z : EpochState ι) (h : ι → ℝ) (t : ℝ) :
    discrepancy A x₀ (movement a z h t) =
      discrepancy A x₀ z + t • ∑ i, h i • A i := by
  simp only [discrepancy, movement, position]
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, ← add_smul]
  congr 1
  ring

theorem budgetCenter_movement {ι n : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ) (a : ℝ)
    (z : EpochState ι) (h : ι → ℝ) (t : ℝ) :
    budgetCenter A x₀ (movement a z h t) =
      budgetCenter A x₀ z - (2 * t) • ∑ i, (position z i * h i) • A i := by
  simp only [budgetCenter, movement, position, spent]
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, ← sub_smul]
  congr 1
  ring

end AugmentedHigherRankKS
