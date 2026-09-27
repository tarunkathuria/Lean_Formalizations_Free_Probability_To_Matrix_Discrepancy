import AugmentedHigherRankKS.PreparationCondition
import AugmentedHigherRankKS.FourBlockCompression

/-! Exact restriction to positive reserves, and affine preparation identities. -/
open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

def positiveReserves (z : EpochState ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => 0 < reserve z i
abbrev ActiveOwners (z : EpochState ι) := {i // i ∈ positiveReserves z}

@[simp] theorem mem_positiveReserves (z : EpochState ι) (i : ι) :
    i ∈ positiveReserves z ↔ 0 < reserve z i := by simp [positiveReserves]

theorem reserve_zero_of_not_positive {a R : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) (i : ι) (hi : i ∉ positiveReserves z) :
    reserve z i = 0 := by
  have hn : ¬ 0 < reserve z i := by simpa only [mem_positiveReserves] using hi
  exact le_antisymm (le_of_not_gt hn) (hz i).2.2.2.2.1

theorem potential_eq_restrict (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : ι → Matrix n n ℂ) (β θ : ℝ) (L : Finset ι)
    (c : ι → ℝ) (hc : ∀ i, i ∉ L → c i = 0) :
    potential H A β c θ =
      potential H (fun i : {i // i ∈ L} => A i) β (fun i => c i) θ := by
  have ho : objective H A β c θ =
      objective H (fun i : {i // i ∈ L} => A i) β (fun i => c i) θ := by
    funext S
    unfold objective
    rw [source_eq_live A β L c hc S]
  simp only [potential, ho]

theorem epochPotential_eq_active (A : ι → Matrix n n ℂ) (β θ : ℝ)
    (x₀ : ι → ℝ) {a R : ℝ} {z : EpochState ι} (hz : z ∈ epochDomain a R) :
    epochPotential A β θ x₀ z =
      potential (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z))
        (fun i : ActiveOwners z => A i) β (fun i => reserve z i) θ :=
  potential_eq_restrict _ A β θ (positiveReserves z) _ (reserve_zero_of_not_positive hz)

theorem discrepancy_preparation (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ)
    (a : ℝ) (z : EpochState ι) (u : ι → ℝ) :
    discrepancy A x₀ (preparation a z u) = discrepancy A x₀ z := rfl

theorem budgetCenter_preparation (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ)
    (a : ℝ) (z : EpochState ι) (u : ι → ℝ) :
    budgetCenter A x₀ (preparation a z u) = budgetCenter A x₀ z + ∑ i, (u i / a) • A i := by
  unfold budgetCenter preparation position spent
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← add_smul]
  congr 1
  ring

theorem budgetCenter_prepareOne (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ)
    (a : ℝ) (z : EpochState ι) (i : ι) (t : ℝ) :
    budgetCenter A x₀ (prepareOne a z i t) = budgetCenter A x₀ z + (t / a) • A i := by
  unfold prepareOne
  rw [budgetCenter_preparation]
  congr 1
  simp only [ite_div, zero_div, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem augmentedCenter_add (H K H' K' : Matrix n n ℂ) :
    augmentedCenter (H + H') (K + K') = augmentedCenter H K + augmentedCenter H' K' := by
  ext (i | i) (j | j) <;> cases i <;> cases j <;>
    simp [augmentedCenter, signedLift, Matrix.fromBlocks, add_comm]

theorem augmentedCenter_smul (t : ℝ) (H K : Matrix n n ℂ) :
    augmentedCenter (t • H) (t • K) = t • augmentedCenter H K := by
  ext (i | i) (j | j) <;> cases i <;> cases j <;>
    simp [augmentedCenter, signedLift, Matrix.fromBlocks]

theorem augmentedCenter_prepareOne (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ)
    (a : ℝ) (z : EpochState ι) (i : ι) (t : ℝ) :
    augmentedCenter (discrepancy A x₀ (prepareOne a z i t))
      (budgetCenter A x₀ (prepareOne a z i t)) =
      augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z) +
        t • ((1 / a) • augmentedCenter 0 (A i)) := by
  rw [budgetCenter_prepareOne]
  change augmentedCenter (discrepancy A x₀ z) _ = _
  have he := augmentedCenter_add (discrepancy A x₀ z) (budgetCenter A x₀ z)
    ((t / a) • (0 : Matrix n n ℂ)) ((t / a) • A i)
  rw [augmentedCenter_smul] at he
  simpa only [smul_zero, add_zero, smul_smul, mul_one_div] using he

/-- During a preparation probe the positive-reserve index set is fixed in the
formula; all omitted coefficients remain exactly zero, even for negative time. -/
theorem epochPotential_prepareOne_eq [Nonempty n]
    (A : ι → Matrix n n ℂ) (β θ : ℝ) (x₀ : ι → ℝ)
    {a R : ℝ} {z : EpochState ι} (hz : z ∈ epochDomain a R)
    (i : ActiveOwners z) (t : ℝ) :
    epochPotential A β θ x₀ (prepareOne a z i t) =
      potential (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z) +
          t • ((1 / a) • augmentedCenter 0 (A i)))
        (fun j : ActiveOwners z => A j) β
        (fun j => reserve z j - if j = i then t else 0) θ := by
  classical
  unfold epochPotential
  rw [augmentedCenter_prepareOne]
  rw [potential_eq_restrict _ A β θ (positiveReserves z) _ (by
    intro j hj
    have hji : j ≠ i.val := by rintro rfl; exact hj i.property
    change reserve z j - (if j = i.val then t else 0) = 0
    rw [if_neg hji, sub_zero, reserve_zero_of_not_positive hz j hj])]
  congr 1
  funext j
  simp [prepareOne, preparation, reserve, Subtype.ext_iff]

end AugmentedHigherRankKS
