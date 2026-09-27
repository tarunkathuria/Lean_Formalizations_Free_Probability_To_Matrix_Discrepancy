import HigherRankKSRuntime.PotentialPerturbation

/-! Quantitative cleanup costs for the actual optimized potential. -/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKSRuntime
open AugmentedHigherRankKS

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

theorem roundOwner_discrepancy_diff (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ)
    (z : EpochState ι) (i : ι) :
    discrepancy A x₀ (roundOwner z i) - discrepancy A x₀ z =
      (faceSign (position z i) - position z i) • A i := by
  unfold discrepancy
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · rw [roundOwner_position, ← sub_smul]
    congr 1
    ring
  · intro j _ hj
    simp [roundOwner, position, hj]
  · simp

theorem roundOwner_budget_diff (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ)
    (z : EpochState ι) (i : ι) :
    budgetCenter A x₀ (roundOwner z i) - budgetCenter A x₀ z =
      ((position z i) ^ 2 - 1) • A i := by
  unfold budgetCenter
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · rw [roundOwner_position, faceSign_sq, ← sub_smul]
    change ((x₀ i) ^ 2 - 1 + spent z i - ((x₀ i) ^ 2 - (position z i) ^ 2 + spent z i)) • A i = _
    congr 1
    ring
  · intro j _ hj
    simp [roundOwner, position, spent, hj]
  · simp

theorem prepareOwner_budget_diff (A : ι → Matrix n n ℂ) (x₀ : ι → ℝ)
    (a : ℝ) (z : EpochState ι) (i : ι) (step : ℝ) :
    budgetCenter A x₀ (prepareOwner a z i step) - budgetCenter A x₀ z =
      (step / a) • A i := by
  unfold budgetCenter
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp only [prepareOwner, preparation, position, spent, Pi.single_eq_same]
    rw [← sub_smul]
    congr 1
    ring
  · intro j _ hj
    simp [prepareOwner, preparation, position, spent, hj]
  · simp

theorem near_face_square_bound {x ρ : ℝ} (hx : |x| ≤ 1) (hρ : 1 - |x| ≤ ρ) :
    |x ^ 2 - 1| ≤ 2 * ρ := by
  have hsq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).mpr hx
  rw [abs_of_nonpos (sub_nonpos.mpr hsq)]
  nlinarith [sq_abs x, abs_nonneg x, mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hx)]

theorem roundOwner_potential_cost [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (θ : ℝ) (x₀ : ι → ℝ)
    {a R ρ ε : ℝ} {z : EpochState ι} (hz : z ∈ epochDomain a R)
    (i : ι) (hε : ‖A i‖ ≤ ε) (hnear : 1 - |position z i| ≤ ρ) :
    epochPotential A β θ x₀ (roundOwner z i) ≤
      epochPotential A β θ x₀ z + 2 * ρ * ε := by
  have hxi : |position z i| ≤ 1 := abs_le.mpr ⟨(hz i).1, (hz i).2.1⟩
  have hρ : 0 ≤ ρ := (sub_nonneg.mpr hxi).trans hnear
  have he0 : 0 ≤ ε := (norm_nonneg _).trans hε
  apply epochPotential_perturb_le A hA hβ hβ1 θ x₀
  · intro j; exact (hz j).2.2.2.2.1
  · intro j; exact (roundOwner_feasible hz i j).2.2.2.2.1
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [roundOwner, reserve] using (hz i).2.2.2.2.1
    · simp [roundOwner, reserve, hj]
  · rw [roundOwner_discrepancy_diff, norm_smul, Real.norm_eq_abs, faceSign_distance hxi]
    calc
      _ ≤ ρ * ε := mul_le_mul hnear hε (norm_nonneg _) hρ
      _ ≤ 2 * ρ * ε := by nlinarith
  · rw [roundOwner_budget_diff, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (near_face_square_bound hxi hnear) hε (norm_nonneg _)
      (mul_nonneg (by norm_num) hρ)

theorem exhaustOwner_potential_cost [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (θ : ℝ) (x₀ : ι → ℝ)
    {a R ζ ε : ℝ} {z : EpochState ι} (hz : z ∈ epochDomain a R)
    (ha : 0 < a) (i : ι) (hε : ‖A i‖ ≤ ε) (hsmall : reserve z i ≤ 2 * ζ) :
    epochPotential A β θ x₀ (exhaustOwner a z i) ≤
      epochPotential A β θ x₀ z + 2 * ζ * ε / a := by
  have hc : 0 ≤ reserve z i := (hz i).2.2.2.2.1
  have hζ : 0 ≤ ζ := by linarith
  have he0 : 0 ≤ ε := (norm_nonneg _).trans hε
  apply epochPotential_perturb_le A hA hβ hβ1 θ x₀
  · intro j; exact (hz j).2.2.2.2.1
  · intro j; exact (exhaustOwner_feasible hz ha i j).2.2.2.2.1
  · intro j
    by_cases hj : j = i
    · subst j; simpa using hc
    · simp [exhaustOwner, prepareOwner, preparation, reserve, hj]
  · have he : discrepancy A x₀ (exhaustOwner a z i) = discrepancy A x₀ z := rfl
    rw [he, sub_self, norm_zero]
    positivity
  · rw [exhaustOwner, prepareOwner_budget_diff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hc ha.le)]
    calc
      _ ≤ (2 * ζ / a) * ε := mul_le_mul (div_le_div_of_nonneg_right hsmall ha.le)
        hε (norm_nonneg _) (by positivity)
      _ = _ := by ring

end HigherRankKSRuntime
