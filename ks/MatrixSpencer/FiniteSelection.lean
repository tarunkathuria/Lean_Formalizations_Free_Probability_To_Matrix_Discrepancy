import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Weighted finite endpoint selection

These lemmas use finite sums of nonnegative real weights. They do not use
probability measures or assume the endpoint-selection conclusion. They
provide weighted Markov and second-moment bounds, a finite union bound,
and a positive-weight outcome outside all bad events.
-/

open scoped BigOperators

namespace MatrixSpencer
namespace FiniteSelection

variable {ι κ : Type*}

/-- The finite weighted Markov inequality before dividing by the threshold. -/
theorem weighted_markov_mul (sample bad : Finset ι) (hsub : bad ⊆ sample)
    (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hx : ∀ i ∈ sample, 0 ≤ x i) (a : ℝ)
    (hlarge : ∀ i ∈ bad, a ≤ x i) :
    a * (∑ i ∈ bad, w i) ≤ ∑ i ∈ sample, w i * x i := by
  calc
    a * (∑ i ∈ bad, w i) = ∑ i ∈ bad, w i * a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ ≤ ∑ i ∈ bad, w i * x i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hlarge i hi) (hw i)
    _ ≤ ∑ i ∈ sample, w i * x i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun i hi _ => mul_nonneg (hw i) (hx i hi))

/-- Weighted Markov for an explicitly specified finite bad event. -/
theorem weighted_markov (sample bad : Finset ι) (hsub : bad ⊆ sample)
    (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hx : ∀ i ∈ sample, 0 ≤ x i) {a : ℝ} (ha : 0 < a)
    (hlarge : ∀ i ∈ bad, a ≤ x i) :
    (∑ i ∈ bad, w i) ≤ (∑ i ∈ sample, w i * x i) / a := by
  apply (le_div_iff₀ ha).mpr
  simpa only [mul_comm] using weighted_markov_mul sample bad hsub w x hw hx a hlarge

/-- Markov with an upper bound on the weighted first moment. -/
theorem weighted_markov_of_moment_le (sample bad : Finset ι) (hsub : bad ⊆ sample)
    (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hx : ∀ i ∈ sample, 0 ≤ x i) {a b : ℝ} (ha : 0 < a)
    (hlarge : ∀ i ∈ bad, a ≤ x i)
    (hmoment : (∑ i ∈ sample, w i * x i) ≤ b) :
    (∑ i ∈ bad, w i) ≤ b / a := by
  exact (weighted_markov sample bad hsub w x hw hx ha hlarge).trans
    (div_le_div_of_nonneg_right hmoment ha.le)

/-- A weighted second-moment bound for deviations from zero. -/
theorem weighted_chebyshev (sample bad : Finset ι) (hsub : bad ⊆ sample)
    (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {a : ℝ} (ha : 0 < a)
    (hlarge : ∀ i ∈ bad, a ≤ |x i|) :
    (∑ i ∈ bad, w i) ≤ (∑ i ∈ sample, w i * (x i) ^ 2) / a ^ 2 := by
  apply weighted_markov sample bad hsub w (fun i => (x i) ^ 2) hw
    (fun i _ => sq_nonneg (x i)) (sq_pos_of_pos ha)
  intro i hi
  simpa only [sq_abs] using
    (sq_le_sq₀ ha.le (abs_nonneg (x i))).mpr (hlarge i hi)

/-- Chebyshev with an explicit weighted second-moment budget. -/
theorem weighted_chebyshev_of_moment_le (sample bad : Finset ι)
    (hsub : bad ⊆ sample) (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {a b : ℝ} (ha : 0 < a) (hlarge : ∀ i ∈ bad, a ≤ |x i|)
    (hmoment : (∑ i ∈ sample, w i * (x i) ^ 2) ≤ b) :
    (∑ i ∈ bad, w i) ≤ b / a ^ 2 := by
  exact (weighted_chebyshev sample bad hsub w x hw ha hlarge).trans
    (div_le_div_of_nonneg_right hmoment (sq_nonneg a))

variable [DecidableEq ι] [DecidableEq κ]

/-- The weighted union bound for two finite events. -/
theorem union_mass_le (s t : Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i ∈ s ∪ t, w i) ≤ (∑ i ∈ s, w i) + ∑ i ∈ t, w i := by
  calc
    (∑ i ∈ s ∪ t, w i) ≤
        (∑ i ∈ s ∪ t, w i) + ∑ i ∈ s ∩ t, w i :=
      le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hw i))
    _ = (∑ i ∈ s, w i) + ∑ i ∈ t, w i := Finset.sum_union_inter

/-- The weighted union bound for any finite family of bad events. -/
theorem biUnion_mass_le (events : Finset κ) (bad : κ → Finset ι)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i ∈ events.biUnion bad, w i) ≤
      ∑ j ∈ events, ∑ i ∈ bad j, w i := by
  induction events using Finset.induction_on with
  | empty => simp
  | @insert j events hj ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hj]
      exact (union_mass_le (bad j) (events.biUnion bad) w hw).trans
        (add_le_add_left ih _)

/-- A strict mass gap produces an outcome of positive weight outside the bad event. -/
theorem exists_positive_outside (sample bad : Finset ι) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hgap : (∑ i ∈ bad, w i) < ∑ i ∈ sample, w i) :
    ∃ i ∈ sample, 0 < w i ∧ i ∉ bad := by
  have hinter : (∑ i ∈ sample ∩ bad, w i) ≤ ∑ i ∈ bad, w i :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun i _ _ => hw i)
  have hsplit := Finset.sum_sdiff (f := w)
    (Finset.inter_subset_left : sample ∩ bad ⊆ sample)
  rw [Finset.sdiff_inter_self_left] at hsplit
  have hpositive : 0 < ∑ i ∈ sample \ bad, w i := by linarith
  obtain ⟨i, hi, hwi⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun i _ => hw i)).mp hpositive
  exact ⟨i, (Finset.mem_sdiff.mp hi).1, hwi, (Finset.mem_sdiff.mp hi).2⟩

/-- Simultaneous avoidance of finitely many bad events with insufficient total mass. -/
theorem exists_positive_avoiding_all (sample : Finset ι) (events : Finset κ)
    (bad : κ → Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hgap : (∑ j ∈ events, ∑ i ∈ bad j, w i) < ∑ i ∈ sample, w i) :
    ∃ i ∈ sample, 0 < w i ∧ ∀ j ∈ events, i ∉ bad j := by
  have hgap' := (biUnion_mass_le events bad w hw).trans_lt hgap
  obtain ⟨i, hi, hwi, hnot⟩ := exists_positive_outside sample (events.biUnion bad) w hw hgap'
  refine ⟨i, hi, hwi, ?_⟩
  intro j hj hij
  exact hnot (Finset.mem_biUnion.mpr ⟨j, hj, hij⟩)

/-- The normalized finite endpoint-selection form, with total weight one. -/
theorem exists_positive_avoiding_all_of_mass_one (sample : Finset ι)
    (events : Finset κ) (bad : κ → Finset ι) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (htotal : (∑ i ∈ sample, w i) = 1)
    (hbad : (∑ j ∈ events, ∑ i ∈ bad j, w i) < 1) :
    ∃ i ∈ sample, 0 < w i ∧ ∀ j ∈ events, i ∉ bad j := by
  apply exists_positive_avoiding_all sample events bad w hw
  rwa [htotal]

/--
A finite endpoint satisfying two nonnegative first-moment tests and one
second-moment test. The conclusion is derived from the moment budgets;
simultaneous feasibility is not an assumption. No mean-zero assumption is
needed for this second-moment bound about zero.
-/
theorem good_endpoint_of_moments (sample : Finset ι)
    (w energy paid tangent : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (htotal : (∑ i ∈ sample, w i) = 1)
    (henergy : ∀ i ∈ sample, 0 ≤ energy i)
    (hpaid : ∀ i ∈ sample, 0 ≤ paid i)
    {energyBudget paidBudget secondMoment energyLimit paidLimit tangentLimit : ℝ}
    (henergyLimit : 0 < energyLimit) (hpaidLimit : 0 < paidLimit)
    (htangentLimit : 0 < tangentLimit)
    (henergyBudget : (∑ i ∈ sample, w i * energy i) ≤ energyBudget)
    (hpaidBudget : (∑ i ∈ sample, w i * paid i) ≤ paidBudget)
    (hsecondMoment : (∑ i ∈ sample, w i * (tangent i) ^ 2) ≤ secondMoment)
    (hcost : energyBudget / energyLimit + paidBudget / paidLimit +
      secondMoment / tangentLimit ^ 2 < 1) :
    ∃ i ∈ sample, 0 < w i ∧ energy i < energyLimit ∧
      paid i < paidLimit ∧ |tangent i| < tangentLimit := by
  classical
  let badEnergy := sample.filter (fun i => energyLimit ≤ energy i)
  let badPaid := sample.filter (fun i => paidLimit ≤ paid i)
  let badTangent := sample.filter (fun i => tangentLimit ≤ |tangent i|)
  have he : (∑ i ∈ badEnergy, w i) ≤ energyBudget / energyLimit :=
    weighted_markov_of_moment_le sample badEnergy (Finset.filter_subset _ _)
      w energy hw henergy henergyLimit
      (fun i hi => (Finset.mem_filter.mp hi).2) henergyBudget
  have hp : (∑ i ∈ badPaid, w i) ≤ paidBudget / paidLimit :=
    weighted_markov_of_moment_le sample badPaid (Finset.filter_subset _ _)
      w paid hw hpaid hpaidLimit
      (fun i hi => (Finset.mem_filter.mp hi).2) hpaidBudget
  have hm : (∑ i ∈ badTangent, w i) ≤ secondMoment / tangentLimit ^ 2 :=
    weighted_chebyshev_of_moment_le sample badTangent (Finset.filter_subset _ _)
      w tangent hw htangentLimit
      (fun i hi => (Finset.mem_filter.mp hi).2) hsecondMoment
  have hunion : (∑ i ∈ (badEnergy ∪ badPaid) ∪ badTangent, w i) ≤
      energyBudget / energyLimit + paidBudget / paidLimit +
        secondMoment / tangentLimit ^ 2 := by
    calc
      _ ≤ (∑ i ∈ badEnergy ∪ badPaid, w i) + ∑ i ∈ badTangent, w i :=
        union_mass_le _ _ w hw
      _ ≤ ((∑ i ∈ badEnergy, w i) + ∑ i ∈ badPaid, w i) +
          ∑ i ∈ badTangent, w i :=
        add_le_add_right (union_mass_le _ _ w hw) _
      _ ≤ _ := add_le_add (add_le_add he hp) hm
  have hgap : (∑ i ∈ (badEnergy ∪ badPaid) ∪ badTangent, w i) <
      ∑ i ∈ sample, w i := by
    rw [htotal]
    exact hunion.trans_lt hcost
  obtain ⟨i, hi, hwi, hnot⟩ :=
    exists_positive_outside sample ((badEnergy ∪ badPaid) ∪ badTangent) w hw hgap
  refine ⟨i, hi, hwi, ?_, ?_, ?_⟩
  all_goals
    apply lt_of_not_ge
    intro h
    apply hnot
    simp [badEnergy, badPaid, badTangent, hi, h]

end FiniteSelection
end MatrixSpencer
