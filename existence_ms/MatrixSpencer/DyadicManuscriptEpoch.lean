import MatrixSpencer.DyadicActualEpoch
import MatrixSpencer.MSManuscriptScore



open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer.DyadicManuscriptEpoch
open FiniteBranchingTermination MSManuscriptProbability

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance manuscriptEpochCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance manuscriptEpochSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- Analytic preparation at the designated start, not a selected terminal leaf. -/
def initial (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) : ValidDyadicEpochState cfg :=
  ⟨Classical.choose (inputs.exists_initial), (Classical.choose_spec (inputs.exists_initial)).1⟩

/-- The actual finite transition tree, including all failed and successful leaves. -/
def tree (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) := Classical.choice (exists_finite_dyadic_epoch_tree cfg inputs (initial cfg inputs))

abbrev Attempt (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) := (tree cfg inputs).Leaves

def leaf (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (l : Attempt cfg inputs) : DyadicEpochState ι := ((tree cfg inputs).leafState l).val

def weight (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) : Attempt cfg inputs → ℝ := (tree cfg inputs).leafWeight

theorem weight_nonneg (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (l : Attempt cfg inputs) : 0 ≤ weight cfg inputs l :=
  ((tree cfg inputs).leafWeight_pos l).le

theorem weight_sum (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) : (∑ l, weight cfg inputs l) = 1 := (tree cfg inputs).leafWeight_sum

def score (cfg : DyadicEpochConfig ι n) (_inputs : DyadicEpochAnalyticInputs cfg) (s : DyadicEpochState ι) : ℝ :=
  MSManuscriptScore.score (Fintype.card ι) (dyadicEpochCertificate cfg s) s.paid s.tangent

theorem leaf_invariant (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (l : Attempt cfg inputs) : (leaf cfg inputs l).Invariant cfg :=
  ((tree cfg inputs).leafState l).property

theorem leaf_terminal (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (l : Attempt cfg inputs) : (leaf cfg inputs l).Terminal cfg :=
  (tree cfg inputs).leaf_terminal l

private theorem count_pos (cfg : DyadicEpochConfig ι n) (_inputs : DyadicEpochAnalyticInputs cfg) : (0:ℝ) < Fintype.card ι := by
  exact_mod_cast (show 0 < Fintype.card ι by have := cfg.count_large; omega)

theorem score_nonneg (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (l : Attempt cfg inputs) : 0 ≤ score cfg inputs (leaf cfg inputs l) :=
  MSManuscriptScore.score_nonneg (count_pos cfg inputs)
    (dyadicEpochCertificate_nonneg cfg (leaf_invariant cfg inputs l)) (leaf_invariant cfg inputs l).paid_nonneg

/-- The quantitative score bound follows from both proved finite-tree accounts. -/
theorem score_moment_le (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) :
    (∑ l, weight cfg inputs l * score cfg inputs (leaf cfg inputs l)) ≤ 3/8 := by
  have hs := Classical.choose_spec (inputs.exists_initial)
  have he0 : dyadicEpochEnergyAccount cfg (initial cfg inputs).val ≤ 2*Real.sqrt (Fintype.card ι : ℝ) := by
    change dyadicEpochEnergyAccount cfg (Classical.choose (inputs.exists_initial)) ≤ _
    simpa only [dyadicEpochEnergyAccount, hs.2.2.1, hs.2.2.2.2.1, mul_zero, sub_zero] using hs.2.2.2.2.2
  have ht0 : dyadicEpochTangentAccount (initial cfg inputs).val = 0 := by
    change dyadicEpochTangentAccount (Classical.choose (inputs.exists_initial)) = 0
    simp [dyadicEpochTangentAccount, hs.2.2.1, hs.2.2.2.1]
  have he : (∑ l, weight cfg inputs l * dyadicEpochEnergySuper cfg (leaf cfg inputs l)) ≤
      2*Real.sqrt (Fintype.card ι : ℝ) := (finite_dyadic_epoch_energy_le cfg inputs (tree cfg inputs)).trans he0
  have ht : (∑ l, weight cfg inputs l * dyadicEpochTangentAdjusted (leaf cfg inputs l)) ≤ 0 := by
    have h := finite_dyadic_epoch_tangent_le cfg inputs (tree cfg inputs)
    rw [ht0] at h
    exact h
  have hc := dyadic_epoch_combined_moment_of_super cfg (leaf cfg inputs) (weight cfg inputs)
    (weight_nonneg cfg inputs) (weight_sum cfg inputs) (leaf_invariant cfg inputs) he
  obtain ⟨he', hp'⟩ := dyadic_epoch_separate_moments_of_combined cfg (leaf cfg inputs) (weight cfg inputs)
    (weight_nonneg cfg inputs) (leaf_invariant cfg inputs) hc
  exact MSManuscriptScore.score_moment_le (weight cfg inputs) (fun l => dyadicEpochCertificate cfg (leaf cfg inputs l))
    (fun l => (leaf cfg inputs l).paid) (fun l => (leaf cfg inputs l).tangent) (count_pos cfg inputs) he' hp'
    (dyadic_epoch_tangent_moment_of_adjusted cfg (leaf cfg inputs) (weight cfg inputs) (weight_nonneg cfg inputs)
      (weight_sum cfg inputs) (leaf_invariant cfg inputs) ht)

theorem good_of_score_lt_one (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (l : Attempt cfg inputs)
    (hscore : score cfg inputs (leaf cfg inputs l) < 1) : DyadicEpochGoodEndpoint cfg (leaf cfg inputs l) := by
  have hi := leaf_invariant cfg inputs l
  obtain ⟨he, hp, ht⟩ := MSManuscriptScore.score_lt_one (count_pos cfg inputs)
    (dyadicEpochCertificate_nonneg cfg hi) hi.paid_nonneg hscore
  exact ⟨hi, hi.successful_of_paid_lt (leaf_terminal cfg inputs l) hp, hp, he, ht,
    hi.selected_retained_growth_le he.le ht.le, hi.selected_reset_growth_le he.le ht.le⟩

/-- This is the remaining value/certificate report accuracy interface. -/
def ReportAccuracy (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (report : DyadicEpochState ι → ℝ) : Prop :=
  ∀ l : Attempt cfg inputs, |report (leaf cfg inputs l)-score cfg inputs (leaf cfg inputs l)| ≤ 1/20

def accepts (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (report : DyadicEpochState ι → ℝ) (l : Attempt cfg inputs) : Bool :=
  acceptReport (report (leaf cfg inputs l))

theorem accepted_good (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (report : DyadicEpochState ι → ℝ)
    (hreport : ReportAccuracy cfg inputs report) (l : Attempt cfg inputs) (ha : accepts cfg inputs report l = true) :
    DyadicEpochGoodEndpoint cfg (leaf cfg inputs l) :=
  good_of_score_lt_one cfg inputs l (acceptReport_sound (hreport l) ha)

theorem acceptance_probability_ge_half (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (report : DyadicEpochState ι → ℝ)
    (hreport : ReportAccuracy cfg inputs report) :
    (1:ℝ)/2 ≤ ∑ l, weight cfg inputs l * (if accepts cfg inputs report l then 1 else 0) :=
  report_acceptance_ge_half (weight cfg inputs) (fun l => score cfg inputs (leaf cfg inputs l))
    (fun l => report (leaf cfg inputs l)) (weight_nonneg cfg inputs) (weight_sum cfg inputs)
    (score_nonneg cfg inputs) (score_moment_le cfg inputs) hreport

abbrev Draws (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (r : ℕ) := FiniteRetry.Draws (Attempt cfg inputs) r

def output (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (report : DyadicEpochState ι → ℝ) (r : ℕ)
    (z : Draws cfg inputs r) : Option (DyadicEpochState ι) :=
  FiniteRetry.firstAccepted (leaf cfg inputs) (accepts cfg inputs report) r z

def drawWeight (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (r : ℕ) : Draws cfg inputs r → ℝ :=
  FiniteRetry.weight (weight cfg inputs) r

theorem drawWeight_nonneg (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (r : ℕ) (z : Draws cfg inputs r) :
    0 ≤ drawWeight cfg inputs r z := FiniteRetry.weight_nonneg _ (weight_nonneg cfg inputs) r z

theorem drawWeight_sum (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (r : ℕ) : (∑ z, drawWeight cfg inputs r z) = 1 :=
  FiniteRetry.weight_sum _ (weight_sum cfg inputs) r

theorem output_sound (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (report : DyadicEpochState ι → ℝ)
    (hreport : ReportAccuracy cfg inputs report) (r : ℕ) (z : Draws cfg inputs r) (s : DyadicEpochState ι)
    (ho : output cfg inputs report r z = some s) : DyadicEpochGoodEndpoint cfg s :=
  FiniteRetry.firstAccepted_sound _ _ _ (accepted_good cfg inputs report hreport) r z s ho

/-- Probability of the literal actual returned endpoint event, not selected-leaf existence. -/
theorem output_event_probability_ge (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (report : DyadicEpochState ι → ℝ)
    (hreport : ReportAccuracy cfg inputs report) (r : ℕ) :
    1-((1:ℝ)/2)^r ≤ ∑ z, drawWeight cfg inputs r z * (if (output cfg inputs report r z).isSome then 1 else 0) :=
  FiniteRetry.successProbability_ge_half _ (weight_nonneg cfg inputs) (weight_sum cfg inputs) _ _
    (acceptance_probability_ge_half cfg inputs report hreport) r

/-- An exact analytic certificate instantiation. This is not a numerical value algorithm. -/
theorem analytic_output_event_probability_ge (cfg : DyadicEpochConfig ι n) (inputs : DyadicEpochAnalyticInputs cfg) (r : ℕ) :
    1-((1:ℝ)/2)^r ≤ ∑ z, drawWeight cfg inputs r z * (if (output cfg inputs (score cfg inputs) r z).isSome then 1 else 0) :=
  output_event_probability_ge cfg inputs (score cfg inputs) (by intro l; simp) r

/-- The existing analytic preparation and support-mesh proofs instantiate the sampler.
Only the scalar response-budget condition remains here; this is not a numerical
preparation or operation-count theorem. -/
theorem instantiated_analytic_output_probability (cfg : DyadicEpochConfig ι n)
    (hbudget : DyadicEpochPreparation.HasResponseBudget cfg) (r : ℕ) :
    let inputs := dyadicEpochAnalyticInputs cfg hbudget
    1-((1:ℝ)/2)^r ≤ ∑ z, drawWeight cfg inputs r z *
      (if (output cfg inputs (score cfg inputs) r z).isSome then 1 else 0) :=
  analytic_output_event_probability_ge cfg (dyadicEpochAnalyticInputs cfg hbudget) r

end MatrixSpencer.DyadicManuscriptEpoch
