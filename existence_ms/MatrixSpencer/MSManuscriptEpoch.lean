import MatrixSpencer.EpochTree
import MatrixSpencer.MSManuscriptScore



open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer.MSManuscriptEpoch
open FiniteBranchingTermination MSManuscriptProbability

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance manuscriptEpochCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance manuscriptEpochSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- Analytic preparation at the designated start, not a selected terminal leaf. -/
def initial (cfg : EpochConfig ι n) : ValidEpochState cfg :=
  ⟨Classical.choose (exists_initial_epoch cfg), (Classical.choose_spec (exists_initial_epoch cfg)).1⟩

/-- The actual finite transition tree, including all failed and successful leaves. -/
def tree (cfg : EpochConfig ι n) := Classical.choice (exists_finite_epoch_tree cfg (initial cfg))

abbrev Attempt (cfg : EpochConfig ι n) := (tree cfg).Leaves

def leaf (cfg : EpochConfig ι n) (l : Attempt cfg) : EpochState ι := ((tree cfg).leafState l).val

def weight (cfg : EpochConfig ι n) : Attempt cfg → ℝ := (tree cfg).leafWeight

theorem weight_nonneg (cfg : EpochConfig ι n) (l : Attempt cfg) : 0 ≤ weight cfg l :=
  ((tree cfg).leafWeight_pos l).le

theorem weight_sum (cfg : EpochConfig ι n) : (∑ l, weight cfg l) = 1 := (tree cfg).leafWeight_sum

def score (cfg : EpochConfig ι n) (s : EpochState ι) : ℝ :=
  MSManuscriptScore.score (Fintype.card ι) (epochCertificate cfg s) s.paid s.tangent

theorem leaf_invariant (cfg : EpochConfig ι n) (l : Attempt cfg) : (leaf cfg l).Invariant cfg :=
  ((tree cfg).leafState l).property

theorem leaf_terminal (cfg : EpochConfig ι n) (l : Attempt cfg) : (leaf cfg l).Terminal :=
  (tree cfg).leaf_terminal l

omit [DecidableEq ι] [Nonempty n] in
private theorem count_pos (cfg : EpochConfig ι n) : (0:ℝ) < Fintype.card ι := by
  exact_mod_cast (show 0 < Fintype.card ι by have := cfg.count_large; omega)

theorem score_nonneg (cfg : EpochConfig ι n) (l : Attempt cfg) : 0 ≤ score cfg (leaf cfg l) :=
  MSManuscriptScore.score_nonneg (count_pos cfg)
    (epochCertificate_nonneg cfg (leaf_invariant cfg l)) (leaf_invariant cfg l).paid_nonneg

/-- The quantitative score bound follows from both proved finite-tree accounts. -/
theorem score_moment_le (cfg : EpochConfig ι n) :
    (∑ l, weight cfg l * score cfg (leaf cfg l)) ≤ 3/8 := by
  have hs := Classical.choose_spec (exists_initial_epoch cfg)
  have he0 : epochEnergyAccount cfg (initial cfg).val ≤ 2*Real.sqrt (Fintype.card ι : ℝ) := by
    change epochEnergyAccount cfg (Classical.choose (exists_initial_epoch cfg)) ≤ _
    simpa only [epochEnergyAccount, hs.2.2.1, hs.2.2.2.2.1, mul_zero, sub_zero] using hs.2.2.2.2.2
  have ht0 : epochTangentAccount (initial cfg).val = 0 := by
    change epochTangentAccount (Classical.choose (exists_initial_epoch cfg)) = 0
    simp [epochTangentAccount, hs.2.2.1, hs.2.2.2.1]
  have he : (∑ l, weight cfg l * epochEnergySuper cfg (leaf cfg l)) ≤
      2*Real.sqrt (Fintype.card ι : ℝ) := (finite_epoch_energy_le cfg (tree cfg)).trans he0
  have ht : (∑ l, weight cfg l * epochTangentAdjusted (leaf cfg l)) ≤ 0 := by
    have h := finite_epoch_tangent_le cfg (tree cfg)
    rw [ht0] at h
    exact h
  have hc := epoch_combined_moment_of_super cfg (leaf cfg) (weight cfg)
    (weight_nonneg cfg) (weight_sum cfg) (leaf_invariant cfg) he
  obtain ⟨he', hp'⟩ := epoch_separate_moments_of_combined cfg (leaf cfg) (weight cfg)
    (weight_nonneg cfg) (leaf_invariant cfg) hc
  exact MSManuscriptScore.score_moment_le (weight cfg) (fun l => epochCertificate cfg (leaf cfg l))
    (fun l => (leaf cfg l).paid) (fun l => (leaf cfg l).tangent) (count_pos cfg) he' hp'
    (epoch_tangent_moment_of_adjusted cfg (leaf cfg) (weight cfg) (weight_nonneg cfg)
      (weight_sum cfg) (leaf_invariant cfg) ht)

theorem good_of_score_lt_one (cfg : EpochConfig ι n) (l : Attempt cfg)
    (hscore : score cfg (leaf cfg l) < 1) : EpochGoodEndpoint cfg (leaf cfg l) := by
  have hi := leaf_invariant cfg l
  obtain ⟨he, hp, ht⟩ := MSManuscriptScore.score_lt_one (count_pos cfg)
    (epochCertificate_nonneg cfg hi) hi.paid_nonneg hscore
  exact ⟨hi, hi.successful_of_paid_lt (leaf_terminal cfg l) hp, hp, he, ht,
    hi.selected_retained_growth_le he.le ht.le, hi.selected_reset_growth_le he.le ht.le⟩

/-- This is the remaining value/certificate report accuracy interface. -/
def ReportAccuracy (cfg : EpochConfig ι n) (report : EpochState ι → ℝ) : Prop :=
  ∀ l : Attempt cfg, |report (leaf cfg l)-score cfg (leaf cfg l)| ≤ 1/20

def accepts (cfg : EpochConfig ι n) (report : EpochState ι → ℝ) (l : Attempt cfg) : Bool :=
  acceptReport (report (leaf cfg l))

theorem accepted_good (cfg : EpochConfig ι n) (report : EpochState ι → ℝ)
    (hreport : ReportAccuracy cfg report) (l : Attempt cfg) (ha : accepts cfg report l = true) :
    EpochGoodEndpoint cfg (leaf cfg l) :=
  good_of_score_lt_one cfg l (acceptReport_sound (hreport l) ha)

theorem acceptance_probability_ge_half (cfg : EpochConfig ι n) (report : EpochState ι → ℝ)
    (hreport : ReportAccuracy cfg report) :
    (1:ℝ)/2 ≤ ∑ l, weight cfg l * (if accepts cfg report l then 1 else 0) :=
  report_acceptance_ge_half (weight cfg) (fun l => score cfg (leaf cfg l))
    (fun l => report (leaf cfg l)) (weight_nonneg cfg) (weight_sum cfg)
    (score_nonneg cfg) (score_moment_le cfg) hreport

abbrev Draws (cfg : EpochConfig ι n) (r : ℕ) := FiniteRetry.Draws (Attempt cfg) r

def output (cfg : EpochConfig ι n) (report : EpochState ι → ℝ) (r : ℕ)
    (z : Draws cfg r) : Option (EpochState ι) :=
  FiniteRetry.firstAccepted (leaf cfg) (accepts cfg report) r z

def drawWeight (cfg : EpochConfig ι n) (r : ℕ) : Draws cfg r → ℝ :=
  FiniteRetry.weight (weight cfg) r

theorem drawWeight_nonneg (cfg : EpochConfig ι n) (r : ℕ) (z : Draws cfg r) :
    0 ≤ drawWeight cfg r z := FiniteRetry.weight_nonneg _ (weight_nonneg cfg) r z

theorem drawWeight_sum (cfg : EpochConfig ι n) (r : ℕ) : (∑ z, drawWeight cfg r z) = 1 :=
  FiniteRetry.weight_sum _ (weight_sum cfg) r

theorem output_sound (cfg : EpochConfig ι n) (report : EpochState ι → ℝ)
    (hreport : ReportAccuracy cfg report) (r : ℕ) (z : Draws cfg r) (s : EpochState ι)
    (ho : output cfg report r z = some s) : EpochGoodEndpoint cfg s :=
  FiniteRetry.firstAccepted_sound _ _ _ (accepted_good cfg report hreport) r z s ho

/-- Probability of the literal actual returned endpoint event, not selected-leaf existence. -/
theorem output_event_probability_ge (cfg : EpochConfig ι n) (report : EpochState ι → ℝ)
    (hreport : ReportAccuracy cfg report) (r : ℕ) :
    1-((1:ℝ)/2)^r ≤ ∑ z, drawWeight cfg r z * (if (output cfg report r z).isSome then 1 else 0) :=
  FiniteRetry.successProbability_ge_half _ (weight_nonneg cfg) (weight_sum cfg) _ _
    (acceptance_probability_ge_half cfg report hreport) r

/-- An exact analytic certificate instantiation. This is not a numerical value algorithm. -/
theorem analytic_output_event_probability_ge (cfg : EpochConfig ι n) (r : ℕ) :
    1-((1:ℝ)/2)^r ≤ ∑ z, drawWeight cfg r z * (if (output cfg (score cfg) r z).isSome then 1 else 0) :=
  output_event_probability_ge cfg (score cfg) (by intro l; simp) r

end MatrixSpencer.MSManuscriptEpoch
