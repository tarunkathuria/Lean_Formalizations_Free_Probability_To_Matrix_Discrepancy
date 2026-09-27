import MatrixSpencer.MSManuscriptAdaptive
import MatrixSpencer.MSManuscriptProbability

/-!
# Actual acceptance and finite independent retries for numerical MS samplers

This adapter consumes any actual finite sampler and a Boolean acceptance
procedure. Its output is the first accepted sampled state, with explicit
failure if the finite retry budget is exhausted. Quality and good-event
probability hypotheses are kept visible for the numerical epoch to discharge.
-/

open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSManuscriptAcceptanceRetry

open MSManuscriptAdaptive
open MSManuscriptProbability.FiniteRetry
variable {α : Type*}

def acceptanceProbability (P : Sampler α) (accept : α → Bool) : ℝ :=
  P.expectation (fun x => if accept x then 1 else 0)

/-- Actual independent trials; no favorable draw is chosen analytically. -/
def output (P : Sampler α) (accept : α → Bool) (r : ℕ) : Sampler (Option α) where
  Draws := Draws P.Draws r
  fintypeDraws := inferInstance
  weight := weight P.weight r
  value := firstAccepted P.value (fun z => accept (P.value z)) r
  weight_nonneg := weight_nonneg P.weight P.weight_nonneg r
  weight_sum := weight_sum P.weight P.weight_sum r

theorem output_sound (P : Sampler α) (accept : α → Bool) (property : α → Prop)
    (hsound : ∀ z : P.Draws, accept (P.value z) = true → property (P.value z))
    (r : ℕ) (z : (output P accept r).Draws) (a : α)
    (ho : (output P accept r).value z = some a) : property a :=
  firstAccepted_sound P.value (fun z => accept (P.value z)) property hsound r z a ho

/-- Transfer a proved good-event probability through a concrete acceptance
procedure that includes every good draw. -/
theorem acceptance_probability_ge (P : Sampler α) (accept : α → Bool)
    (good : α → Prop) [DecidablePred good] {p : ℝ}
    (hgood : p ≤ P.expectation (fun a => if good a then 1 else 0))
    (hincluded : ∀ z : P.Draws, good (P.value z) → accept (P.value z) = true) :
    p ≤ acceptanceProbability P accept := by
  apply hgood.trans
  unfold Sampler.expectation acceptanceProbability Sampler.expectation
  apply Finset.sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_left _ (P.weight_nonneg z)
  by_cases hg : good (P.value z)
  · simp only [if_pos hg, hincluded z hg, ↓reduceIte, le_refl]
  · simp only [if_neg hg]
    cases accept (P.value z) <;> norm_num

/-- General success probability; no particular epoch success constant is
hard-coded into the retry construction. -/
theorem output_probability_ge (P : Sampler α) (accept : α → Bool) {p : ℝ}
    (htrial : p ≤ acceptanceProbability P accept) (r : ℕ) :
    1 - (1 - p) ^ r ≤ (output P accept r).expectation success := by
  have ht := single_success_add_failure P.weight P.weight_sum (fun z => accept (P.value z))
  have hf : singleFailure P.weight (fun z => accept (P.value z)) ≤ 1 - p := by
    change p ≤ singleSuccess P.weight (fun z => accept (P.value z)) at htrial
    linarith
  have hp := pow_le_pow_left₀ (singleFailure_nonneg P.weight P.weight_nonneg
    (fun z => accept (P.value z))) hf r
  have htotal := MSManuscriptProbability.FiniteRetry.success_add_failure P.weight P.weight_sum
    P.value (fun z => accept (P.value z)) r
  rw [failureProbability_eq_pow] at htotal
  change 1 - (1 - p) ^ r ≤ MSManuscriptProbability.FiniteRetry.successProbability
    P.weight P.value (fun z => accept (P.value z)) r
  linarith

theorem output_event_probability_ge (P : Sampler α) (accept : α → Bool) {p : ℝ}
    (htrial : p ≤ acceptanceProbability P accept) (r : ℕ) :
    1 - (1 - p) ^ r ≤ ∑ z : (output P accept r).Draws, (output P accept r).weight z *
      (if ((output P accept r).value z).isSome then 1 else 0) :=
  output_probability_ge P accept htrial r

/-- The literal failure event has the complementary geometric bound. -/
theorem output_failure_le (P : Sampler α) (accept : α → Bool) {p : ℝ}
    (htrial : p ≤ acceptanceProbability P accept) (r : ℕ) :
    (output P accept r).expectation failure ≤ (1 - p) ^ r := by
  have hs := output_probability_ge P accept htrial r
  have ht := MSManuscriptAdaptive.success_add_failure (output P accept r)
  linarith

end MatrixSpencer.MSManuscriptAcceptanceRetry
