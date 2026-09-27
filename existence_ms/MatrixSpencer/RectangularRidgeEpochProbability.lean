import MatrixSpencer.RectangularRidgeStoppedSampler

/-!
# Local account inequalities imply the finite epoch success probability

The probability estimate is derived from the actual finite adaptive sampler.
Its inputs are local preparation and movement inequalities, pathwise clock and
rounding bounds, and scalar budgets. No good-event probability is an input.
The numerical ridge transition must still discharge those local inputs.
-/
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RectangularRidgeEpochProbability
open MSManuscriptAdaptive RectangularRidgeStoppedSampler
variable {α : Type*}
attribute [local instance] Classical.propDecidable

/-- Rounding is charged pathwise; paid covariance loss shares the energy account. -/
def energyAccount (energy paid clock rounding : α → ℝ) (price drift : ℝ) (s : α) : ℝ :=
  energy s + price * paid s - drift * clock s - 2 * rounding s

def tangentAccount (tangent clock : α → ℝ) (N : ℝ) (s : α) : ℝ :=
  tangent s ^ 2 - N * clock s

/-- Exact local preparation bookkeeping suffices for account monotonicity. -/
lemma preparation_energy_le (energy paid clock rounding : α → ℝ) (price drift : ℝ)
    (s t : α)
    (he : energy t + price * (paid t - paid s) ≤ energy s + 2 * (rounding t - rounding s))
    (ht : clock t = clock s) :
    energyAccount energy paid clock rounding price drift t ≤
      energyAccount energy paid clock rounding price drift s := by
  unfold energyAccount
  rw [ht]
  linarith

/-- Actual conditional squared-tangent control and an exact clock update give
its local account inequality. -/
lemma movement_tangent_le (P : Sampler α) (tangent clock : α → ℝ) (N Δ : ℝ) (s : α)
    (ht : ∀ z, clock (P.value z) = clock s + Δ)
    (hv : P.expectation (fun t => tangent t ^ 2) ≤ tangent s ^ 2 + N * Δ) :
    P.expectation (tangentAccount tangent clock N) ≤ tangentAccount tangent clock N s := by
  have hc : P.expectation (fun t => N * clock t) = N * (clock s + Δ) := by
    change (∑ z, P.weight z * (N * clock (P.value z))) = _
    simp_rw [ht]
    rw [← Finset.sum_mul, P.weight_sum, one_mul]
  change P.expectation (fun t => tangent t ^ 2 - N * clock t) ≤ _
  rw [Sampler.expectation_sub, hc]
  unfold tangentAccount
  linarith

variable (stop : α → Prop) [DecidablePred stop] (prepare : α → α) (move : α → Sampler α)

/-- Local energy inequalities telescope with the actual stopping and preparation tests. -/
theorem joint_moment_le (energy paid clock rounding : α → ℝ) (price drift τ ρ : ℝ)
    (hD : 0 ≤ drift)
    (hprepare : ∀ s, energyAccount energy paid clock rounding price drift (prepare s) ≤
      energyAccount energy paid clock rounding price drift s)
    (hmove : ∀ s, ¬stop s → (move s).expectation (energyAccount energy paid clock rounding price drift) ≤
      energyAccount energy paid clock rounding price drift s)
    (htime : ∀ s, clock s ≤ τ) (hround : ∀ s, rounding s ≤ ρ) (k : ℕ) (s : α) :
    (run stop prepare move k s).expectation (fun t => energy t + price * paid t) ≤
      energyAccount energy paid clock rounding price drift s + drift * τ + 2 * ρ := by
  let P := run stop prepare move k s
  have ha := run_account_le stop prepare move (energyAccount energy paid clock rounding price drift)
    hprepare hmove k s
  have hp (t : α) : energy t + price * paid t ≤
      energyAccount energy paid clock rounding price drift t + (drift * τ + 2 * ρ) := by
    have hc := mul_le_mul_of_nonneg_left (htime t) hD
    have hr := hround t
    unfold energyAccount
    linarith
  have he := P.expectation_mono hp
  have hh : P.expectation (fun t => energyAccount energy paid clock rounding price drift t +
      (drift * τ + 2 * ρ)) = P.expectation (energyAccount energy paid clock rounding price drift) +
        (drift * τ + 2 * ρ) := by
    simp only [Sampler.expectation, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      P.weight_sum, one_mul]
  rw [hh] at he
  change P.expectation (energyAccount energy paid clock rounding price drift) ≤ _ at ha
  linarith

/-- The saved tangent moment needs no independence between adaptive stages. -/
theorem tangent_moment_le (tangent clock : α → ℝ) (N τ : ℝ) (hN : 0 ≤ N)
    (hprepare : ∀ s, tangentAccount tangent clock N (prepare s) ≤ tangentAccount tangent clock N s)
    (hmove : ∀ s, ¬stop s → (move s).expectation (tangentAccount tangent clock N) ≤
      tangentAccount tangent clock N s)
    (htime : ∀ s, clock s ≤ τ) (k : ℕ) (s : α) :
    (run stop prepare move k s).expectation (fun t => tangent t ^ 2) ≤
      tangentAccount tangent clock N s + N * τ := by
  let P := run stop prepare move k s
  have ha := run_account_le stop prepare move (tangentAccount tangent clock N) hprepare hmove k s
  have hp : P.expectation (fun t => tangent t ^ 2 - N * τ) ≤
      P.expectation (tangentAccount tangent clock N) :=
    P.expectation_mono (fun t => sub_le_sub_left (mul_le_mul_of_nonneg_left (htime t) hN) _)
  rw [Sampler.expectation_sub, Sampler.expectation_const] at hp
  change P.expectation (tangentAccount tangent clock N) ≤ _ at ha
  linarith

/-- Literal probability of the three original epoch tests, derived from local
account facts. The accepted branches are not selected by the sampler. -/
theorem good_probability_ge (energy paid dust tangent clock rounding : α → ℝ)
    (N drift τ ρ : ℝ) (hN : 0 < N) (hD : 0 ≤ drift)
    (he : ∀ s, 0 ≤ energy s) (hp : ∀ s, 0 ≤ paid s) (hd : ∀ s, dust s ≤ N / 1024)
    (htime : ∀ s, clock s ≤ τ) (hround : ∀ s, rounding s ≤ ρ)
    (hprepareE : ∀ s, energyAccount energy paid clock rounding (2048 / Real.sqrt N) drift (prepare s) ≤
      energyAccount energy paid clock rounding (2048 / Real.sqrt N) drift s)
    (hmoveE : ∀ s, ¬stop s →
      (move s).expectation (energyAccount energy paid clock rounding (2048 / Real.sqrt N) drift) ≤
        energyAccount energy paid clock rounding (2048 / Real.sqrt N) drift s)
    (hprepareT : ∀ s, tangentAccount tangent clock N (prepare s) ≤ tangentAccount tangent clock N s)
    (hmoveT : ∀ s, ¬stop s → (move s).expectation (tangentAccount tangent clock N) ≤
      tangentAccount tangent clock N s)
    (k : ℕ) (s : α)
    (hbudgetE : energyAccount energy paid clock rounding (2048 / Real.sqrt N) drift s +
      drift * τ + 2 * ρ ≤ (151 / 50 : ℝ) * Real.sqrt N)
    (hbudgetT : tangentAccount tangent clock N s + N * τ ≤ N) :
    (31 / 50 : ℝ) ≤ ∑ z : (run stop prepare move k s).Draws,
      (run stop prepare move k s).weight z *
        (if MSManuscriptEpochProbability.Good N
          (energy ((run stop prepare move k s).value z))
          (paid ((run stop prepare move k s).value z))
          (dust ((run stop prepare move k s).value z))
          (tangent ((run stop prepare move k s).value z)) then 1 else 0) := by
  apply MSManuscriptEpochProbability.good_probability_ge _ energy paid dust tangent hN he hp hd
  · exact (joint_moment_le stop prepare move energy paid clock rounding (2048 / Real.sqrt N)
      drift τ ρ hD hprepareE hmoveE htime hround k s).trans hbudgetE
  · exact (tangent_moment_le stop prepare move tangent clock N τ hN.le
      hprepareT hmoveT htime k s).trans hbudgetT

end MatrixSpencer.RectangularRidgeEpochProbability
