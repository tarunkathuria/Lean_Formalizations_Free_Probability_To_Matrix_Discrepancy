import MatrixSpencer.KSDebitEntropyRun
import MatrixSpencer.KSInitialBounds

/-!
# Discrepancy quality of the actual finite debit walk

The transition and preparation are those of `KSDebitWalkRun`. This module
telescopes a stated bound on the actual pre-preparation potential drift,
then uses the proved entropy movement bound and the actual debit norm
majorization. It also counts successful finite leaves: a successful leaf
must have a sign on every original label and satisfy the discrepancy bound.

The local potential drift remains an explicit numerical-controller
obligation. These conditional quality estimates do not assert that a
numerical direction or potential-report algorithm has been constructed.
-/

open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSDebitWalkQuality

open KSDebitWalkRun
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

def potential (C : Controller N n) (s : State C) : ℝ :=
  KSDebitPreparation.statePotential C.vectors C.δ C.η C.θ s.coeff

/-- This obligation refers to the genuine optimized potential at the two
actual weighted proposals, before the numerical retirement preparation. -/
def LocalPotentialDrift (C : Controller N n) (β : ℝ) : Prop :=
  ∀ s : State C, ¬terminal s →
    (KSDebitPreparation.statePotential C.vectors C.δ C.η C.θ
        (KSDebitMovement.proposal s.coeff (C.direction s) (-C.stepSize)) +
      KSDebitPreparation.statePotential C.vectors C.δ C.η C.θ
        (KSDebitMovement.proposal s.coeff (C.direction s) C.stepSize)) / 2 ≤
      potential C s + β * C.stepSize ^ 2

theorem step_potential_le (C : Controller N n) {β : ℝ}
    (hdrift : LocalPotentialDrift C β) (s : State C) (ht : ¬terminal s) :
    (potential C (step C s false) + potential C (step C s true)) / 2 ≤
      potential C s + β * C.stepSize ^ 2 := by
  have hp (b : Bool) : potential C (step C s b) ≤
      KSDebitPreparation.statePotential C.vectors C.δ C.η C.θ
        (KSDebitMovement.proposal s.coeff (C.direction s) (signedStep C b)) := by
    unfold potential
    rw [step_active_coeff C s ht b]
    exact KSDebitPreparation.prepare_nonincreasing C.η_nonneg C.report _ C.accuracy
      (KSDebitMovement.proposal_mem_cube s.coeff s.cube (C.direction s)
        (C.direction_norm s ht) C.δ_pos (signedStep_abs_le C b) s.margin)
  have hfalse := hp false
  have htrue := hp true
  simp only [signedStep, Bool.false_eq_true, ↓reduceIte] at hfalse htrue
  have hd := hdrift s ht
  linarith

theorem expected_potential_le_cost (C : Controller N n) {β : ℝ}
    (hdrift : LocalPotentialDrift C β) (T : ℕ) (s : State C) :
    (run C T s).expectation (potential C) ≤
      potential C s + β * C.stepSize ^ 2 * expectedMovements C T s := by
  have ht := KSFiniteCoinRun.progress_telescope terminal (step C)
    (fun a => -potential C a) (-β * C.stepSize ^ 2)
    (fun a ha => by have := step_potential_le C hdrift a ha; linarith) T s
  change -potential C s + (-β * C.stepSize ^ 2) * expectedMovements C T s ≤
    (run C T s).expectation (fun a => -potential C a) at ht
  rw [FiniteBranchingTermination.Tree.expectation_neg] at ht
  linarith

/-- Entropy, rather than squared-coordinate energy, supplies the cost bound;
there is no additional inverse-margin factor in the accumulated drift. -/
theorem expected_potential_le (C : Controller N n) {β : ℝ} (hβ : 0 ≤ β)
    (hdrift : LocalPotentialDrift C β) (T : ℕ) (s : State C) :
    (run C T s).expectation (potential C) ≤
      potential C s + β * ((N : ℝ) * (2 * Real.log 2)) := by
  have hb := mul_le_mul_of_nonneg_left
    (KSDebitEntropyRun.expectedMovements_le C T s)
    (mul_nonneg hβ (sq_nonneg C.stepSize))
  have heq : β * C.stepSize ^ 2 *
      (((N : ℝ) * (2 * Real.log 2)) / C.stepSize ^ 2) =
      β * ((N : ℝ) * (2 * Real.log 2)) := by field_simp [ne_of_gt C.step_pos]
  rw [heq] at hb
  exact (expected_potential_le_cost C hdrift T s).trans (add_le_add_left hb _)

/-- The ordinary operator norm of the original signed atom sum. -/
def discrepancy (C : Controller N n) (s : State C) : ℝ :=
  ‖KSPotentialModels.center (fun i => KSRankOne.atom (C.vectors i)) s.coeff‖

theorem discrepancy_nonneg (C : Controller N n) (s : State C) :
    0 ≤ discrepancy C s := norm_nonneg _

theorem discrepancy_le_potential_add (C : Controller N n)
    (hparseval : (∑ i, KSRankOne.atom (C.vectors i)) = 1)
    (hηbudget : (N : ℝ) * C.η ≤ C.δ) (s : State C) :
    discrepancy C s ≤ potential C s + 2 * C.δ :=
  KSDebitPreparation.norm_le_statePotential_add C.vectors hparseval C.δ_pos.le
    C.η_nonneg hηbudget C.θ_pos s.cube

/-- All cutoff leaves are included in this expectation, whether or not they
are full signings. Their cube and debit invariants justify majorization. -/
theorem expected_discrepancy_le (C : Controller N n)
    (hparseval : (∑ i, KSRankOne.atom (C.vectors i)) = 1)
    (hηbudget : (N : ℝ) * C.η ≤ C.δ) {β : ℝ} (hβ : 0 ≤ β)
    (hdrift : LocalPotentialDrift C β) (T : ℕ) (s : State C) :
    (run C T s).expectation (discrepancy C) ≤
      potential C s + 2 * C.δ + β * ((N : ℝ) * (2 * Real.log 2)) := by
  have hpoint : (run C T s).expectation (discrepancy C) ≤
      (run C T s).expectation (potential C) + 2 * C.δ := by
    unfold FiniteBranchingTermination.Tree.expectation
    calc
      _ ≤ ∑ l : (run C T s).Leaves, (run C T s).leafWeight l *
          (potential C ((run C T s).leafState l) + 2 * C.δ) :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left
          (discrepancy_le_potential_add C hparseval hηbudget _)
          ((run C T s).leafWeight_pos l).le
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
          (run C T s).leafWeight_sum, one_mul]
  have hpot := expected_potential_le C hβ hdrift T s
  linarith

theorem initial_potential_le_zero (C : Controller N n) :
    potential C (initialState C) ≤
      KSDebitPreparation.statePotential C.vectors C.δ C.η C.θ 0 :=
  KSDebitPreparation.prepare_nonincreasing C.η_nonneg C.report _ C.accuracy
    (ksCube_zero (by norm_num))

theorem zero_potential_bound (C : Controller N n)
    (hparseval : (∑ i, KSRankOne.atom (C.vectors i)) = 1)
    {ε : ℝ} (hεpos : 0 < ε)
    (hε : ∀ i, ‖KSRankOne.atom (C.vectors i)‖ ≤ ε)
    (hθ : C.θ = ksRegularizerScale ε n) :
    KSDebitPreparation.statePotential C.vectors C.δ C.η C.θ 0 ≤
      (16 * Real.sqrt 2 + 2) * Real.sqrt ε := by
  have hz : KSPotentialModels.center (fun i => KSRankOne.atom (C.vectors i)) 0 = 0 := by
    simp [KSPotentialModels.center]
  have ho : KSPotentialModels.naturalOwners 64 (0 : Fin N → ℝ) = fun _ => 64 := by
    funext i
    simp [KSPotentialModels.naturalOwners]
  unfold KSDebitPreparation.statePotential KSDebitPotential.potential
  rw [hz, KSDebitBudget.debit_zero, ho, hθ]
  have hc : KSDebitCenter.center (0 : Matrix n n ℂ) 0 = 0 := by
    simp [KSDebitCenter.center, signedLift, KSSpinSource.doubled]
  rw [hc]
  exact ks_spin_initial_bound C.vectors hparseval hεpos hε

theorem expected_discrepancy_from_zero_le (C : Controller N n)
    (hparseval : (∑ i, KSRankOne.atom (C.vectors i)) = 1)
    (hηbudget : (N : ℝ) * C.η ≤ C.δ) {ε β : ℝ} (hεpos : 0 < ε)
    (hε : ∀ i, ‖KSRankOne.atom (C.vectors i)‖ ≤ ε)
    (hθ : C.θ = ksRegularizerScale ε n) (hδ : C.δ = Real.sqrt ε)
    (hβ : 0 ≤ β) (hdrift : LocalPotentialDrift C β) (T : ℕ) :
    (run C T (initialState C)).expectation (discrepancy C) ≤
      (16 * Real.sqrt 2 + 4) * C.δ + β * ((N : ℝ) * (2 * Real.log 2)) := by
  have hi := (initial_potential_le_zero C).trans (zero_potential_bound C hparseval hεpos hε hθ)
  have he := expected_discrepancy_le C hparseval hηbudget hβ hdrift T (initialState C)
  rw [← hδ] at hi
  nlinarith

attribute [local instance] Classical.propDecidable

/-- The event uses every original label, in addition to the actual norm.
A cutoff leaf without a full signing cannot satisfy this predicate. -/
def successful (C : Controller N n) (a : ℝ) (s : State C) : Prop :=
  (∀ i, IsSign (s.coeff i)) ∧ discrepancy C s ≤ a

def successProbability (C : Controller N n) (T : ℕ) (s : State C) (a : ℝ) : ℝ :=
  (run C T s).expectation (fun z => if successful C a z then 1 else 0)

def badNormProbability (C : Controller N n) (T : ℕ) (s : State C) (a : ℝ) : ℝ :=
  (run C T s).expectation (fun z => if a < discrepancy C z then 1 else 0)

theorem successProbability_eq_leaf_sum (C : Controller N n) (T : ℕ) (s : State C) (a : ℝ) :
    successProbability C T s a =
      ∑ l : (run C T s).Leaves, (run C T s).leafWeight l *
        (if (∀ i, IsSign (((run C T s).leafState l).coeff i)) ∧
            ‖KSPotentialModels.center (fun i => KSRankOne.atom (C.vectors i))
              ((run C T s).leafState l).coeff‖ ≤ a then 1 else 0) := by
  unfold successProbability FiniteBranchingTermination.Tree.expectation successful discrepancy
  apply Finset.sum_congr rfl
  intro l _
  dsimp only
  split_ifs <;> rfl

theorem badNormProbability_le (C : Controller N n) (T : ℕ) (s : State C)
    {a : ℝ} (ha : 0 < a) :
    badNormProbability C T s a ≤ (run C T s).expectation (discrepancy C) / a := by
  apply (le_div_iff₀ ha).mpr
  unfold badNormProbability FiniteBranchingTermination.Tree.expectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro l _
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ ((run C T s).leafWeight_pos l).le
  dsimp only
  split_ifs with hl
  · simpa only [one_mul] using hl.le
  · simpa only [zero_mul] using discrepancy_nonneg C ((run C T s).leafState l)

/-- This is the finite union bound for the actual leaf occurrences and
their actual coin weights; no probability-space or stopping axiom is used. -/
theorem one_le_success_add_bad (C : Controller N n) (T : ℕ) (s : State C) (a : ℝ) :
    1 ≤ successProbability C T s a + cutoffProbability C T s +
      badNormProbability C T s a := by
  have hp (z : State C) : (1 : ℝ) ≤
      (if successful C a z then 1 else 0) +
      KSStoppedProgress.activeIndicator terminal z +
      (if a < discrepancy C z then 1 else 0) := by
    by_cases ht : terminal z
    · have hs := (terminal_iff_full_signing z).mp ht
      by_cases hn : discrepancy C z ≤ a
      · simp [successful, hs, hn, not_lt.mpr hn, KSStoppedProgress.activeIndicator, ht]
      · simp [successful, hs, hn, lt_of_not_ge hn, KSStoppedProgress.activeIndicator, ht]
    · have hs : ¬∀ i, IsSign (z.coeff i) := by
        intro hs
        exact ht ((terminal_iff_full_signing z).mpr hs)
      simp only [successful, hs, false_and, ↓reduceIte, zero_add,
        KSStoppedProgress.activeIndicator, ht]
      split_ifs <;> norm_num
  calc
    1 = ∑ l : (run C T s).Leaves, (run C T s).leafWeight l * 1 := by
      simp only [mul_one, (run C T s).leafWeight_sum]
    _ ≤ ∑ l : (run C T s).Leaves, (run C T s).leafWeight l *
        ((if successful C a ((run C T s).leafState l) then 1 else 0) +
          KSStoppedProgress.activeIndicator terminal ((run C T s).leafState l) +
          (if a < discrepancy C ((run C T s).leafState l) then 1 else 0)) :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hp _)
        ((run C T s).leafWeight_pos l).le
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, successProbability, badNormProbability,
        cutoffProbability, KSFiniteCoinRun.activeProbability, KSFiniteCoinRun.expectation,
        FiniteBranchingTermination.Tree.expectation, run]

/-- A trial succeeds with probability at least `41/56` when its timeout
probability is at most `1/8` and its true expected norm is at most `K δ`.
The successful output is a full signing with true norm at most `7 K δ`. -/
theorem successProbability_ge (C : Controller N n) (T : ℕ) (s : State C)
    {K : ℝ} (hK : 0 < K)
    (htime : cutoffProbability C T s ≤ 1 / 8)
    (hmean : (run C T s).expectation (discrepancy C) ≤ K * C.δ) :
    (41 : ℝ) / 56 ≤ successProbability C T s (7 * K * C.δ) := by
  have hden : 0 < 7 * K * C.δ := mul_pos (mul_pos (by norm_num) hK) C.δ_pos
  have hb := (badNormProbability_le C T s hden).trans
    (div_le_div_of_nonneg_right hmean hden.le)
  have hratio : K * C.δ / (7 * K * C.δ) = (1 : ℝ) / 7 := by
    field_simp [ne_of_gt hK, ne_of_gt C.δ_pos]
  rw [hratio] at hb
  have hu := one_le_success_add_bad C T s (7 * K * C.δ)
  linarith

/-- The timeout and mean-norm premises are discharged from the actual
entropy count, the actual debit bound, and the stated local drift budget. -/
theorem successProbability_ge_of_budgets (C : Controller N n)
    (hparseval : (∑ i, KSRankOne.atom (C.vectors i)) = 1)
    (hηbudget : (N : ℝ) * C.η ≤ C.δ) {β K : ℝ}
    (hβ : 0 ≤ β) (hK : 0 < K) (hdrift : LocalPotentialDrift C β)
    (T : ℕ) (hT : 0 < T) (s : State C)
    (htime : ((N : ℝ) * (2 * Real.log 2)) / (C.stepSize ^ 2 * (T : ℝ)) ≤ 1 / 8)
    (hbudget : potential C s + 2 * C.δ + β * ((N : ℝ) * (2 * Real.log 2)) ≤ K * C.δ) :
    (41 : ℝ) / 56 ≤ successProbability C T s (7 * K * C.δ) :=
  successProbability_ge C T s hK
    ((KSDebitEntropyRun.cutoffProbability_le C T hT s).trans htime)
    ((expected_discrepancy_le C hparseval hηbudget hβ hdrift T s).trans hbudget)

/-- With the initial variance estimate and a total potential-drift budget
of `δ`, this gives the concrete constant-trial success bound from zero.
The local drift hypothesis is still required for the actual controller. -/
theorem successProbability_from_zero_ge (C : Controller N n)
    (hparseval : (∑ i, KSRankOne.atom (C.vectors i)) = 1)
    (hηbudget : (N : ℝ) * C.η ≤ C.δ) {ε β : ℝ} (hεpos : 0 < ε)
    (hε : ∀ i, ‖KSRankOne.atom (C.vectors i)‖ ≤ ε)
    (hθ : C.θ = ksRegularizerScale ε n) (hδ : C.δ = Real.sqrt ε)
    (hβ : 0 ≤ β) (hdrift : LocalPotentialDrift C β)
    (hdriftBudget : β * ((N : ℝ) * (2 * Real.log 2)) ≤ C.δ)
    (T : ℕ) (hT : 0 < T)
    (htime : ((N : ℝ) * (2 * Real.log 2)) / (C.stepSize ^ 2 * (T : ℝ)) ≤ 1 / 8) :
    (41 : ℝ) / 56 ≤ successProbability C T (initialState C)
      (7 * (16 * Real.sqrt 2 + 5) * C.δ) := by
  apply successProbability_ge C T (initialState C) (by positivity)
  · exact (KSDebitEntropyRun.cutoffProbability_from_zero_le C T hT).trans htime
  · have he := expected_discrepancy_from_zero_le C hparseval hηbudget hεpos hε
      hθ hδ hβ hdrift T
    nlinarith

theorem exists_successful_leaf_of_probability_pos (C : Controller N n)
    (T : ℕ) (s : State C) (a : ℝ) (hpos : 0 < successProbability C T s a) :
    ∃ l : (run C T s).Leaves,
      (∀ i, IsSign (((run C T s).leafState l).coeff i)) ∧
        discrepancy C ((run C T s).leafState l) ≤ a := by
  by_contra hn
  have hall (l : (run C T s).Leaves) : ¬successful C a ((run C T s).leafState l) :=
    fun hl => hn ⟨l, hl⟩
  have hz : successProbability C T s a = 0 := by
    unfold successProbability FiniteBranchingTermination.Tree.expectation
    apply Finset.sum_eq_zero
    intro l _
    simp only [hall l, ↓reduceIte, mul_zero]
  linarith

end MatrixSpencer.KSDebitWalkQuality
