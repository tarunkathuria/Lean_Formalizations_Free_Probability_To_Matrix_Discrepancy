import MatrixSpencer.KSDebitWalkQuality
import MatrixSpencer.KSComplexNorm

/-!
# Numerical norm acceptance at the actual finite walk leaves

The acceptance predicate checks every original sign and the certified
finite Jacobi norm report. The true operator norm appears only in proofs.
The earlier finite-walk quality event is contained in this numerical
acceptance event with the explicit `7 K δ` and `9 K δ` allowances.

This composition retains the accurate potential report, direction, and
local drift obligations of the walk controller. It does not discharge
those remaining numerical-controller requirements.
-/

open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSDebitWalkAcceptance

open KSDebitWalkRun
variable {N d : ℕ} [Nonempty (Fin d)]

def signedMatrix (C : Controller N (Fin d)) (s : State C) : Matrix (Fin d) (Fin d) ℂ :=
  KSPotentialModels.center (fun i => KSRankOne.atom (C.vectors i)) s.coeff

theorem signedMatrix_isHermitian (C : Controller N (Fin d)) (s : State C) :
    (signedMatrix C s).IsHermitian :=
  KSPotentialModels.center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (C.vectors i)) s.coeff

/-- Both conjuncts are finite tests: all original scalar signs, followed
by the real Jacobi norm-report comparison. -/
def accepts (C : Controller N (Fin d)) (ν a : ℝ) (s : State C) : Bool :=
  (List.finRange N).all (fun i => decide (s.coeff i = 1) || decide (s.coeff i = -1)) &&
    KSComplexNorm.accepts (signedMatrix C s) ν a

theorem accepts_iff (C : Controller N (Fin d)) (ν a : ℝ) (s : State C) :
    accepts C ν a s = true ↔
      (∀ i, IsSign (s.coeff i)) ∧ KSComplexNorm.report (signedMatrix C s) ν ≤ a := by
  simp [accepts, List.all_eq_true, IsSign, KSComplexNorm.accepts]

theorem accepts_sound (C : Controller N (Fin d)) {ν a : ℝ} (hν : 0 < ν)
    (s : State C) (haccept : accepts C ν a s = true) :
    (∀ i, IsSign (s.coeff i)) ∧ ‖signedMatrix C s‖ ≤ a := by
  obtain ⟨hs, hr⟩ := (accepts_iff C ν a s).mp haccept
  exact ⟨hs, KSComplexNorm.accepted_norm_le _ (signedMatrix_isHermitian C s) hν hr⟩

def acceptanceProbability (C : Controller N (Fin d)) (T : ℕ) (s : State C)
    (ν a : ℝ) : ℝ :=
  (run C T s).expectation (fun z => if accepts C ν a z then 1 else 0)

/-- The finite leaf distribution is unchanged; only its acceptance test
is replaced by the actual computed upper norm report. -/
theorem successProbability_le_acceptanceProbability (C : Controller N (Fin d))
    (T : ℕ) (s : State C) {ν a b : ℝ} (hν : 0 < ν) (hallow : a + ν ≤ b) :
    KSDebitWalkQuality.successProbability C T s a ≤ acceptanceProbability C T s ν b := by
  classical
  unfold KSDebitWalkQuality.successProbability acceptanceProbability
    FiniteBranchingTermination.Tree.expectation
  apply Finset.sum_le_sum
  intro l _
  apply mul_le_mul_of_nonneg_left _ ((run C T s).leafWeight_pos l).le
  dsimp only
  by_cases hs : KSDebitWalkQuality.successful C a ((run C T s).leafState l)
  · have ha : accepts C ν b ((run C T s).leafState l) = true := by
      apply (accepts_iff C ν b _).mpr
      exact ⟨hs.1, KSComplexNorm.good_norm_accepted _ (signedMatrix_isHermitian C _)
        hν hs.2 hallow⟩
    simp only [if_pos hs, ha, ↓reduceIte, le_refl]
  · simp only [if_neg hs]
    split_ifs <;> norm_num

/-- A true-norm `7 K δ` success probability transfers to the `9 K δ`
numerical test, with a report tolerance of `2 K δ`. -/
theorem acceptanceProbability_ge (C : Controller N (Fin d)) (T : ℕ) (s : State C)
    {K p : ℝ} (hK : 0 < K)
    (hgood : p ≤ KSDebitWalkQuality.successProbability C T s (7 * K * C.δ)) :
    p ≤ acceptanceProbability C T s (2 * K * C.δ) (9 * K * C.δ) :=
  hgood.trans (successProbability_le_acceptanceProbability C T s
    (mul_pos (mul_pos (by norm_num) hK) C.δ_pos) (by nlinarith))

/-- This is success by the actual finite numerical acceptance test, with
the earlier local potential-drift obligation still stated explicitly. -/
theorem acceptanceProbability_from_zero_ge (C : Controller N (Fin d))
    (hparseval : (∑ i, KSRankOne.atom (C.vectors i)) = 1)
    (hηbudget : (N : ℝ) * C.η ≤ C.δ) {ε β : ℝ} (hεpos : 0 < ε)
    (hε : ∀ i, ‖KSRankOne.atom (C.vectors i)‖ ≤ ε)
    (hθ : C.θ = ksRegularizerScale ε (Fin d)) (hδ : C.δ = Real.sqrt ε)
    (hβ : 0 ≤ β) (hdrift : KSDebitWalkQuality.LocalPotentialDrift C β)
    (hdriftBudget : β * ((N : ℝ) * (2 * Real.log 2)) ≤ C.δ)
    (T : ℕ) (hT : 0 < T)
    (htime : ((N : ℝ) * (2 * Real.log 2)) / (C.stepSize ^ 2 * (T : ℝ)) ≤ 1 / 8) :
    (41 : ℝ) / 56 ≤ acceptanceProbability C T (initialState C)
      (2 * (16 * Real.sqrt 2 + 5) * C.δ) (9 * (16 * Real.sqrt 2 + 5) * C.δ) :=
  acceptanceProbability_ge C T (initialState C) (by positivity)
    (KSDebitWalkQuality.successProbability_from_zero_ge C hparseval hηbudget hεpos hε hθ hδ
      hβ hdrift hdriftBudget T hT htime)

end MatrixSpencer.KSDebitWalkAcceptance
